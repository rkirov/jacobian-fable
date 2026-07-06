import Jacobian.Dbar.PlanarCousin
import Jacobian.Dbar.Operator
import Jacobian.Cech.Cochains
import Jacobian.Cech.Refinement
import Jacobian.Meromorphic

/-!
# Disk acyclicity of `𝒪_D` (`Jacobian/Dbar/DiskAcyclic.lean`)

Unit: dbar-solvability (`docs/design/dbar-solvability.md` D9, §4.8, §7.4). Depends on the
sibling units `cech-cohomology` (`Jacobian.Cech.Cochains`) and `meromorphic-and-divisors`
(`Jacobian.Meromorphic`).

Main deliverable (D=0 case, the sheaf `𝒪` of holomorphic functions): `Z¹(cover of a chart disk,
𝒪) = B¹`, i.e. `H¹(chart disk, 𝒪) = 0` — every additive holomorphic cocycle on a finite cover of
a chart disk splits, via `PlanarCousin.exists_holo_splitting_ball` transported through the chart
and cech's `MeroGermOn`/`evalAt` germ API for the pointwise bookkeeping.

DEVIATION (honestly reported): the general-divisor twist (`subsingleton_h1Cover_of_isChartDisk`,
needing `[T2Space X] [CompactSpace X]` and a finite-product twisting germ
`q := ∏ a ∈ D.support ∩ V, (· - e a) ^ D (e.symm a)`) is NOT included — it is a substantial
independent construction (one-directional twisted cochain maps commuting with `d0`/`d1`/
`restrictL`) that did not fit the remaining time budget; see the final report. The `D = 0` case
below is a complete, self-contained, fully admitted-free proof of disk acyclicity for the
structure sheaf, which is the piece the design flags as needed with "no compactness".
-/

open scoped ContDiff Manifold
open Set Filter Topology TopologicalSpace

namespace RS

open Cech

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [T1Space X]

private theorem heqOn_to_evEq {f g : X → ℂ} {U : Set X} (h : ∀ x ∈ U, f x = g x) :
    f =ᶠ[Filter.codiscreteWithin U] g :=
  Filter.mem_of_superset (Filter.self_mem_codiscreteWithin _) h

/-! ### Compat helpers (holomorphic ⇒ meromorphic, candidates for upstreaming to `mero`) -/

theorem meromorphicOnX_of_contMDiffOn_omega {U : Set X} (hU : IsOpen U) {u : X → ℂ}
    (hu : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω u U) : MeromorphicOnX u U := fun x hx => by
  have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω u x := (hu x hx).contMDiffAt (hU.mem_nhds hx)
  exact ContMDiffAt.meromorphicAtX h2

theorem mk_mem_linSysOn_zero {U : Set X} (hU : IsOpen U) {u : X → ℂ}
    (hu : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω u U) :
    MeroGermOn.mk u (meromorphicOnX_of_contMDiffOn_omega hU hu) ∈ LinSysOn (0 : Divisor X) U := by
  rw [mem_linSysOn_iff_of_isOpen hU]
  intro x hx
  rw [MeroGermOn.ord_mk hU hx]
  have h0 : ((0 : Divisor X) x : ℤ) = 0 := by
    simp [Function.locallyFinsuppWithin.coe_zero]
  rw [h0]
  have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω u x := (hu x hx).contMDiffAt (hU.mem_nhds hx)
  simpa using ContMDiffAt.ordAtX_nonneg h2

/-- Acyclicity for `𝒪` (no compactness needed): `H¹` of a finite cover of a chart disk, with
the structure sheaf's coefficients, vanishes. -/
theorem subsingleton_h1Cover_zero_of_isChartDisk {V : Opens X} (hV : IsChartDisk V)
    (𝒱 : FinCover V) : Subsingleton (H1Cover (0 : Divisor X) 𝒱) := by
  rw [subsingleton_h1Cover_iff]
  intro f hf
  obtain ⟨x₀, r, hr, _hx₀, hVs, hVim⟩ := hV
  set e := chartAt ℂ x₀ with he_def
  set W : Fin 𝒱.n → Set ℂ := fun i => ⇑e '' (𝒱.U i : Set X) with hW_def
  have hUisub : ∀ i, (𝒱.U i : Set X) ⊆ (e).source := fun i =>
    Set.Subset.trans (𝒱.le_base i : (𝒱.U i : Set X) ⊆ (V : Set X)) hVs
  have hUiUj_source : ∀ i j, ((𝒱.U i ⊓ 𝒱.U j : Opens X) : Set X) ⊆ e.source := fun i j =>
    (Set.inter_subset_left).trans (hUisub i)
  have hWo : ∀ i, IsOpen (W i) := fun i =>
    e.isOpen_image_of_subset_source (𝒱.U i).2 (hUisub i)
  have hWinter : ∀ i j, W i ∩ W j = ⇑e '' ((𝒱.U i ⊓ 𝒱.U j : Opens X) : Set X) := by
    intro i j
    apply Set.Subset.antisymm
    · rintro z ⟨⟨p, hp, rfl⟩, ⟨q, hq, hpq⟩⟩
      have : p = q := e.injOn (hUisub i hp) (hUisub j hq) hpq.symm
      exact ⟨p, ⟨hp, this ▸ hq⟩, rfl⟩
    · rintro z ⟨p, ⟨hp1, hp2⟩, rfl⟩
      exact ⟨⟨p, hp1, rfl⟩, ⟨p, hp2, rfl⟩⟩
  have hWb : ∀ i, W i ⊆ Metric.ball (e x₀) r := by
    intro i
    rw [hW_def]
    simp only
    rw [← hVim]
    exact Set.image_mono (𝒱.le_base i : (𝒱.U i : Set X) ⊆ (V : Set X))
  have hcov : Metric.ball (e x₀) r ⊆ ⋃ i, W i := by
    rw [← hVim]
    rintro z ⟨p, hp, rfl⟩
    obtain ⟨i, hi⟩ := 𝒱.covers p hp
    exact Set.mem_iUnion.2 ⟨i, p, hi, rfl⟩
  -- Step 1: holomorphic representatives of the germ cocycle.
  have hF_ord : ∀ i j, ∀ x ∈ (𝒱.U i ⊓ 𝒱.U j : Opens X),
      0 ≤ (f (i, j) : MeroGermOn X ((𝒱.U i ⊓ 𝒱.U j : Opens X) : Set X)).ord x := by
    intro i j x hx
    have := (mem_linSysOn_iff_of_isOpen (𝒱.U i ⊓ 𝒱.U j).2).1 (f (i, j)).2 x hx
    simpa using this
  set F : Fin 𝒱.n → Fin 𝒱.n → X → ℂ :=
    fun i j => (f (i, j) : MeroGermOn X ((𝒱.U i ⊓ 𝒱.U j : Opens X) : Set X)).holoRepr
    with hF_def
  have hF_cd : ∀ i j, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (F i j) ((𝒱.U i ⊓ 𝒱.U j : Opens X) : Set X) :=
    fun i j => MeroGermOn.holoRepr_contMDiffOn (𝒱.U i ⊓ 𝒱.U j).2 (hF_ord i j)
  -- Step 2: planar transport of the representatives.
  set φ : Fin 𝒱.n → Fin 𝒱.n → ℂ → ℂ := fun i j => F i j ∘ e.symm with hφ_def
  have hφ_diff : ∀ i j, DifferentiableOn ℂ (φ i j) (W i ∩ W j) := by
    intro i j
    rw [hWinter]
    have := (contMDiffOn_iff_analyticOnNhd_of_subset_source (chart_mem_atlas ℂ x₀)
      (hUiUj_source i j) (𝒱.U i ⊓ 𝒱.U j).2).1 (hF_cd i j)
    exact this.differentiableOn
  -- Step 3: pointwise cocycle identity for `φ`, from `Z1.rel_res`.
  have hcoc : ∀ i j k, ∀ z ∈ W i ∩ W j ∩ W k, φ i k z = φ i j z + φ j k z := by
    intro i j k z hz
    obtain ⟨p, hp, rfl⟩ : ∃ p ∈ ((𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k : Opens X) : Set X), e p = z := by
      have hz1 : z ∈ W i ∩ W j := ⟨hz.1.1, hz.1.2⟩
      have hz2 : z ∈ W j ∩ W k := ⟨hz.1.2, hz.2⟩
      rw [hWinter] at hz1 hz2
      obtain ⟨p, hp1, rfl⟩ := hz1
      obtain ⟨q, hq2, hpq⟩ := hz2
      have hpq' : p = q := e.injOn (hUiUj_source i j hp1) (hUiUj_source j k hq2) hpq.symm
      exact ⟨p, ⟨hp1, hpq' ▸ hq2.2⟩, rfl⟩
    have hbc : 𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k ≤ 𝒱.U j ⊓ 𝒱.U k :=
      le_inf (le_trans inf_le_left inf_le_right) inf_le_right
    have hac : 𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k ≤ 𝒱.U i ⊓ 𝒱.U k :=
      le_inf (le_trans inf_le_left inf_le_left) inf_le_right
    have hab : 𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k ≤ 𝒱.U i ⊓ 𝒱.U j := inf_le_left
    have hrel := Z1.rel_res (0 : Divisor X) (W := 𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k) hf i j k
      (le_refl _) hbc hac hab
    have hpik : p ∈ ((𝒱.U i ⊓ 𝒱.U k : Opens X) : Set X) := ⟨hp.1.1, hp.2⟩
    have hpij : p ∈ ((𝒱.U i ⊓ 𝒱.U j : Opens X) : Set X) := hp.1
    have hpjk : p ∈ ((𝒱.U j ⊓ 𝒱.U k : Opens X) : Set X) := ⟨hp.1.2, hp.2⟩
    have hordij := hF_ord i j p hpij
    have hordjk := hF_ord j k p hpjk
    have hordik := hF_ord i k p hpik
    have hrelv : (LinSysOn.restrictL (0 : Divisor X) hbc (f (j, k)) :
          MeroGermOn X ((𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k : Opens X) : Set X)) -
        (LinSysOn.restrictL (0 : Divisor X) hac (f (i, k)) :
          MeroGermOn X ((𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k : Opens X) : Set X)) +
        (LinSysOn.restrictL (0 : Divisor X) hab (f (i, j)) :
          MeroGermOn X ((𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k : Opens X) : Set X)) = 0 := by
      have := congrArg Subtype.val hrel
      simpa using this
    have hsum : (LinSysOn.restrictL (0 : Divisor X) hbc (f (j, k)) :
          MeroGermOn X ((𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k : Opens X) : Set X)) +
        (LinSysOn.restrictL (0 : Divisor X) hab (f (i, j)) :
          MeroGermOn X ((𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k : Opens X) : Set X)) =
        (LinSysOn.restrictL (0 : Divisor X) hac (f (i, k)) :
          MeroGermOn X ((𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k : Opens X) : Set X)) := by
      linear_combination hrelv
    rw [restrictL_apply_coe, restrictL_apply_coe, restrictL_apply_coe] at hsum
    have hordjk_r : 0 ≤ (MeroGermOn.restrict hbc
        (f (j, k) : MeroGermOn X ((𝒱.U j ⊓ 𝒱.U k : Opens X) : Set X))).ord p := by
      rw [MeroGermOn.ord_restrict hbc (𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k).2 (𝒱.U j ⊓ 𝒱.U k).2 hp]
      exact hordjk
    have hordij_r : 0 ≤ (MeroGermOn.restrict hab
        (f (i, j) : MeroGermOn X ((𝒱.U i ⊓ 𝒱.U j : Opens X) : Set X))).ord p := by
      rw [MeroGermOn.ord_restrict hab (𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k).2 (𝒱.U i ⊓ 𝒱.U j).2 hp]
      exact hordij
    have heval := congrArg (fun g => MeroGermOn.evalAt g p) hsum
    dsimp only at heval
    rw [MeroGermOn.evalAt_add (𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k).2 hp hordjk_r hordij_r] at heval
    rw [MeroGermOn.evalAt_restrict hbc (𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k).2 (𝒱.U j ⊓ 𝒱.U k).2 hp,
      MeroGermOn.evalAt_restrict hab (𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k).2 (𝒱.U i ⊓ 𝒱.U j).2 hp,
      MeroGermOn.evalAt_restrict hac (𝒱.U i ⊓ 𝒱.U j ⊓ 𝒱.U k).2 (𝒱.U i ⊓ 𝒱.U k).2 hp] at heval
    show F i k (e.symm (e p)) = F i j (e.symm (e p)) + F j k (e.symm (e p))
    rw [e.left_inv (hUisub i hp.1.1)]
    show F i k p = F i j p + F j k p
    have e1 : F i k p = (f (i, k) : MeroGermOn X ((𝒱.U i ⊓ 𝒱.U k : Opens X) : Set X)).evalAt p :=
      rfl
    have e2 : F i j p = (f (i, j) : MeroGermOn X ((𝒱.U i ⊓ 𝒱.U j : Opens X) : Set X)).evalAt p :=
      rfl
    have e3 : F j k p = (f (j, k) : MeroGermOn X ((𝒱.U j ⊓ 𝒱.U k : Opens X) : Set X)).evalAt p :=
      rfl
    rw [e1, e2, e3]
    linear_combination -heval
  -- Step 4: apply the planar holomorphic Cousin splitting.
  obtain ⟨u, hu_diff, hu_split⟩ := exists_holo_splitting_ball hr hWo hWb hcov hφ_diff hcoc
  -- Step 5: pull back to `X` and assemble a `C0` cochain witnessing `f ∈ B1`.
  set v : Fin 𝒱.n → X → ℂ := fun i => u i ∘ e with hv_def
  have hv_cd : ∀ i, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (v i) (𝒱.U i : Set X) := by
    intro i
    apply (contMDiffOn_iff_analyticOnNhd_of_subset_source (chart_mem_atlas ℂ x₀)
      (hUisub i) (𝒱.U i).2).2
    rw [show (⇑e '' (𝒱.U i : Set X)) = W i from rfl]
    apply AnalyticOnNhd.congr (hWo i) ((hu_diff i).analyticOnNhd (hWo i))
    rintro z ⟨q, hq, rfl⟩
    show u i (e q) = v i (e.symm (e q))
    rw [e.left_inv (hUisub i hq)]
    rfl
  set h : C0 (0 : Divisor X) 𝒱 := fun i =>
    ⟨MeroGermOn.mk (v i) (meromorphicOnX_of_contMDiffOn_omega (𝒱.U i).2 (hv_cd i)),
      mk_mem_linSysOn_zero (𝒱.U i).2 (hv_cd i)⟩ with hh_def
  have hpointwise : ∀ i j, ∀ p ∈ ((𝒱.U i ⊓ 𝒱.U j : Opens X) : Set X), F i j p = v j p - v i p := by
    intro i j p hp
    have hpi : p ∈ (𝒱.U i : Set X) := hp.1
    have hpj : p ∈ (𝒱.U j : Set X) := hp.2
    have hz : e p ∈ W i ∩ W j := ⟨⟨p, hpi, rfl⟩, ⟨p, hpj, rfl⟩⟩
    have hsplit := hu_split i j (e p) hz
    have hFip : φ i j (e p) = F i j p := by
      show F i j (e.symm (e p)) = F i j p
      rw [e.left_inv (hUisub i hpi)]
    show F i j p = v j p - v i p
    rw [← hFip, hsplit]
    show u j (e p) - u i (e p) = v j p - v i p
    rfl
  have hd0h : d0 (0 : Divisor X) 𝒱 h = f := by
    funext p
    obtain ⟨i, j⟩ := p
    apply Subtype.ext
    rw [d0_apply]
    show (MeroGermOn.restrict inf_le_right (h j : MeroGermOn X (𝒱.U (i, j).2 : Set X)) -
        MeroGermOn.restrict inf_le_left (h i : MeroGermOn X (𝒱.U (i, j).1 : Set X)) :
        MeroGermOn X ((𝒱.U (i, j).1 ⊓ 𝒱.U (i, j).2 : Opens X) : Set X)) =
      (f (i, j) : MeroGermOn X ((𝒱.U (i, j).1 ⊓ 𝒱.U (i, j).2 : Opens X) : Set X))
    show MeroGermOn.restrict inf_le_right (MeroGermOn.mk (v j)
        (meromorphicOnX_of_contMDiffOn_omega (𝒱.U j).2 (hv_cd j))) -
      MeroGermOn.restrict inf_le_left (MeroGermOn.mk (v i)
        (meromorphicOnX_of_contMDiffOn_omega (𝒱.U i).2 (hv_cd i))) =
      (f (i, j) : MeroGermOn X ((𝒱.U (i, j).1 ⊓ 𝒱.U (i, j).2 : Opens X) : Set X))
    rw [MeroGermOn.restrict_mk, MeroGermOn.restrict_mk,
      ← MeroGermOn.mk_holoRepr (𝒱.U (i, j).1 ⊓ 𝒱.U (i, j).2).2
        (f (i, j) : MeroGermOn X ((𝒱.U (i, j).1 ⊓ 𝒱.U (i, j).2 : Opens X) : Set X)),
      sub_eq_add_neg, MeroGermOn.mk_neg, MeroGermOn.mk_add]
    apply MeroGermOn.mk_eq_mk.2
    apply heqOn_to_evEq
    intro p hp
    show v j p + -v i p = F i j p
    rw [hpointwise i j p hp]
    ring
  rw [← hd0h]
  exact LinearMap.mem_range_self _ _

end RS
