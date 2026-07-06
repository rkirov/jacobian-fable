import Jacobian.Finiteness.CompactRestrict
import Jacobian.Cech.Cochains

/-!
# `ShrinkChain`: Forster's four-level shrinking chain (`finiteness-and-chi`)

Unit: finiteness-and-chi (`docs/design/finiteness-and-chi.md` D3, §4.2, proof plan §6.4).

`ShrinkChain X` packages Forster's `𝔚 ⋐ 𝔙 ⋐ 𝔘 ⋐ 𝔘*` same-index-set shrinking chain (D3): `U*`
chart disks (Leray-good), `U` the level whose closure sits inside `U*`, `V` the Montel-compact
middle level, `W` the coboundary level whose closure sits inside `V`. All four induced
`FinCover ⊤`s share the same index set, so every refinement map between them is `τ = id`
(`ref_star_U`/`ref_star_V`/`ref_star_W`/`ref_U_V`/`ref_V_W`/`ref_U_W`) — no `τ`-plumbing ever
enters the norm layer.

Existence (`ShrinkChain.nonempty`) iterates the cech `exists_chartDisk_closure_basis` pattern
four times per point (chart disk ⋐ level 1 ⋐ level 2 ⋐ level 3), then extracts a finite subcover
of the innermost level `W`, reindexed by `Finset.equivFin` exactly as `Cech.Covers`'s
`exists_good_refinement_closure` does.

Also provides the Banach cochain layer at one level `P ∈ {U, V, W}`: `NC0`/`NC1` (finite `Pi`s
of `BddHoloOn`), `deltaCLM` (the `0`-to-`1` coboundary, Cech's `d0` transposed to the norm
layer), `NZ1` (bounded cocycles, packaged as `ContinuousLinearMap.ker` of an internal `d1NC` —
closed and complete "for free", no hand-rolled pointwise-condition closedness proof needed),
and `resNC0`/`resNC1` (restriction CLMs between same-index levels).

**Deferred** (honest scope note): `resZ` (the restriction of `resNC1` to `NZ1`), `tradeSpace`/
`tradePi`/`tradeCompact` (Forster's 14.6(b) subspace `L` and its two projections), and the
cocycle-level compactness lemmas `isCompactOperator_resZ_UV`/`isCompactOperator_tradeCompact`
deferred here from `CompactRestrict.lean`'s docstring, are NOT included in this delivery. `resZ`
needs a naturality lemma (`d1NC T P' ∘ resNC1 T h = ⋯ ∘ d1NC T P`, a multi-term
restriction-composition identity in the exact texture of `Cech.Refinement`'s
`resC1_comp_d0` — ~40 lines of `restrictCLM`-composition bookkeeping) that a time-boxed attempt
did not finish honestly (no `sorry` was left in its place; the attempt was deleted and the
lemma is simply absent). A continuation builder should add `resNC1_mapsTo_NZ1` first (mirroring
`resC1_comp_d0`'s proof, replacing `LinSysOn.restrictL`/`restrictL_restrictL` with
`restrictCLM`/a new `restrictCLM_restrictCLM` presheaf-law lemma in `BddHolo.lean`), then `resZ`
via `ContinuousLinearMap.codRestrict`, then `tradeSpace := (tradeDefect).ker` (§5 step 1) and
`tradePi`/`tradeCompact` as its two projections (§4.2), then the two deferred compactness
lemmas via `IsCompactOperator.comp_clm`/`.clm_comp` composed with `isCompactOperator_restrictCLM`.
None of this changes any signature already exported here.
-/

open scoped ContDiff Manifold BoundedContinuousFunction
open Set Filter Topology TopologicalSpace Metric RS.Cech

namespace RS.Finiteness

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Forster's `𝔚 ⋐ 𝔙 ⋐ 𝔘 ⋐ 𝔘*` with `𝔘*` chart disks; same index set (D3). -/
structure ShrinkChain (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] where
  n : ℕ
  c : Fin n → X
  Ustar : Fin n → Opens X
  U : Fin n → Opens X
  V : Fin n → Opens X
  W : Fin n → Opens X
  isChartDisk_Ustar : ∀ i, IsChartDisk (Ustar i)
  Ustar_subset_source : ∀ i, (Ustar i : Set X) ⊆ (chartAt ℂ (c i)).source
  closure_U_subset : ∀ i, closure (U i : Set X) ⊆ (Ustar i : Set X)
  closure_V_subset : ∀ i, closure (V i : Set X) ⊆ (U i : Set X)
  closure_W_subset : ∀ i, closure (W i : Set X) ⊆ (V i : Set X)
  covers_W : ∀ x : X, ∃ i, x ∈ W i

namespace ShrinkChain

variable (T : ShrinkChain X)

theorem W_subset_V (i : Fin T.n) : (T.W i : Set X) ⊆ (T.V i : Set X) :=
  subset_closure.trans (T.closure_W_subset i)

theorem V_subset_U (i : Fin T.n) : (T.V i : Set X) ⊆ (T.U i : Set X) :=
  subset_closure.trans (T.closure_V_subset i)

theorem U_subset_Ustar (i : Fin T.n) : (T.U i : Set X) ⊆ (T.Ustar i : Set X) :=
  subset_closure.trans (T.closure_U_subset i)

theorem covers_V (x : X) : ∃ i, x ∈ T.V i := (T.covers_W x).imp (fun i hi => T.W_subset_V i hi)

theorem covers_U (x : X) : ∃ i, x ∈ T.U i :=
  (T.covers_W x).imp (fun i hi => T.V_subset_U i (T.W_subset_V i hi))

theorem covers_Ustar (x : X) : ∃ i, x ∈ T.Ustar i :=
  (T.covers_W x).imp (fun i hi => T.U_subset_Ustar i (T.V_subset_U i (T.W_subset_V i hi)))

/-- The four `FinCover ⊤`s induced by a `ShrinkChain`. -/
noncomputable def coverW : FinCover (⊤ : Opens X) where
  n := T.n
  U := T.W
  le_base _ := le_top
  covers x _ := T.covers_W x

noncomputable def coverV : FinCover (⊤ : Opens X) where
  n := T.n
  U := T.V
  le_base _ := le_top
  covers x _ := T.covers_V x

noncomputable def coverU : FinCover (⊤ : Opens X) where
  n := T.n
  U := T.U
  le_base _ := le_top
  covers x _ := T.covers_U x

noncomputable def coverStar : FinCover (⊤ : Opens X) where
  n := T.n
  U := T.Ustar
  le_base _ := le_top
  covers x _ := T.covers_Ustar x

theorem good_star : T.coverStar.IsGood := T.isChartDisk_Ustar

theorem ref_star_U : IsRefIdx T.coverStar T.coverU id := fun i => T.U_subset_Ustar i
theorem ref_star_V : IsRefIdx T.coverStar T.coverV id :=
  fun i => (T.V_subset_U i).trans (T.U_subset_Ustar i)
theorem ref_star_W : IsRefIdx T.coverStar T.coverW id :=
  fun i => ((T.W_subset_V i).trans (T.V_subset_U i)).trans (T.U_subset_Ustar i)
theorem ref_U_V : IsRefIdx T.coverU T.coverV id := fun i => T.V_subset_U i
theorem ref_V_W : IsRefIdx T.coverV T.coverW id := fun i => T.W_subset_V i
theorem ref_U_W : IsRefIdx T.coverU T.coverW id := fun i => (T.W_subset_V i).trans (T.V_subset_U i)

end ShrinkChain

/-- **Existence** of a `ShrinkChain` (§6.4): iterate the cech chart-disk-with-compact-closure
basis four times per point, then extract a finite subcover of the innermost level. -/
theorem ShrinkChain.nonempty [T2Space X] [CompactSpace X] : Nonempty (ShrinkChain X) := by
  choose Ustar hUstarGood hxUstar hUstarCompact using
    fun x : X => exists_chartDisk_closure_basis (x := x) (W := (Set.univ : Set X))
      Filter.univ_mem
  choose U hUgood hxU hUsubUstar hUcompact using
    fun x : X => exists_chartDisk_closure_basis (x := x) (W := (Ustar x : Set X))
      ((Ustar x).2.mem_nhds (hxUstar x))
  choose V hVgood hxV hVsubU hVcompact using
    fun x : X => exists_chartDisk_closure_basis (x := x) (W := (U x : Set X))
      ((U x).2.mem_nhds (hxU x))
  choose W hWgood hxW hWsubV hWcompact using
    fun x : X => exists_chartDisk_closure_basis (x := x) (W := (V x : Set X))
      ((V x).2.mem_nhds (hxV x))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => (W x : Set X)) (fun x => (W x).2) (by
      intro x _
      exact mem_iUnion.2 ⟨x, hxW x⟩)
  classical
  set eF := t.equivFin with heF_def
  set c' : Fin t.card → X := fun k => (eF.symm k : X) with hc'_def
  -- Extract the chart-disk witness point/radius for `Ustar` at each reindexed center.
  choose x' r' hr' hx' hsub' himg' using fun k : Fin t.card => hUstarGood (c' k)
  refine ⟨⟨t.card, x', fun k => Ustar (c' k), fun k => U (c' k), fun k => V (c' k),
    fun k => W (c' k), fun k => ⟨x' k, r' k, hr' k, hx' k, hsub' k, himg' k⟩, hsub', ?_, ?_, ?_, ?_⟩⟩
  · exact fun k => hUsubUstar (c' k)
  · exact fun k => hVsubU (c' k)
  · exact fun k => hWsubV (c' k)
  · intro x
    have hxmem : x ∈ ⋃ y ∈ t, (W y : Set X) := ht (mem_univ x)
    simp only [Set.mem_iUnion] at hxmem
    obtain ⟨y, hyt, hxy⟩ := hxmem
    exact ⟨eF ⟨y, hyt⟩, by simpa [hc'_def] using hxy⟩

/-! ### Banach cochain layer at a level `P ∈ {U, V, W}` -/

variable (T : ShrinkChain X) (P P' : Fin T.n → Opens X)

/-- `0`-cochains at level `P` (a finite `Pi` of `BddHoloOn`s). -/
abbrev NC0 : Type _ := ∀ i : Fin T.n, BddHoloOn (P i)

/-- `1`-cochains at level `P` (full product over ordered pairs, no `i < j` convention — matches
cech's D5 convention). -/
abbrev NC1 : Type _ := ∀ p : Fin T.n × Fin T.n, BddHoloOn (P p.1 ⊓ P p.2)

/-- `(δ⁰f)_{ij} = f_j − f_i` (after restriction to `P i ⊓ P j`); the Banach-layer analogue of
`Cech.d0`. -/
noncomputable def deltaCLM : NC0 T P →L[ℂ] NC1 T P :=
  ContinuousLinearMap.pi fun p : Fin T.n × Fin T.n =>
    (restrictCLM (inf_le_right : P p.1 ⊓ P p.2 ≤ P p.2)).comp (ContinuousLinearMap.proj p.2)
    - (restrictCLM (inf_le_left : P p.1 ⊓ P p.2 ≤ P p.1)).comp (ContinuousLinearMap.proj p.1)

@[simp] theorem deltaCLM_apply (f : NC0 T P) (p : Fin T.n × Fin T.n) :
    deltaCLM T P f p = restrictCLM inf_le_right (f p.2) - restrictCLM inf_le_left (f p.1) := rfl

/-- The `1`-to-`2`-cochain coboundary at level `P`, purely internal (used only to package `NZ1`
as a continuous-kernel submodule — no `NC2` is ever exported). -/
noncomputable def d1NC :
    NC1 T P →L[ℂ] ∀ t : Fin T.n × Fin T.n × Fin T.n, BddHoloOn (P t.1 ⊓ P t.2.1 ⊓ P t.2.2) :=
  ContinuousLinearMap.pi fun t : Fin T.n × Fin T.n × Fin T.n =>
    (restrictCLM (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        P t.1 ⊓ P t.2.1 ⊓ P t.2.2 ≤ P t.2.1 ⊓ P t.2.2)).comp
        (ContinuousLinearMap.proj (t.2.1, t.2.2))
    - (restrictCLM (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        P t.1 ⊓ P t.2.1 ⊓ P t.2.2 ≤ P t.1 ⊓ P t.2.2)).comp
        (ContinuousLinearMap.proj (t.1, t.2.2))
    + (restrictCLM (inf_le_left : P t.1 ⊓ P t.2.1 ⊓ P t.2.2 ≤ P t.1 ⊓ P t.2.1)).comp
        (ContinuousLinearMap.proj (t.1, t.2.1))

/-- **Bounded cocycles**: the kernel of `d1NC`, a *closed* submodule (`ContinuousLinearMap.ker`)
— Banach for free (`ContinuousLinearMap.completeSpace_ker`), no hand-rolled pointwise-condition
closedness proof needed. -/
@[simp] theorem d1NC_apply (f : NC1 T P) (t : Fin T.n × Fin T.n × Fin T.n) :
    d1NC T P f t =
      restrictCLM (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (f (t.2.1, t.2.2))
      - restrictCLM (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (f (t.1, t.2.2))
      + restrictCLM inf_le_left (f (t.1, t.2.1)) := rfl

noncomputable def NZ1 : Submodule ℂ (NC1 T P) := (d1NC T P).ker

set_option synthInstance.maxHeartbeats 800000 in
instance : CompleteSpace (NZ1 T P) := ContinuousLinearMap.completeSpace_ker (d1NC T P)

theorem mem_NZ1_iff (f : NC1 T P) : f ∈ NZ1 T P ↔ ∀ t, d1NC T P f t = 0 := by
  rw [NZ1, LinearMap.mem_ker]
  exact ⟨fun h t => congrFun h t, fun h => funext h⟩

/-- **The cocycle-relation workhorse** (mirrors `Cech.Refinement`'s `Z1.rel_res`): any
cocycle-relation triple, restricted to any smaller open `W` (via arbitrary — by proof
irrelevance, any — witnessing inequalities). -/
theorem NZ1.rel_res {f : NC1 T P} (hf : f ∈ NZ1 T P) (a b c : Fin T.n) {W : Opens X}
    (h : W ≤ P a ⊓ P b ⊓ P c) (hbc : W ≤ P b ⊓ P c) (hac : W ≤ P a ⊓ P c) (hab : W ≤ P a ⊓ P b) :
    restrictCLM hbc (f (b, c)) - restrictCLM hac (f (a, c)) + restrictCLM hab (f (a, b)) = 0 := by
  have hzero : d1NC T P f (a, b, c) = 0 := (mem_NZ1_iff T P f).1 hf (a, b, c)
  rw [d1NC_apply] at hzero
  have hcongr := congrArg (restrictCLM h) hzero
  simp only [map_add, map_sub, map_zero] at hcongr
  rw [restrictCLM_restrictCLM (le_inf (inf_le_left.trans inf_le_right) inf_le_right) h hbc,
    restrictCLM_restrictCLM (le_inf (inf_le_left.trans inf_le_left) inf_le_right) h hac,
    restrictCLM_restrictCLM inf_le_left h hab] at hcongr
  exact hcongr

/-- Restriction of `0`-cochains along a same-index shrinking `P' ≤ P`. -/
noncomputable def resNC0 (h : ∀ i, P' i ≤ P i) : NC0 T P →L[ℂ] NC0 T P' :=
  ContinuousLinearMap.pi fun i => (restrictCLM (h i)).comp (ContinuousLinearMap.proj i)

/-- Restriction of `1`-cochains along a same-index shrinking `P' ≤ P`. -/
noncomputable def resNC1 (h : ∀ i, P' i ≤ P i) : NC1 T P →L[ℂ] NC1 T P' :=
  ContinuousLinearMap.pi fun p : Fin T.n × Fin T.n =>
    (restrictCLM (inf_le_inf (h p.1) (h p.2))).comp (ContinuousLinearMap.proj p)

@[simp] theorem resNC1_apply (h : ∀ i, P' i ≤ P i) (f : NC1 T P) (p : Fin T.n × Fin T.n) :
    resNC1 T P P' h f p = restrictCLM (inf_le_inf (h p.1) (h p.2)) (f p) := rfl

/-- Restriction takes bounded cocycles to bounded cocycles (naturality of `d1NC`, via the
`NZ1.rel_res` workhorse — mirrors `Cech.Refinement`'s `resC1_mem_Z1`). -/
theorem resNC1_mapsTo_NZ1 (h : ∀ i, P' i ≤ P i) {f : NC1 T P} (hf : f ∈ NZ1 T P) :
    resNC1 T P P' h f ∈ NZ1 T P' := by
  rw [mem_NZ1_iff]
  rintro ⟨k, l, m⟩
  rw [d1NC_apply, resNC1_apply, resNC1_apply, resNC1_apply]
  have hkh : P' k ⊓ P' l ⊓ P' m ≤ P (k) := (inf_le_left.trans inf_le_left).trans (h k)
  have hlh : P' k ⊓ P' l ⊓ P' m ≤ P l := (inf_le_left.trans inf_le_right).trans (h l)
  have hmh : P' k ⊓ P' l ⊓ P' m ≤ P m := inf_le_right.trans (h m)
  have key := NZ1.rel_res T P hf k l m
    (le_inf (le_inf hkh hlh) hmh) (le_inf hlh hmh) (le_inf hkh hmh) (le_inf hkh hlh)
  rw [restrictCLM_restrictCLM (inf_le_inf (h l) (h m))
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (le_inf hlh hmh),
    restrictCLM_restrictCLM (inf_le_inf (h k) (h m))
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (le_inf hkh hmh),
    restrictCLM_restrictCLM (inf_le_inf (h k) (h l)) inf_le_left (le_inf hkh hlh)]
  exact key

/-- Restriction of bounded cocycles between same-index levels. -/
noncomputable def resZ (h : ∀ i, P' i ≤ P i) : NZ1 T P →L[ℂ] NZ1 T P' :=
  ((resNC1 T P P' h).comp (NZ1 T P).subtypeL).codRestrict (NZ1 T P')
    (fun f => resNC1_mapsTo_NZ1 T P P' h f.2)

end RS.Finiteness
