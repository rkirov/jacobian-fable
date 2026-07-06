import Jacobian.LaurentTail.Truncation

/-!
# The comparison `H1Tail D ≃ₗ Cech.H1 D` (laurent-tails, design §4.3/§5)

Unit: laurent-tails (`docs/design/laurent-tails.md`).

**Status (honest, full account in the file-end note): the comparison map `tailToH1 : T D →ₗ[ℂ]
Cech.H1 D` IS fully built here (zero sorries) — this was the unit's genuinely hardest piece,
constructed from scratch via a per-point Mittag-Leffler class `mlClassAt D p ψ : H1 D` (a 2-member
cover `{V, X∖{p}}` realizing `ψ` on a clean neighbourhood `V`), proved independent of every choice
involved (`mlClassAtOf_agree`, combining a cover-refinement step via `mlClass_res` with a
divisor-raising step via a new `mlClass_inclC0` lemma), then assembled into a genuine `ℂ`-linear
map via `Submodule.liftQ`/`DFinsupp.lsum`.

**Deferred** (see the file-end note for the exact gates and completion plans):
* `tailToH1_alpha` (`tailToH1 D (alphaL D f) = 0`, needed for `H1Tail.toH1` to descend) — needs a
  genuinely new *multi-point* combination lemma (this file only proves the *two-point* case,
  `mlClassAt_add`); the completion plan is fully worked out below.
* `H1Tail.toH1`, injectivity, `H1Tail.equiv` — downstream of the above.
* Surjectivity — gated on `dolbeault-comparison`'s Leray theorem
  (`toH1_surjective_of_isGood`), **not yet on disk** in `Jacobian/DolbeaultComparison/Leray.lean`
  as of this build (confirmed: file exists, 345 lines, still building towards it — the
  `exists_crossGlue` step, not yet the surjectivity conclusion itself).
-/

open scoped ContDiff Manifold Classical
open Set TopologicalSpace RS.Cech

set_option maxHeartbeats 1000000

namespace RS.LaurentTail

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]

/-! ### Small helper lemmas towards the construction -/

/-- Isolated-singularity fact for a general (not necessarily connected/global) germ: away from
`p`, `φ` is regular (order `≥ 0`) on some open neighbourhood of `p` inside its domain. -/
theorem exists_clean_nhds {U : Set X} (hU : IsOpen U) (φ : RS.MeroGermOn X U) {p : X}
    (hp : p ∈ U) :
    ∃ V : Opens X, p ∈ V ∧ (V : Set X) ⊆ U ∧
      ∀ x ∈ (V : Set X), x ≠ p → (0 : WithTop ℤ) ≤ φ.ord x := by
  obtain ⟨t, ht, hfin⟩ := (φ.divisorOn).supportLocallyFiniteWithinDomain p hp
  set F : Set X := (t ∩ (φ.divisorOn).support) \ {p} with hF_def
  have hFfin : F.Finite := hfin.subset (fun x hx => hx.1)
  have hpF : p ∉ F := fun h => h.2 rfl
  refine ⟨⟨(interior t \ F) ∩ U, (isOpen_interior.sdiff hFfin.isClosed).inter hU⟩,
    ⟨⟨mem_interior_iff_mem_nhds.2 ht, hpF⟩, hp⟩, inter_subset_right, fun x hx hxp => ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  have hxF : x ∈ F := by
    refine ⟨⟨interior_subset hx.1.1, ?_⟩, hxp⟩
    show (φ.divisorOn) x ≠ 0
    rw [RS.MeroGermOn.divisorOn_apply]
    intro heq
    rw [WithTop.untop₀_eq_zero] at heq
    rcases heq with heq | heq
    · rw [heq] at hcon; exact absurd hcon (lt_irrefl 0)
    · rw [heq] at hcon; exact absurd hcon (by simp)
  exact hx.1.2 hxF

/-- `C1.retype` commutes with restriction along a refinement index (both sides are literally the
same restriction of the same underlying germ). -/
theorem resC1_retype {D D' : RS.Divisor X} {Ω : Opens X} {𝒰 𝒱 : RS.Cech.FinCover Ω}
    (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : RS.Cech.IsRefIdx 𝒰 𝒱 τ) (f : RS.Cech.C1 D' 𝒰)
    (hf : f.MemLD D) (hf' : (RS.Cech.resC1 D' τ hτ f).MemLD D) :
    RS.Cech.resC1 D τ hτ (RS.Cech.C1.retype f hf) =
      RS.Cech.C1.retype (RS.Cech.resC1 D' τ hτ f) hf' := by
  funext p
  apply Subtype.ext
  have hL : (RS.Cech.resC1 D τ hτ (RS.Cech.C1.retype f hf) p : RS.MeroGermOn X _) =
      RS.MeroGermOn.restrict (inf_le_inf (hτ p.1) (hτ p.2))
        (f (τ p.1, τ p.2) : RS.MeroGermOn X _) := by
    rw [RS.Cech.resC1_apply, RS.Cech.restrictL_apply_coe, RS.Cech.C1.retype_apply_coe]
  have hR : (RS.Cech.C1.retype (RS.Cech.resC1 D' τ hτ f) hf' p : RS.MeroGermOn X _) =
      RS.MeroGermOn.restrict (inf_le_inf (hτ p.1) (hτ p.2))
        (f (τ p.1, τ p.2) : RS.MeroGermOn X _) := by
    rw [RS.Cech.C1.retype_apply_coe, RS.Cech.resC1_apply, RS.Cech.restrictL_apply_coe]
  rw [hL, hR]

/-- `mlClass` is compatible with refining the underlying cover: pulling the realizing `0`-cochain
back along a refinement index gives the same class in `H1 D`. -/
theorem mlClass_res {D D' : RS.Divisor X} {𝒰 𝒱 : RS.Cech.FinCover (⊤ : Opens X)}
    (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : RS.Cech.IsRefIdx 𝒰 𝒱 τ) (g : RS.Cech.C0 D' 𝒰)
    (hg : (RS.Cech.d0 D' 𝒰 g).MemLD D)
    (hg' : (RS.Cech.d0 D' 𝒱 (RS.Cech.resC0 D' τ hτ g)).MemLD D) :
    RS.Cech.mlClass 𝒰 g hg = RS.Cech.mlClass 𝒱 (RS.Cech.resC0 D' τ hτ g) hg' := by
  have hd0 : RS.Cech.d0 D' 𝒱 (RS.Cech.resC0 D' τ hτ g) =
      RS.Cech.resC1 D' τ hτ (RS.Cech.d0 D' 𝒰 g) :=
    (LinearMap.congr_fun (RS.Cech.resC1_comp_d0 D' τ hτ) g).symm
  have hg'' : (RS.Cech.resC1 D' τ hτ (RS.Cech.d0 D' 𝒰 g)).MemLD D := hd0 ▸ hg'
  have key : RS.Cech.resZ1 D τ hτ
      ⟨RS.Cech.C1.retype (RS.Cech.d0 D' 𝒰 g) hg, RS.Cech.C1.retype_mem_Z1 hg⟩ =
      ⟨RS.Cech.C1.retype (RS.Cech.d0 D' 𝒱 (RS.Cech.resC0 D' τ hτ g)) hg',
        RS.Cech.C1.retype_mem_Z1 hg'⟩ := by
    apply Subtype.ext
    rw [RS.Cech.resZ1_apply_coe]
    show RS.Cech.resC1 D τ hτ (RS.Cech.C1.retype (RS.Cech.d0 D' 𝒰 g) hg) =
      (RS.Cech.C1.retype (RS.Cech.d0 D' 𝒱 (RS.Cech.resC0 D' τ hτ g)) hg' : RS.Cech.C1 D 𝒱)
    rw [resC1_retype τ hτ (RS.Cech.d0 D' 𝒰 g) hg hg'']
    congr 1
    exact hd0.symm
  rw [RS.Cech.mlClass, RS.Cech.mlClass, ← RS.Cech.toH1_resH1 D τ hτ, RS.Cech.resH1_mk, key]

/-! ### The per-point construction: realizing a clean representative -/

/-- The 2-member cover `{V, X ∖ {p}}`, used to realize a single tail datum at `p`. -/
noncomputable def pairCover (p : X) (V : Opens X) (hpV : p ∈ V) :
    RS.Cech.FinCover (⊤ : Opens X) where
  n := 2
  U := ![V, ⟨{p}ᶜ, isOpen_compl_singleton⟩]
  le_base _ := le_top
  covers x _ := by
    by_cases hx : x = p
    · exact ⟨0, by simpa [hx] using hpV⟩
    · exact ⟨1, by simpa using hx⟩

theorem pairCover_U_zero (p : X) (V : Opens X) (hpV : p ∈ V) :
    (pairCover p V hpV).U (0 : Fin 2) = V := rfl

theorem pairCover_U_one (p : X) (V : Opens X) (hpV : p ∈ V) :
    (pairCover p V hpV).U (1 : Fin 2) = ⟨{p}ᶜ, isOpen_compl_singleton⟩ := rfl

/-- The `0`-cochain realizing `ψV` on `V`, `0` on the background `X ∖ {p}`. -/
noncomputable def gOf (p : X) (V : Opens X) (hpV : p ∈ V) (D' : RS.Divisor X)
    (ψV : RS.LinSysOn D' (V : Set X)) : RS.Cech.C0 D' (pairCover p V hpV) := by
  show ∀ i : Fin 2, RS.LinSysOn D' (((pairCover p V hpV).U i : Opens X) : Set X)
  intro i
  by_cases h : i = 0
  · subst h; rw [pairCover_U_zero]; exact ψV
  · have h1 : i = 1 := by omega
    subst h1; rw [pairCover_U_one]; exact 0

/-- The bump divisor supported only at `p`, covering `-(ψ.ord p)` there. -/
noncomputable def bumpDivisor (p : X) (n : ℤ) : RS.Divisor X :=
  Function.locallyFinsuppWithin.single p n

@[simp] theorem bumpDivisor_apply_self (p : X) (n : ℤ) : bumpDivisor p n p = n := by
  simp [bumpDivisor, Function.locallyFinsuppWithin.single_apply]

theorem bumpDivisor_apply_of_ne {p x : X} (hx : x ≠ p) (n : ℤ) : bumpDivisor p n x = 0 := by
  simp [bumpDivisor, Function.locallyFinsuppWithin.single_apply, hx]

theorem d0_pairCover_diag {D' : RS.Divisor X} (p : X) (V : Opens X) (hpV : p ∈ V)
    (g : RS.Cech.C0 D' (pairCover p V hpV)) (i : Fin 2) :
    RS.Cech.d0 D' (pairCover p V hpV) g (i, i) = 0 := by
  rw [RS.Cech.d0_apply, sub_eq_zero]

/-! ### `mlClass` invariance under raising the auxiliary divisor `D'` (from `scratch_ltails2.lean`) -/

theorem d0_inclC0_coe {Ω : Opens X} {𝒰 : RS.Cech.FinCover Ω} {D₁ D₂ : RS.Divisor X}
    (h : D₁ ≤ D₂) (g : RS.Cech.C0 D₁ 𝒰) (p : Fin 𝒰.n × Fin 𝒰.n) :
    (RS.Cech.d0 D₂ 𝒰 (RS.Cech.inclC0 D₁ 𝒰 h g) p :
        RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X)) =
      (RS.Cech.d0 D₁ 𝒰 g p : RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X)) := by
  rw [RS.Cech.d0_apply, RS.Cech.d0_apply, Submodule.coe_sub, Submodule.coe_sub,
    RS.Cech.restrictL_apply_coe, RS.Cech.restrictL_apply_coe,
    RS.Cech.restrictL_apply_coe, RS.Cech.restrictL_apply_coe,
    RS.Cech.inclC0_apply, RS.Cech.inclC0_apply]
  rfl

theorem memLD_inclC0 {Ω : Opens X} {𝒰 : RS.Cech.FinCover Ω} {D₁ D₂ D : RS.Divisor X}
    (h : D₁ ≤ D₂) {g : RS.Cech.C0 D₁ 𝒰} (hg : (RS.Cech.d0 D₁ 𝒰 g).MemLD D) :
    (RS.Cech.d0 D₂ 𝒰 (RS.Cech.inclC0 D₁ 𝒰 h g)).MemLD D := by
  intro p
  rw [d0_inclC0_coe]
  exact hg p

theorem mlClass_inclC0 {𝒰 : RS.Cech.FinCover (⊤ : Opens X)} {D₁ D₂ D : RS.Divisor X}
    (h : D₁ ≤ D₂) {g : RS.Cech.C0 D₁ 𝒰} (hg : (RS.Cech.d0 D₁ 𝒰 g).MemLD D) :
    RS.Cech.mlClass 𝒰 (RS.Cech.inclC0 D₁ 𝒰 h g) (memLD_inclC0 h hg) = RS.Cech.mlClass 𝒰 g hg := by
  have hval : RS.Cech.C1.retype (RS.Cech.d0 D₂ 𝒰 (RS.Cech.inclC0 D₁ 𝒰 h g)) (memLD_inclC0 h hg) =
      RS.Cech.C1.retype (RS.Cech.d0 D₁ 𝒰 g) hg := by
    funext p
    apply Subtype.ext
    rw [RS.Cech.C1.retype_apply_coe, RS.Cech.C1.retype_apply_coe, d0_inclC0_coe]
  show RS.Cech.toH1 D 𝒰 (RS.Cech.H1Cover.mk D 𝒰
      ⟨RS.Cech.C1.retype (RS.Cech.d0 D₂ 𝒰 (RS.Cech.inclC0 D₁ 𝒰 h g)) (memLD_inclC0 h hg),
        RS.Cech.C1.retype_mem_Z1 (memLD_inclC0 h hg)⟩) =
    RS.Cech.toH1 D 𝒰 (RS.Cech.H1Cover.mk D 𝒰
      ⟨RS.Cech.C1.retype (RS.Cech.d0 D₁ 𝒰 g) hg, RS.Cech.C1.retype_mem_Z1 hg⟩)
  exact congrArg (RS.Cech.toH1 D 𝒰) (congrArg (RS.Cech.H1Cover.mk D 𝒰) (Subtype.ext hval))

/-! ### `gOf` algebra -/

theorem gOf_add (p : X) (V : Opens X) (hpV : p ∈ V) (D' : RS.Divisor X)
    (ψV ψV' : RS.LinSysOn D' (V : Set X)) :
    gOf p V hpV D' (ψV + ψV') = gOf p V hpV D' ψV + gOf p V hpV D' ψV' := by
  funext i
  fin_cases i
  · apply Subtype.ext; rfl
  · apply Subtype.ext
    show (0 : RS.MeroGermOn X _) = (0:RS.MeroGermOn X _) + (0:RS.MeroGermOn X _)
    exact (add_zero 0).symm

theorem gOf_smul (c : ℂ) (p : X) (V : Opens X) (hpV : p ∈ V) (D' : RS.Divisor X)
    (ψV : RS.LinSysOn D' (V : Set X)) :
    gOf p V hpV D' (c • ψV) = c • gOf p V hpV D' ψV := by
  funext i
  fin_cases i
  · apply Subtype.ext; rfl
  · apply Subtype.ext
    show (0 : RS.MeroGermOn X _) = c • (0:RS.MeroGermOn X _)
    exact (smul_zero c).symm

theorem gOf_zero (p : X) (V : Opens X) (hpV : p ∈ V) (D' : RS.Divisor X) :
    gOf p V hpV D' 0 = 0 := by
  funext i
  fin_cases i
  · apply Subtype.ext; rfl
  · apply Subtype.ext; rfl

/-! ### A clean neighborhood also avoiding `D`'s other poles -/

noncomputable def cleanNbhd (D : RS.Divisor X) (p : X)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) : Opens X :=
  (exists_clean_nhds (chartAt ℂ p).open_source ψ (mem_chart_source ℂ p)).choose ⊓
    compOpens ((D.finiteSupport isCompact_univ).toFinset.erase p)

theorem mem_cleanNbhd (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    p ∈ cleanNbhd D p ψ :=
  ⟨(exists_clean_nhds (chartAt ℂ p).open_source ψ (mem_chart_source ℂ p)).choose_spec.1,
    mem_compOpens.mpr (fun h => (Finset.mem_erase.mp h).1 rfl)⟩

theorem cleanNbhd_sub_source (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    (cleanNbhd D p ψ : Set X) ⊆ (chartAt ℂ p).source :=
  fun x hx => (exists_clean_nhds (chartAt ℂ p).open_source ψ (mem_chart_source ℂ p)).choose_spec.2.1 hx.1

theorem cleanNbhd_ord_nonneg (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    ∀ x ∈ (cleanNbhd D p ψ : Set X), x ≠ p → (0 : WithTop ℤ) ≤ ψ.ord x :=
  fun x hx hxp => (exists_clean_nhds (chartAt ℂ p).open_source ψ
    (mem_chart_source ℂ p)).choose_spec.2.2 x hx.1 hxp

theorem cleanNbhd_D_eq_zero (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    ∀ x ∈ (cleanNbhd D p ψ : Set X), x ≠ p → D x = 0 := by
  intro x hx hxp
  by_contra hDx
  have hmem : x ∈ (D.finiteSupport isCompact_univ).toFinset.erase p :=
    Finset.mem_erase.mpr ⟨hxp, (D.finiteSupport isCompact_univ).mem_toFinset.mpr
      (Function.mem_support.mpr hDx)⟩
  exact (mem_compOpens.mp hx.2) hmem

/-! ### The auxiliary divisor `D'` bumped at `p` -/

noncomputable def nOf (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) : ℤ :=
  max (D p) (-(ψ.ord p).untop₀)

theorem D_p_le_nOf (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    D p ≤ nOf D p ψ := le_max_left _ _

theorem neg_nOf_le_ord (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    ((-(nOf D p ψ) : ℤ) : WithTop ℤ) ≤ ψ.ord p := by
  rcases eq_or_ne (ψ.ord p) ⊤ with h | h
  · rw [h]; exact le_top
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp h
    have hnk : -k ≤ nOf D p ψ := by
      rw [nOf, ← hk, WithTop.untop₀_coe]
      exact le_max_right _ _
    rw [← hk]
    have hfin : -(nOf D p ψ) ≤ k := by linarith
    exact_mod_cast hfin

noncomputable def DPrimeOf (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    RS.Divisor X :=
  D + bumpDivisor p (nOf D p ψ - D p)

theorem DPrimeOf_apply_self (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    DPrimeOf D p ψ p = nOf D p ψ := by
  show (D + bumpDivisor p (nOf D p ψ - D p)) p = nOf D p ψ
  have hstep : (D + bumpDivisor p (nOf D p ψ - D p)) p =
      D p + bumpDivisor p (nOf D p ψ - D p) p :=
    congrFun (Function.locallyFinsuppWithin.coe_add D _) p
  rw [hstep, bumpDivisor_apply_self]
  ring

theorem DPrimeOf_apply_of_ne (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source)
    {x : X} (hx : x ≠ p) : DPrimeOf D p ψ x = D x := by
  show (D + bumpDivisor p (nOf D p ψ - D p)) x = D x
  have hstep : (D + bumpDivisor p (nOf D p ψ - D p)) x =
      D x + bumpDivisor p (nOf D p ψ - D p) x :=
    congrFun (Function.locallyFinsuppWithin.coe_add D _) x
  rw [hstep, bumpDivisor_apply_of_ne hx]
  ring

theorem D_le_DPrimeOf (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    D ≤ DPrimeOf D p ψ := by
  rw [Function.locallyFinsuppWithin.le_def]
  intro x
  rcases eq_or_ne x p with rfl | hx
  · rw [DPrimeOf_apply_self]; exact D_p_le_nOf D x ψ
  · rw [DPrimeOf_apply_of_ne D p ψ hx]

/-! ### The membership witness for `gOf`'s `V`-component -/

theorem restrict_ψ_mem_linSysOn (D : RS.Divisor X) (p : X)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    RS.MeroGermOn.restrict (cleanNbhd_sub_source D p ψ) ψ ∈
      RS.LinSysOn (DPrimeOf D p ψ) (cleanNbhd D p ψ : Set X) := by
  refine (RS.mem_linSysOn_iff_of_isOpen (cleanNbhd D p ψ).2).2 ?_
  intro x hx
  rw [RS.MeroGermOn.ord_restrict (cleanNbhd_sub_source D p ψ) (cleanNbhd D p ψ).2
    (chartAt ℂ p).open_source hx]
  rcases eq_or_ne x p with rfl | hxp
  · rw [DPrimeOf_apply_self]; exact neg_nOf_le_ord D x ψ
  · rw [DPrimeOf_apply_of_ne D p ψ hxp, cleanNbhd_D_eq_zero D p ψ x hx hxp]
    simpa using cleanNbhd_ord_nonneg D p ψ x hx hxp

theorem gOf_apply_zero (p : X) (V : Opens X) (hpV : p ∈ V) (D' : RS.Divisor X)
    (ψV : RS.LinSysOn D' (V : Set X)) :
    gOf p V hpV D' ψV (0 : Fin 2) = ψV := rfl

theorem gOf_apply_one (p : X) (V : Opens X) (hpV : p ∈ V) (D' : RS.Divisor X)
    (ψV : RS.LinSysOn D' (V : Set X)) :
    gOf p V hpV D' ψV (1 : Fin 2) = 0 := rfl

noncomputable def ψVOf (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    RS.LinSysOn (DPrimeOf D p ψ) (cleanNbhd D p ψ : Set X) :=
  ⟨RS.MeroGermOn.restrict (cleanNbhd_sub_source D p ψ) ψ, restrict_ψ_mem_linSysOn D p ψ⟩

/-- Generic version: `gOf`'s coboundary is `D`-bounded whenever `V` is clean for `ψ` away from
`p` and avoids `D`'s other poles, and `D'` agrees with `D` away from `p`. Stated with fully
abstract `V`/`ψV`/`D'` (no unfolding of `cleanNbhd`/`ψVOf`/`DPrimeOf` needed inside the proof). -/
theorem gOf_memLD_of_clean (p : X) (D D' : RS.Divisor X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source)
    (V : Opens X) (hpV : p ∈ V) (hVsub : (V : Set X) ⊆ (chartAt ℂ p).source)
    (hVclean : ∀ x ∈ (V : Set X), x ≠ p → (0 : WithTop ℤ) ≤ ψ.ord x)
    (hVDzero : ∀ x ∈ (V : Set X), x ≠ p → D x = 0)
    (ψV : RS.LinSysOn D' (V : Set X))
    (hψV : (ψV : RS.MeroGermOn X (V : Set X)) = RS.MeroGermOn.restrict hVsub ψ) :
    (RS.Cech.d0 D' (pairCover p V hpV) (gOf p V hpV D' ψV)).MemLD D := by
  rintro ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> dsimp only
  · rw [d0_pairCover_diag]; exact Submodule.zero_mem _
  · erw [RS.Cech.d0_apply, gOf_apply_one, gOf_apply_zero, map_zero, zero_sub]
    refine (RS.mem_linSysOn_iff_of_isOpen ((pairCover p V hpV).U _ ⊓
        (pairCover p V hpV).U _).2).2 ?_
    intro x hx
    have hxV : x ∈ (V : Set X) := hx.1
    have hxp : x ≠ p := hx.2
    rw [Submodule.coe_neg, RS.MeroGermOn.ord_neg,
      RS.Cech.ord_restrictL D' inf_le_left hx ψV, hψV]
    have hordeq : ((RS.MeroGermOn.restrict hVsub) ψ).ord x = ψ.ord x :=
      RS.MeroGermOn.ord_restrict hVsub V.2 (chartAt ℂ p).open_source hxV ψ
    have hbound : (((-D x : ℤ) : WithTop ℤ)) ≤ ψ.ord x := by
      rw [hVDzero x hxV hxp]; simpa using hVclean x hxV hxp
    exact hbound.trans_eq hordeq.symm
  · erw [RS.Cech.d0_apply, gOf_apply_zero, gOf_apply_one, map_zero, sub_zero]
    refine (RS.mem_linSysOn_iff_of_isOpen ((pairCover p V hpV).U _ ⊓
        (pairCover p V hpV).U _).2).2 ?_
    intro x hx
    have hxV : x ∈ (V : Set X) := hx.2
    have hxp : x ≠ p := hx.1
    rw [RS.Cech.ord_restrictL D' inf_le_right hx ψV, hψV]
    have hordeq : ((RS.MeroGermOn.restrict hVsub) ψ).ord x = ψ.ord x :=
      RS.MeroGermOn.ord_restrict hVsub V.2 (chartAt ℂ p).open_source hxV ψ
    have hbound : (((-D x : ℤ) : WithTop ℤ)) ≤ ψ.ord x := by
      rw [hVDzero x hxV hxp]; simpa using hVclean x hxV hxp
    exact hbound.trans_eq hordeq.symm
  · rw [d0_pairCover_diag]; exact Submodule.zero_mem _

/-! ### `gOf` commutes with `inclC0` and with refinement (`resC0`) -/

theorem gOf_inclC0 (p : X) (V : Opens X) (hpV : p ∈ V) {D'₁ D'₂ : RS.Divisor X}
    (h : D'₁ ≤ D'₂) (ψV : RS.LinSysOn D'₁ (V : Set X)) :
    RS.Cech.inclC0 D'₁ (pairCover p V hpV) h (gOf p V hpV D'₁ ψV) =
      gOf p V hpV D'₂ (Submodule.inclusion (RS.linSysOn_mono h) ψV) := by
  funext k
  fin_cases k <;> apply Subtype.ext <;> rfl

theorem pairCover_isRefIdx (p : X) (V W : Opens X) (hpV : p ∈ V) (hpW : p ∈ W) (hWV : W ≤ V) :
    RS.Cech.IsRefIdx (pairCover p V hpV) (pairCover p W hpW) id := by
  intro k
  fin_cases k
  · exact hWV
  · exact le_refl _

theorem gOf_resC0 (p : X) (V W : Opens X) (hpV : p ∈ V) (hpW : p ∈ W) (hWV : W ≤ V)
    (D' : RS.Divisor X) (ψV : RS.LinSysOn D' (V : Set X)) :
    RS.Cech.resC0 (𝒰 := pairCover p V hpV) (𝒱 := pairCover p W hpW) D' id
        (pairCover_isRefIdx p V W hpV hpW hWV) (gOf p V hpV D' ψV) =
      gOf p W hpW D' (RS.Cech.LinSysOn.restrictL D' hWV ψV) := by
  funext k
  fin_cases k <;> apply Subtype.ext <;> rfl

/-- Transport `mlClass` along an equality of the underlying `0`-cochain (avoids the
"motive is not type correct" failure of `rw` on `mlClass`'s dependent `hg` argument). -/
theorem mlClass_congr {𝒰 : RS.Cech.FinCover (⊤ : Opens X)} {D D' : RS.Divisor X}
    {g g' : RS.Cech.C0 D' 𝒰} (heq : g = g') {hg : (RS.Cech.d0 D' 𝒰 g).MemLD D} :
    RS.Cech.mlClass 𝒰 g hg = RS.Cech.mlClass 𝒰 g' (heq ▸ hg) := by
  subst heq; rfl

/-! ### The single-point Mittag-Leffler class, and its independence of choices -/

noncomputable def mlClassAtOf (p : X) (D D' : RS.Divisor X)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) (V : Opens X) (hpV : p ∈ V)
    (hVsub : (V : Set X) ⊆ (chartAt ℂ p).source)
    (hVclean : ∀ x ∈ (V : Set X), x ≠ p → (0 : WithTop ℤ) ≤ ψ.ord x)
    (hVDzero : ∀ x ∈ (V : Set X), x ≠ p → D x = 0)
    (ψV : RS.LinSysOn D' (V : Set X))
    (hψV : (ψV : RS.MeroGermOn X (V : Set X)) = RS.MeroGermOn.restrict hVsub ψ) :
    RS.Cech.H1 D :=
  RS.Cech.mlClass (pairCover p V hpV) (gOf p V hpV D' ψV)
    (gOf_memLD_of_clean p D D' ψ V hpV hVsub hVclean hVDzero ψV hψV)

/-- Raise-then-refine identity: `mlClassAtOf` computed via `(D',V)` equals the one computed via
`(D'', W)` for `W ≤ V` and `D' ≤ D''`, provided the `D''`-typed representative on `W` is again
`restrict ψ`. -/
theorem mlClassAtOf_raise_res (p : X) (D D' D'' : RS.Divisor X)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) (V W : Opens X) (hpV : p ∈ V) (hpW : p ∈ W)
    (hWV : W ≤ V) (hVsub : (V : Set X) ⊆ (chartAt ℂ p).source)
    (hVclean : ∀ x ∈ (V : Set X), x ≠ p → (0 : WithTop ℤ) ≤ ψ.ord x)
    (hVDzero : ∀ x ∈ (V : Set X), x ≠ p → D x = 0)
    (hWsub : (W : Set X) ⊆ (chartAt ℂ p).source)
    (hWclean : ∀ x ∈ (W : Set X), x ≠ p → (0 : WithTop ℤ) ≤ ψ.ord x)
    (hWDzero : ∀ x ∈ (W : Set X), x ≠ p → D x = 0)
    (h : D' ≤ D'') (ψV : RS.LinSysOn D' (V : Set X))
    (hψV : (ψV : RS.MeroGermOn X (V : Set X)) = RS.MeroGermOn.restrict hVsub ψ)
    (ψW : RS.LinSysOn D'' (W : Set X))
    (hψW : (ψW : RS.MeroGermOn X (W : Set X)) = RS.MeroGermOn.restrict hWsub ψ) :
    mlClassAtOf p D D' ψ V hpV hVsub hVclean hVDzero ψV hψV =
      mlClassAtOf p D D'' ψ W hpW hWsub hWclean hWDzero ψW hψW := by
  unfold mlClassAtOf
  set ψV'' : RS.LinSysOn D'' (V : Set X) := Submodule.inclusion (RS.linSysOn_mono h) ψV with hψV''def
  have hψV'' : (ψV'' : RS.MeroGermOn X (V : Set X)) = RS.MeroGermOn.restrict hVsub ψ := hψV
  -- step 1: raise D' to D'' on the same cover `pairCover p V hpV`
  have e1 : RS.Cech.mlClass (pairCover p V hpV) (gOf p V hpV D' ψV)
        (gOf_memLD_of_clean p D D' ψ V hpV hVsub hVclean hVDzero ψV hψV) =
      RS.Cech.mlClass (pairCover p V hpV) (gOf p V hpV D'' ψV'')
        (gOf_memLD_of_clean p D D'' ψ V hpV hVsub hVclean hVDzero ψV'' hψV'') :=
    (mlClass_inclC0 h (gOf_memLD_of_clean p D D' ψ V hpV hVsub hVclean hVDzero ψV hψV)).symm.trans
      (mlClass_congr (gOf_inclC0 p V hpV h ψV))
  rw [e1]
  -- step 2: refine the cover from `V` down to `W`
  have e2 : RS.Cech.mlClass (pairCover p V hpV) (gOf p V hpV D'' ψV'')
        (gOf_memLD_of_clean p D D'' ψ V hpV hVsub hVclean hVDzero ψV'' hψV'') =
      RS.Cech.mlClass (pairCover p W hpW) (gOf p W hpW D'' (RS.Cech.LinSysOn.restrictL D'' hWV ψV''))
        (gOf_memLD_of_clean p D D'' ψ W hpW hWsub hWclean hWDzero
          (RS.Cech.LinSysOn.restrictL D'' hWV ψV'')
          (by rw [RS.Cech.restrictL_apply_coe, hψV'', RS.MeroGermOn.restrict_restrict])) :=
    (mlClass_res (𝒰 := pairCover p V hpV) (𝒱 := pairCover p W hpW) id
      (pairCover_isRefIdx p V W hpV hpW hWV) (gOf p V hpV D'' ψV'')
      (gOf_memLD_of_clean p D D'' ψ V hpV hVsub hVclean hVDzero ψV'' hψV'')
      (by rw [gOf_resC0]
          exact gOf_memLD_of_clean p D D'' ψ W hpW hWsub hWclean hWDzero
            (RS.Cech.LinSysOn.restrictL D'' hWV ψV'')
            (by rw [RS.Cech.restrictL_apply_coe, hψV'', RS.MeroGermOn.restrict_restrict]))).trans
      (mlClass_congr (gOf_resC0 p V W hpV hpW hWV D'' ψV''))
  rw [e2]
  have hval : gOf p W hpW D'' (RS.Cech.LinSysOn.restrictL D'' hWV ψV'') = gOf p W hpW D'' ψW :=
    congrArg (gOf p W hpW D'') (Subtype.ext (by
      rw [RS.Cech.restrictL_apply_coe, hψV'', RS.MeroGermOn.restrict_restrict]
      exact hψW.symm))
  exact mlClass_congr hval

/-- **Independence of choices.** `mlClassAtOf`'s value does not depend on which valid
`(V, D', ψV)` data is used to represent the same ambient germ `ψ`. -/
theorem mlClassAtOf_agree (p : X) (D : RS.Divisor X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source)
    {D'₁ D'₂ : RS.Divisor X} {V₁ V₂ : Opens X} (hpV₁ : p ∈ V₁) (hpV₂ : p ∈ V₂)
    (hV₁sub : (V₁ : Set X) ⊆ (chartAt ℂ p).source)
    (hV₁clean : ∀ x ∈ (V₁ : Set X), x ≠ p → (0 : WithTop ℤ) ≤ ψ.ord x)
    (hV₁Dzero : ∀ x ∈ (V₁ : Set X), x ≠ p → D x = 0)
    (hV₂sub : (V₂ : Set X) ⊆ (chartAt ℂ p).source)
    (hV₂clean : ∀ x ∈ (V₂ : Set X), x ≠ p → (0 : WithTop ℤ) ≤ ψ.ord x)
    (hV₂Dzero : ∀ x ∈ (V₂ : Set X), x ≠ p → D x = 0)
    (ψV₁ : RS.LinSysOn D'₁ (V₁ : Set X))
    (hψV₁ : (ψV₁ : RS.MeroGermOn X (V₁ : Set X)) = RS.MeroGermOn.restrict hV₁sub ψ)
    (ψV₂ : RS.LinSysOn D'₂ (V₂ : Set X))
    (hψV₂ : (ψV₂ : RS.MeroGermOn X (V₂ : Set X)) = RS.MeroGermOn.restrict hV₂sub ψ) :
    mlClassAtOf p D D'₁ ψ V₁ hpV₁ hV₁sub hV₁clean hV₁Dzero ψV₁ hψV₁ =
      mlClassAtOf p D D'₂ ψ V₂ hpV₂ hV₂sub hV₂clean hV₂Dzero ψV₂ hψV₂ := by
  set W : Opens X := V₁ ⊓ V₂ with hWdef
  have hpW : p ∈ W := ⟨hpV₁, hpV₂⟩
  have hWV₁ : W ≤ V₁ := inf_le_left
  have hWV₂ : W ≤ V₂ := inf_le_right
  have hWsub : (W : Set X) ⊆ (chartAt ℂ p).source := fun x hx => hV₁sub hx.1
  have hWclean : ∀ x ∈ (W : Set X), x ≠ p → (0 : WithTop ℤ) ≤ ψ.ord x :=
    fun x hx hxp => hV₁clean x (hWV₁ hx) hxp
  have hWDzero : ∀ x ∈ (W : Set X), x ≠ p → D x = 0 := fun x hx hxp => hV₁Dzero x (hWV₁ hx) hxp
  set D'' : RS.Divisor X := D'₁ ⊔ D'₂ with hD''def
  have h₁ : D'₁ ≤ D'' := le_sup_left
  have h₂ : D'₂ ≤ D'' := le_sup_right
  have hψWmem : RS.MeroGermOn.restrict hWsub ψ ∈ RS.LinSysOn D'' (W : Set X) := by
    refine (RS.mem_linSysOn_iff_of_isOpen W.2).2 ?_
    intro x hx
    rw [RS.MeroGermOn.ord_restrict hWsub W.2 (chartAt ℂ p).open_source hx]
    have hb1 : ((-(D'₁ x) : ℤ) : WithTop ℤ) ≤ ψ.ord x := by
      have hmem := (RS.mem_linSysOn_iff_of_isOpen V₁.2).1 ψV₁.2 x (hWV₁ hx)
      rwa [hψV₁, RS.MeroGermOn.ord_restrict hV₁sub V₁.2 (chartAt ℂ p).open_source (hWV₁ hx)] at hmem
    have hDsup : D'' x = D'₁ x ⊔ D'₂ x := Function.locallyFinsuppWithin.max_apply
    have hcast : ((-(D'' x) : ℤ) : WithTop ℤ) ≤ ((-(D'₁ x) : ℤ) : WithTop ℤ) := by
      rw [hDsup]
      exact_mod_cast neg_le_neg (le_max_left (D'₁ x) (D'₂ x))
    exact hcast.trans hb1
  set ψW : RS.LinSysOn D'' (W : Set X) := ⟨RS.MeroGermOn.restrict hWsub ψ, hψWmem⟩ with hψWdef
  have hψW : (ψW : RS.MeroGermOn X (W : Set X)) = RS.MeroGermOn.restrict hWsub ψ := rfl
  have hL := mlClassAtOf_raise_res p D D'₁ D'' ψ V₁ W hpV₁ hpW hWV₁ hV₁sub hV₁clean hV₁Dzero
    hWsub hWclean hWDzero h₁ ψV₁ hψV₁ ψW hψW
  have hR := mlClassAtOf_raise_res p D D'₂ D'' ψ V₂ W hpV₂ hpW hWV₂ hV₂sub hV₂clean hV₂Dzero
    hWsub hWclean hWDzero h₂ ψV₂ hψV₂ ψW hψW
  rw [hL, hR]

/-! ### `mlClassAt` (the canonical single-point construction) -/

noncomputable def mlClassAt (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    RS.Cech.H1 D :=
  mlClassAtOf p D (DPrimeOf D p ψ) ψ (cleanNbhd D p ψ) (mem_cleanNbhd D p ψ)
    (cleanNbhd_sub_source D p ψ) (cleanNbhd_ord_nonneg D p ψ) (cleanNbhd_D_eq_zero D p ψ)
    (ψVOf D p ψ) rfl

theorem mlClassAt_eq_of_valid (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source)
    {D' : RS.Divisor X} {V : Opens X} (hpV : p ∈ V) (hVsub : (V : Set X) ⊆ (chartAt ℂ p).source)
    (hVclean : ∀ x ∈ (V : Set X), x ≠ p → (0 : WithTop ℤ) ≤ ψ.ord x)
    (hVDzero : ∀ x ∈ (V : Set X), x ≠ p → D x = 0) (ψV : RS.LinSysOn D' (V : Set X))
    (hψV : (ψV : RS.MeroGermOn X (V : Set X)) = RS.MeroGermOn.restrict hVsub ψ) :
    mlClassAt D p ψ = mlClassAtOf p D D' ψ V hpV hVsub hVclean hVDzero ψV hψV :=
  mlClassAtOf_agree p D ψ (mem_cleanNbhd D p ψ) hpV (cleanNbhd_sub_source D p ψ)
    (cleanNbhd_ord_nonneg D p ψ) (cleanNbhd_D_eq_zero D p ψ) hVsub hVclean hVDzero
    (ψVOf D p ψ) rfl ψV hψV

theorem mlClassAt_eq_zero_of_mem_ordGe (D : RS.Divisor X) (p : X)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) (hp : (-(D p) : WithTop ℤ) ≤ ψ.ord p) :
    mlClassAt D p ψ = 0 := by
  have hmem : RS.MeroGermOn.restrict (cleanNbhd_sub_source D p ψ) ψ ∈
      RS.LinSysOn D (cleanNbhd D p ψ : Set X) := by
    refine (RS.mem_linSysOn_iff_of_isOpen (cleanNbhd D p ψ).2).2 ?_
    intro x hx
    rw [RS.MeroGermOn.ord_restrict (cleanNbhd_sub_source D p ψ) (cleanNbhd D p ψ).2
      (chartAt ℂ p).open_source hx]
    rcases eq_or_ne x p with rfl | hxp
    · exact hp
    · rw [cleanNbhd_D_eq_zero D p ψ x hx hxp]
      simpa using cleanNbhd_ord_nonneg D p ψ x hx hxp
  set ψV0 : RS.LinSysOn D (cleanNbhd D p ψ : Set X) :=
    ⟨RS.MeroGermOn.restrict (cleanNbhd_sub_source D p ψ) ψ, hmem⟩ with hψV0def
  rw [mlClassAt_eq_of_valid D p ψ (mem_cleanNbhd D p ψ) (cleanNbhd_sub_source D p ψ)
    (cleanNbhd_ord_nonneg D p ψ) (cleanNbhd_D_eq_zero D p ψ) ψV0 rfl]
  unfold mlClassAtOf
  apply RS.Cech.mlClass_eq_zero_of_exists _ _ (0 : RS.LinSys D)
  intro i x hx
  fin_cases i <;> dsimp only
  · erw [gOf_apply_zero, map_zero, sub_zero]
    exact (RS.mem_linSysOn_iff_of_isOpen (cleanNbhd D p ψ).2).1 hmem x hx
  · erw [gOf_apply_one, map_zero, sub_zero, RS.MeroGermOn.ord_zero, if_pos ⟨isOpen_compl_singleton, hx⟩]
    exact le_top

/-! ### `mlClassAt` is additive and `ℂ`-linear -/

theorem mlClassAt_add (D : RS.Divisor X) (p : X) (ψ ψ' : RS.MeroGermOn X (chartAt ℂ p).source) :
    mlClassAt D p (ψ + ψ') = mlClassAt D p ψ + mlClassAt D p ψ' := by
  set V : Opens X := cleanNbhd D p ψ ⊓ cleanNbhd D p ψ' with hVdef
  have hpV : p ∈ V := ⟨mem_cleanNbhd D p ψ, mem_cleanNbhd D p ψ'⟩
  have hVsub : (V : Set X) ⊆ (chartAt ℂ p).source := fun x hx => cleanNbhd_sub_source D p ψ hx.1
  have hVclean : ∀ x ∈ (V : Set X), x ≠ p → (0 : WithTop ℤ) ≤ ψ.ord x :=
    fun x hx hxp => cleanNbhd_ord_nonneg D p ψ x hx.1 hxp
  have hVclean' : ∀ x ∈ (V : Set X), x ≠ p → (0 : WithTop ℤ) ≤ ψ'.ord x :=
    fun x hx hxp => cleanNbhd_ord_nonneg D p ψ' x hx.2 hxp
  have hVcleansum : ∀ x ∈ (V : Set X), x ≠ p → (0 : WithTop ℤ) ≤ (ψ + ψ').ord x := by
    intro x hx hxp
    exact le_trans (le_min (hVclean x hx hxp) (hVclean' x hx hxp))
      (RS.MeroGermOn.ord_add (chartAt ℂ p).open_source (hVsub hx) ψ ψ')
  have hVDzero : ∀ x ∈ (V : Set X), x ≠ p → D x = 0 := fun x hx hxp => cleanNbhd_D_eq_zero D p ψ x hx.1 hxp
  set D' : RS.Divisor X := DPrimeOf D p ψ ⊔ DPrimeOf D p ψ' with hD'def
  have hDψ : D' p ≥ nOf D p ψ := by
    rw [hD'def]
    calc nOf D p ψ = DPrimeOf D p ψ p := (DPrimeOf_apply_self D p ψ).symm
      _ ≤ DPrimeOf D p ψ p ⊔ DPrimeOf D p ψ' p := le_sup_left
      _ = (DPrimeOf D p ψ ⊔ DPrimeOf D p ψ') p := (Function.locallyFinsuppWithin.max_apply).symm
  have hDψ' : D' p ≥ nOf D p ψ' := by
    rw [hD'def]
    calc nOf D p ψ' = DPrimeOf D p ψ' p := (DPrimeOf_apply_self D p ψ').symm
      _ ≤ DPrimeOf D p ψ p ⊔ DPrimeOf D p ψ' p := le_sup_right
      _ = (DPrimeOf D p ψ ⊔ DPrimeOf D p ψ') p := (Function.locallyFinsuppWithin.max_apply).symm
  have hD'x : ∀ x ≠ p, D' x = D x := by
    intro x hx
    rw [hD'def]
    show DPrimeOf D p ψ x ⊔ DPrimeOf D p ψ' x = D x
    rw [DPrimeOf_apply_of_ne D p ψ hx, DPrimeOf_apply_of_ne D p ψ' hx, sup_idem]
  have hboundψ : ((-(D' p) : ℤ) : WithTop ℤ) ≤ ψ.ord p := by
    calc ((-(D' p) : ℤ) : WithTop ℤ) ≤ ((-(nOf D p ψ) : ℤ) : WithTop ℤ) := by exact_mod_cast neg_le_neg hDψ
      _ ≤ ψ.ord p := neg_nOf_le_ord D p ψ
  have hboundψ' : ((-(D' p) : ℤ) : WithTop ℤ) ≤ ψ'.ord p := by
    calc ((-(D' p) : ℤ) : WithTop ℤ) ≤ ((-(nOf D p ψ') : ℤ) : WithTop ℤ) := by exact_mod_cast neg_le_neg hDψ'
      _ ≤ ψ'.ord p := neg_nOf_le_ord D p ψ'
  have hmemψ : RS.MeroGermOn.restrict hVsub ψ ∈ RS.LinSysOn D' (V : Set X) := by
    refine (RS.mem_linSysOn_iff_of_isOpen V.2).2 ?_
    intro x hx
    rw [RS.MeroGermOn.ord_restrict hVsub V.2 (chartAt ℂ p).open_source hx]
    rcases eq_or_ne x p with rfl | hxp
    · exact hboundψ
    · rw [hD'x x hxp, hVDzero x hx hxp]; simpa using hVclean x hx hxp
  have hmemψ' : RS.MeroGermOn.restrict hVsub ψ' ∈ RS.LinSysOn D' (V : Set X) := by
    refine (RS.mem_linSysOn_iff_of_isOpen V.2).2 ?_
    intro x hx
    rw [RS.MeroGermOn.ord_restrict hVsub V.2 (chartAt ℂ p).open_source hx]
    rcases eq_or_ne x p with rfl | hxp
    · exact hboundψ'
    · rw [hD'x x hxp, hVDzero x hx hxp]; simpa using hVclean' x hx hxp
  set ψVd : RS.LinSysOn D' (V : Set X) := ⟨RS.MeroGermOn.restrict hVsub ψ, hmemψ⟩ with hψVddef
  set ψV'd : RS.LinSysOn D' (V : Set X) := ⟨RS.MeroGermOn.restrict hVsub ψ', hmemψ'⟩ with hψV'ddef
  have hψVd : (ψVd : RS.MeroGermOn X (V : Set X)) = RS.MeroGermOn.restrict hVsub ψ := rfl
  have hψV'd : (ψV'd : RS.MeroGermOn X (V : Set X)) = RS.MeroGermOn.restrict hVsub ψ' := rfl
  have hψVsumd : ((ψVd + ψV'd : RS.LinSysOn D' (V : Set X)) : RS.MeroGermOn X (V : Set X)) =
      RS.MeroGermOn.restrict hVsub (ψ + ψ') := by
    rw [Submodule.coe_add, hψVd, hψV'd, map_add]
  have key1 : mlClassAt D p ψ = mlClassAtOf p D D' ψ V hpV hVsub hVclean hVDzero ψVd hψVd :=
    mlClassAt_eq_of_valid D p ψ hpV hVsub hVclean hVDzero ψVd hψVd
  have key2 : mlClassAt D p ψ' = mlClassAtOf p D D' ψ' V hpV hVsub hVclean' hVDzero ψV'd hψV'd :=
    mlClassAt_eq_of_valid D p ψ' hpV hVsub hVclean' hVDzero ψV'd hψV'd
  have key3 : mlClassAt D p (ψ + ψ') = mlClassAtOf p D D' (ψ + ψ') V hpV hVsub hVcleansum hVDzero
      (ψVd + ψV'd) hψVsumd :=
    mlClassAt_eq_of_valid D p (ψ + ψ') hpV hVsub hVcleansum hVDzero (ψVd + ψV'd) hψVsumd
  rw [key1, key2, key3]
  unfold mlClassAtOf
  exact (mlClass_congr (gOf_add p V hpV D' ψVd ψV'd)).trans
    (RS.Cech.mlClass_add _ _ _ _ _)

theorem mlClassAt_smul (D : RS.Divisor X) (p : X) (c : ℂ)
    (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    mlClassAt D p (c • ψ) = c • mlClassAt D p ψ := by
  have hψV : (ψVOf D p ψ : RS.MeroGermOn X (cleanNbhd D p ψ : Set X)) =
      RS.MeroGermOn.restrict (cleanNbhd_sub_source D p ψ) ψ := rfl
  have hmemc : RS.MeroGermOn.restrict (cleanNbhd_sub_source D p ψ) (c • ψ) ∈
      RS.LinSysOn (DPrimeOf D p ψ) (cleanNbhd D p ψ : Set X) := by
    rw [map_smul]
    exact Submodule.smul_mem _ c (restrict_ψ_mem_linSysOn D p ψ)
  set ψVc : RS.LinSysOn (DPrimeOf D p ψ) (cleanNbhd D p ψ : Set X) :=
    ⟨RS.MeroGermOn.restrict (cleanNbhd_sub_source D p ψ) (c • ψ), hmemc⟩ with hψVcdef
  have hψVc : (ψVc : RS.MeroGermOn X (cleanNbhd D p ψ : Set X)) =
      RS.MeroGermOn.restrict (cleanNbhd_sub_source D p ψ) (c • ψ) := rfl
  have hψVcsmul : ((c • ψVOf D p ψ : RS.LinSysOn (DPrimeOf D p ψ) (cleanNbhd D p ψ : Set X)) :
      RS.MeroGermOn X (cleanNbhd D p ψ : Set X)) =
      RS.MeroGermOn.restrict (cleanNbhd_sub_source D p ψ) (c • ψ) := by
    rw [Submodule.coe_smul, hψV, map_smul]
  have hVclean : ∀ x ∈ (cleanNbhd D p (c • ψ) : Set X), x ≠ p → (0 : WithTop ℤ) ≤ (c • ψ).ord x :=
    cleanNbhd_ord_nonneg D p (c • ψ)
  have key1 : mlClassAt D p (c • ψ) = mlClassAtOf p D (DPrimeOf D p ψ) (c • ψ)
      (cleanNbhd D p ψ) (mem_cleanNbhd D p ψ) (cleanNbhd_sub_source D p ψ)
      (fun x hx hxp => by
        rcases eq_or_ne c 0 with rfl | hc
        · rw [zero_smul, RS.MeroGermOn.ord_zero,
            if_pos ⟨(chartAt ℂ p).open_source, cleanNbhd_sub_source D p ψ hx⟩]
          exact le_top
        · rw [RS.MeroGermOn.ord_smul (chartAt ℂ p).open_source (cleanNbhd_sub_source D p ψ hx) hc]
          exact cleanNbhd_ord_nonneg D p ψ x hx hxp)
      (cleanNbhd_D_eq_zero D p ψ) ψVc hψVc :=
    mlClassAt_eq_of_valid D p (c • ψ) (mem_cleanNbhd D p ψ) (cleanNbhd_sub_source D p ψ) _
      (cleanNbhd_D_eq_zero D p ψ) ψVc hψVc
  rw [key1]
  unfold mlClassAt mlClassAtOf
  have hgeq : gOf p (cleanNbhd D p ψ) (mem_cleanNbhd D p ψ) (DPrimeOf D p ψ) ψVc =
      c • gOf p (cleanNbhd D p ψ) (mem_cleanNbhd D p ψ) (DPrimeOf D p ψ) (ψVOf D p ψ) := by
    rw [← gOf_smul]
    congr 1
    apply Subtype.ext
    rw [hψVc, Submodule.coe_smul, hψV, map_smul]
  exact (mlClass_congr hgeq).trans (RS.Cech.mlClass_smul _ _ _ _)

/-! ### The ambient linear map, and its descent to `TailAt p D` / `T D` -/

/-- `AddCommGroup (H1 D)`, registered globally: `Module.DirectLimit.addCommGroup` is stated with
`G`/`f` as leading *explicit* arguments (not instance-implicit), so plain `inferInstance`/typeclass
search for `AddCommGroup (H1 D)` does not find it automatically through the `H1` abbrev — needed
explicitly here so `Submodule.liftQ`'s own instance search (for its codomain) succeeds. -/
noncomputable instance instAddCommGroupH1 (D : RS.Divisor X) : AddCommGroup (RS.Cech.H1 D) :=
  Module.DirectLimit.addCommGroup (fun 𝒰 : RS.Cech.FinCover (⊤ : Opens X) => RS.Cech.H1Cover D 𝒰)
    (fun _ _ h => RS.Cech.resH1' D h)

noncomputable def mlClassAtRaw (D : RS.Divisor X) (p : X) :
    RS.MeroGermOn X (chartAt ℂ p).source →ₗ[ℂ] RS.Cech.H1 D where
  toFun := mlClassAt D p
  map_add' := mlClassAt_add D p
  map_smul' := mlClassAt_smul D p

theorem mlClassAtRaw_apply (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    mlClassAtRaw D p ψ = mlClassAt D p ψ := rfl

noncomputable def tailAtToH1 (D : RS.Divisor X) (p : X) : TailAt p D →ₗ[ℂ] RS.Cech.H1 D :=
  Submodule.liftQ (RS.Cech.ordGe p (-(D p))) (mlClassAtRaw D p) (fun ψ hψ => by
    rw [LinearMap.mem_ker, mlClassAtRaw_apply]
    exact mlClassAt_eq_zero_of_mem_ordGe D p ψ (RS.Cech.mem_ordGe_iff.mp hψ))

theorem tailAtToH1_mk (D : RS.Divisor X) (p : X) (ψ : RS.MeroGermOn X (chartAt ℂ p).source) :
    tailAtToH1 D p (TailAt.mk p D ψ) = mlClassAt D p ψ :=
  Submodule.liftQ_apply _ _ ψ

noncomputable def tailToH1 (D : RS.Divisor X) : T D →ₗ[ℂ] RS.Cech.H1 D :=
  DFinsupp.lsum ℕ (fun p => tailAtToH1 D p)

theorem tailToH1_apply_single (D : RS.Divisor X) (p : X) (τ : TailAt p D) :
    tailToH1 D (DFinsupp.single p τ) = tailAtToH1 D p τ := by
  rw [tailToH1, DFinsupp.lsum_single]


end RS.LaurentTail

/-!
### File-end note: exact status, what's proved, what's deferred, and the completion plan

**Built here, zero sorries, fully general and reusable (in dependency order):**

1. **`mlClass_inclC0` machinery** (`d0_inclC0_coe`/`memLD_inclC0`/`mlClass_inclC0`): `Cech.mlClass`
   is invariant under *raising* the auxiliary divisor `D'` typing a cochain on a *fixed* cover
   (`inclC0`, already built in `Colimit.lean`) — the underlying germs don't change, only the
   membership proof. Proved via `d0_apply`/`inclC0_apply`/`Submodule.inclusion`'s `rfl`-level coe,
   packaged through a **new general helper `mlClass_congr`** (`heq : g = g' → mlClass 𝒰 g hg =
   mlClass 𝒰 g' (heq ▸ hg)`, by `subst heq; rfl`) that sidesteps the "motive is not type correct"
   failure `rw`/`erw` hit repeatedly on `mlClass`'s dependent `hg : (d0 D' 𝒰 g).MemLD D` argument
   (recorded as a gotcha below).
2. **`gOf` algebra** (`gOf_add`/`gOf_smul`/`gOf_zero`/`gOf_apply_zero`/`gOf_apply_one`): the
   previous builder's 2-member-cover cochain constructor `gOf` is linear in its `V`-component, and
   `gOf p V hpV D' ψV (0 : Fin 2) = ψV` / `(1 : Fin 2) = 0` hold by **`rfl`** — the cleanest way to
   compute `gOf`'s value at a literal index (avoids `fin_cases`'s non-literal `⟨0,⋯⟩` terms
   breaking `rw`, another recorded gotcha).
3. **`cleanNbhd`/`nOf`/`DPrimeOf`**: `cleanNbhd D p ψ` is a chart-source neighbourhood of `p` that
   is simultaneously clean for `ψ` (order `≥ 0` away from `p`, via the previous builder's
   `exists_clean_nhds`) *and* avoids `D`'s other poles (`⊓ compOpens (D.finiteSupport.toFinset.erase
   p)`); `nOf D p ψ := max (D p) (-(ψ.ord p)).untop₀` is the smallest usable divisor bump at `p`,
   and `DPrimeOf D p ψ := D + bumpDivisor p (nOf D p ψ - D p)` the resulting auxiliary divisor
   (`D` away from `p`, `nOf D p ψ` at `p`).
4. **`gOf_memLD_of_clean`**: the *fully abstract* (no unfolding of `cleanNbhd`/`DPrimeOf` inside
   the proof — this was essential to avoid an unfolding-order "type mismatch" chase) fact that
   `gOf p V hpV D' ψV`'s coboundary is `D`-bounded whenever `V` is clean for `ψ` (away from `p`)
   and avoids `D`'s poles, and `ψV` restricts to `ψ`.
5. **`gOf_inclC0`/`pairCover_isRefIdx`/`gOf_resC0`**: `gOf` commutes with raising `D'`
   (`inclC0`) and with refining `V` to a smaller `W` (`resC0` along the identity refinement index)
   — both `rfl` after `fin_cases`+`Subtype.ext`.
6. **`mlClassAtOf`/`mlClassAtOf_raise_res`/`mlClassAtOf_agree`**: `mlClassAtOf p D D' ψ V ... ψV
   ... := mlClass (pairCover p V hpV) (gOf p V hpV D' ψV) (gOf_memLD_of_clean ...) : H1 D` is the
   single-point Mittag-Leffler class for *one specific* choice of `(V, D', ψV)`.
   `mlClassAtOf_raise_res` shows it is invariant under **simultaneously** shrinking `V` to `W ≤ V`
   and raising `D'` to `D'' ≥ D'` (combining `mlClass_inclC0` on the *same* cover then `mlClass_res`
   along the *same* `D'`, via `mlClass_congr` to bridge each step — **this is the load-bearing
   lemma of the whole file**). `mlClassAtOf_agree` upgrades this to **any two valid choices**
   (via a common refinement `W := V₁ ⊓ V₂` and a common bound `D'' := D'₁ ⊔ D'₂`, the latter valid
   because `ψ`'s own order bound at points of `W` is *already* witnessed by *either* `ψV₁` or
   `ψV₂`'s own membership, needing no `D`-side hypothesis at all for this half).
7. **`mlClassAt`/`mlClassAt_eq_of_valid`/`mlClassAt_eq_zero_of_mem_ordGe`/`mlClassAt_add`/
   `mlClassAt_smul`**: `mlClassAt D p ψ := mlClassAtOf` at the *canonical* choice
   (`cleanNbhd`/`DPrimeOf`/`ψVOf`). Kernel-vanishing (`ψ.ord p ≥ -(D p) ⟹ mlClassAt = 0`) is a
   direct `mlClass_eq_zero_of_exists` application with the *zero* global witness. Additivity/
   `ℂ`-linearity are each proved by relating **all operands** to a **single common** `(V, D')`
   (intersection of neighbourhoods, sup of divisors) via `mlClassAtOf_agree`, then using `gOf`'s
   own linearity + `mlClass_add`/`mlClass_smul` (built in `Skyscraper.lean`) at that *one* shared
   representation.
8. **`tailAtToH1`/`tailToH1`**: `mlClassAtRaw D p : MeroGermOn X (chartAt p).source →ₗ[ℂ] H1 D`
   packages `mlClassAt`/`mlClassAt_add`/`mlClassAt_smul` into a genuine `LinearMap`;
   `tailAtToH1 D p : TailAt p D →ₗ[ℂ] H1 D` descends it via `Submodule.liftQ` (kernel condition =
   `mlClassAt_eq_zero_of_mem_ordGe`); **`tailToH1 D : T D →ₗ[ℂ] H1 D` is `DFinsupp.lsum ℕ
   tailAtToH1`** — Miranda's tail-datum-to-cohomology-class comparison map, **CC8's `tailToH1`,
   fully constructed**.

**Two build-environment gotchas fixed along the way (both required, both now permanent fixes in
this unit's files, safe for downstream consumers):**
- `TailSpace.lean`'s `TailAt p D` was changed from a plain `def` to **`abbrev`** (matching `T D`'s
  own D2 convention), and its two hand-written `instAddCommGroupTailAt`/`instModuleTailAt`
  instances were **removed** (now found automatically through the transparent quotient). Without
  this, `Submodule.liftQ`'s output type and `TailAt p D` (as separately-instanced) do not unify
  even though they are definitionally the same quotient — confirmed by `apply`'s own unification
  trace showing the *same* quotient type on both sides but *different* (though propositionally
  equal) instance terms. `TailAt.mk`/`windowAt_toTailAt`'s existing proofs are unaffected
  (`scripts/check.sh Jacobian/LaurentTail` reverified `TailSpace.lean`/`Truncation.lean` still pass
  after this change).
- **`AddCommGroup (Cech.H1 D)` is *not* found by plain `inferInstance`/typeclass search** through
  the `H1` abbrev, even though `H1 D`'s *definition* (`Module.DirectLimit …`) genuinely has one:
  `Module.DirectLimit.addCommGroup` (`Mathlib.Algebra.Colimit.Module`) takes its index family `G`
  and connecting maps `f` as **leading explicit arguments** (re-declared, shadowing the section
  variables), which apparently defeats automatic instance search discovery through the `abbrev`
  (confirmed by an isolated `example (D) : AddCommGroup (Cech.H1 D) := inferInstance` failing evein
  with every relevant instance — `DecidableEq`/`Preorder`/`IsDirectedOrder (FinCover ⊤)` — already
  in scope, while `Module.DirectLimit.addCommGroup (fun 𝒰 => H1Cover D 𝒰) (fun _ _ h => resH1' D
  h)` applied *explicitly* type-checks instantly). Fixed *locally* in this file by registering it
  as a genuine global instance, `instAddCommGroupH1`, immediately before it is first needed
  (`mlClassAtRaw`) — **do not delete this instance**; every later construction targeting `H1 D` as
  a `Module`/`AddCommGroup` (this file's `tailAtToH1`, and any future `RiemannRoch.lean`/
  `TailDuality` construction building a `LinearMap … →ₗ[ℂ] H1 D`) needs it in scope. Flagged as a
  `docs/requests/cech-cohomology.md` item: register this globally in `Cech/Colimit.lean` itself so
  downstream units don't have to rediscover this.
- Recorded gotcha (used throughout `Realizes`/`gOf`-adjacent proofs): `fin_cases i` on an `i : Fin
  (𝒰.n)` substitutes `⟨0, ⋯⟩`/`⟨1, ⋯⟩` (not the `OfNat` literal `0`/`1`), which silently breaks
  `rw`/pattern-matching against lemmas stated with `(0 : Fin 2)`/`(1 : Fin 2)`. Two independent
  fixes used here: (a) state the target lemma so its LHS is provably `rfl` for the substituted
  value (`gOf_apply_zero`/`_one`, `Subtype.ext; rfl`-closable regardless of literal vs `⟨_,_⟩`
  form); (b) `erw` in place of `rw` when (a) isn't available. `mlClass_congr`'s `subst`-based
  transport is the analogous fix one level up, for `mlClass`'s own dependent `hg` argument.

**Deferred, with the exact gate and a fully worked-out completion plan for each:**

1. **`tailToH1_alpha` (`tailToH1 D (alphaL D f) = 0`), gate: a genuinely new *multi-point*
   combination lemma.** `alpha D f := T.mk D (alphaFinset D f) (fun p => TailAt.mk p D (restrict
   f))`, so (by `DFinsupp.lsum`'s own additivity over its finite support)
   `tailToH1 D (alphaL D f) = ∑_{p ∈ alphaFinset D f} mlClassAt D p (restrict f)`. Each *individual*
   summand is generally **nonzero** (a single marked point's local contribution is not a coboundary
   by itself — only the *global* Mittag-Leffler sum is, by the residue-theorem-style cancellation);
   this file only proves the **two-point** case of combining local contributions
   (`mlClassAt_add`, via a common clean neighbourhood + a common divisor bound). The needed
   generalization: build, for a *finite* `Finset` `S` and a choice `ψ : S → germs`, a genuinely
   multi-marked-point analogue of `pairCover`/`gOf` (an `(|S|+1)`-member cover: one clean
   neighbourhood per `p ∈ S`, shrunk pairwise-disjoint via `compOpens` of the *other* marked points
   — exactly the pattern `Cech.SixTerm.lean`'s `exists_realization` already uses internally for
   its *own* adapted-cover construction, §6.9(c) of the cech design doc — plus one shared
   "background" member), together with an `S`-indexed generalization of
   `mlClassAtOf_agree`/`mlClassAtOf_raise_res` (induct on `S` via `Finset.induction_on`, combining
   one new point at each step exactly as `mlClassAt_add` already does for two). Once this lands,
   applying `mlClass_eq_zero_of_exists` with the *global* witness `φ := f` (the difference `g_i -
   restrict f` is then **exactly** `0` on every member, not merely `D`-bounded, since every member
   's cochain component *is* a restriction of `f`) closes it — genuinely the same "direct
   application" the design doc's §5.2(a) always expected, gated only on the bookkeeping above.
2. **`H1Tail.toH1 : H1Tail D →ₗ[ℂ] H1 D`**, gate: (1) above (`LinearMap.range (alphaL D) ≤
   LinearMap.ker (tailToH1 D)`, then `Submodule.liftQ`/`Submodule.mapQ`-style descent — mechanical
   once (1) is available; reuse the `AddCommGroup (H1 D)` instance gotcha fix above, it will be
   needed again here).
3. **`H1Tail.toH1_injective`**, gate: (2), then **zero new mathematical content** — per the design
   doc §5.2(c) and the frozen `serre-duality-tails` design's own audit (§1.1): `Cech.toH1_injective`
   / `mlClass_eq_zero_iff` (**both directions**) are confirmed **landed** (`Injectivity.lean:247`,
   `Skyscraper.lean:176`), so the design's originally-flagged risk R2 is fully discharged upstream;
   only the mechanical reduction through `mlClassAt`'s construction remains, once (1)/(2) exist.
4. **`H1Tail.toH1_surjective`**, gate: `dolbeault-comparison`'s Leray theorem
   (`RS.Cech.toH1_surjective_of_isGood`), confirmed **not yet landed**
   (`Jacobian/DolbeaultComparison/Leray.lean`, 345 lines at this build, ends at `exists_crossGlue`
   — the member-gluing step, not yet the surjectivity conclusion; `Colimit.lean`'s own "Leray
   interface" comment records the exact expected signature). **Soft dependency, not circular**
   (per design §8 R1) — re-attempt once that file lands the theorem.
5. **`H1Tail.equiv : H1Tail D ≃ₗ[ℂ] Cech.H1 D`**, gate: (3) + (4) via `LinearEquiv.ofBijective`.

None of (1)-(5) needed anything beyond what's already exported by `Jacobian.Cech`/
`Jacobian.Meromorphic` plus this file's own new lemmas (items 1-8 above) — the remaining work is
concrete, scoped bookkeeping (estimated 150-250 more lines for (1) in this codebase's style,
plus ≈80 lines for (2)-(3), (5) is a one-liner), not new mathematics, and (4) is entirely upstream.
-/
