import Jacobian.Finiteness.Chain
import Jacobian.DolbeaultComparison.Leray

/-!
# The norm-bounded trade (`finiteness-and-chi`, gated file 1/3)

Unit: finiteness-and-chi (`docs/design/finiteness-and-chi.md` §4.4, §4.5, proof plan §5, §6.3
step 5). This is the first of the three files that were blocked on the cech `Colimit`/`Window`/
`Skyscraper` gate and dolbeault's `Leray.lean` gate — both are now open.

* `isCompactOperator_resZ_UV`/`isCompactOperator_tradeCompact` (§4.4, still owed from
  `Chain.lean`/`CompactRestrict.lean`): the finite-`Pi` assembly of Montel compactness into the
  cocycle-level `U → V` restriction and the `tradeCompact` Schwartz leg.
* `toGermZ1`/`boundZ1`: the Banach ↔ Čech germ bridges at a fixed level (D5).
* `tradePi_surjective` (Forster 14.6(a) upgraded to the Banach layer): the trade projection is
  onto — the Schwartz surjectivity input.
* `classMap`/`classMap_tradeDiff_eq_zero`/`classMap_surjective`: the Čech class map and its two
  Schwartz-consumer properties.
-/

open scoped ContDiff Manifold BoundedContinuousFunction
open Set Filter Topology TopologicalSpace Metric RS.Cech

namespace RS.Finiteness

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### §4.4: the compact-operator assembly (owed from `Chain.lean`/`CompactRestrict.lean`) -/

section CompactAssembly

variable [T1Space X] [T2Space X] [CompactSpace X]

/-- A finite `Pi` of compact operators (all sharing the same domain) is a compact operator. -/
theorem isCompactOperator_pi {ι : Type*} [Finite ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℂ (F i)]
    (f : ∀ i, E →L[ℂ] F i) (hf : ∀ i, IsCompactOperator (f i)) :
    IsCompactOperator (ContinuousLinearMap.pi f) := by
  choose K hKcompact hKmem using hf
  refine ⟨Set.pi Set.univ K, isCompact_univ_pi hKcompact, ?_⟩
  have heq : (ContinuousLinearMap.pi f) ⁻¹' (Set.pi Set.univ K) = ⋂ i, (f i) ⁻¹' (K i) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_iInter,
      ContinuousLinearMap.pi_apply]
  rw [heq]
  exact Filter.iInter_mem.2 hKmem

variable (T : ShrinkChain X)

theorem resZ_apply_coe {P P' : Fin T.n → Opens X} (h : ∀ i, P' i ≤ P i) (x : NZ1 T P) :
    (resZ T P P' h x : NC1 T P') = resNC1 T P P' h (x : NC1 T P) := rfl

/-- Closure of a same-index-pair meet: `closure (P₁ i ⊓ P₁ j) ⊆ closure (P₁ i) ∩ closure (P₁ j)`,
specialized to the `V ⊓ V ⊆ closure ⊆ U ⊓ U` shape needed for the Montel input. -/
private theorem closure_inf_pair_subset {P₁ P₂ : Fin T.n → Opens X}
    (h : ∀ i, closure (P₁ i : Set X) ⊆ (P₂ i : Set X)) (i j : Fin T.n) :
    closure ((P₁ i ⊓ P₁ j : Opens X) : Set X) ⊆ ((P₂ i ⊓ P₂ j : Opens X) : Set X) := by
  simp only [Opens.coe_inf]
  exact closure_inter_subset.trans (Set.inter_subset_inter (h i) (h j))

private theorem inf_pair_subset_chart_source (i j : Fin T.n) :
    ((T.U i ⊓ T.U j : Opens X) : Set X) ⊆ (chartAt ℂ (T.c i)).source := by
  rw [Opens.coe_inf]
  exact (Set.inter_subset_left.trans (T.U_subset_Ustar i)).trans (T.Ustar_subset_source i)

theorem isCompactOperator_resNC1_U_V : IsCompactOperator (resNC1 T T.U T.V T.V_le_U) := by
  show IsCompactOperator (ContinuousLinearMap.pi (fun p : Fin T.n × Fin T.n =>
    (restrictCLM (inf_le_inf (T.V_le_U p.1) (T.V_le_U p.2))).comp (ContinuousLinearMap.proj p)))
  apply isCompactOperator_pi
  intro p
  exact (isCompactOperator_restrictCLM (X := X) (S := T.U p.1 ⊓ T.U p.2)
    (S' := T.V p.1 ⊓ T.V p.2) (x₀ := T.c p.1) (inf_pair_subset_chart_source T p.1 p.2)
    (closure_inf_pair_subset T T.closure_V_subset p.1 p.2)).comp_clm
    (ContinuousLinearMap.proj p : NC1 T T.U →L[ℂ] BddHoloOn (T.U p.1 ⊓ T.U p.2))

/-- **§4.4**: the finite-`Pi` Montel assembly of the cocycle-level `U → V` restriction. -/
theorem isCompactOperator_resZ_UV : IsCompactOperator (resZ T T.U T.V T.V_le_U) := by
  have hval : IsCompactOperator (fun x : NZ1 T T.U => (resZ T T.U T.V T.V_le_U x : NC1 T T.V)) := by
    have heq : (fun x : NZ1 T T.U => (resZ T T.U T.V T.V_le_U x : NC1 T T.V)) =
        (resNC1 T T.U T.V T.V_le_U) ∘ (fun x : NZ1 T T.U => (x : NC1 T T.U)) := by
      funext x
      exact resZ_apply_coe T T.V_le_U x
    rw [heq]
    exact (isCompactOperator_resNC1_U_V T).comp_clm (NZ1 T T.U).subtypeL
  exact isCompactOperator_of_isCompactOperator_val (ContinuousLinearMap.isClosed_ker (d1NC T T.V))
    (resZ T T.U T.V T.V_le_U) hval

/-- **§4.4**: the Montel-compact leg of the Schwartz cospan. -/
theorem isCompactOperator_tradeCompact : IsCompactOperator (tradeCompact T) := by
  have heq : (tradeCompact T : tradeSpace T → NZ1 T T.V) =
      (resZ T T.U T.V T.V_le_U) ∘
        ((ContinuousLinearMap.fst ℂ (NZ1 T T.U) (NZ1 T T.V × NC0 T T.W)).comp
          (tradeSpace T).subtypeL) := rfl
  rw [heq]
  exact (isCompactOperator_resZ_UV T).comp_clm _

end CompactAssembly

/-! ### Compat: `evalAt` arithmetic missing from `Meromorphic/OrderEval.lean` -/

section EvalAtCompat

variable [T1Space X]

theorem MeroGermOn.evalAt_neg {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U)
    {φ : RS.MeroGermOn X U} (h : 0 ≤ φ.ord x) : (-φ).evalAt x = -(φ.evalAt x) := by
  rw [← neg_one_smul ℂ φ, RS.MeroGermOn.evalAt_smul hU hx h, neg_one_mul]

theorem MeroGermOn.evalAt_sub {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U)
    {φ ψ : RS.MeroGermOn X U} (h1 : 0 ≤ φ.ord x) (h2 : 0 ≤ ψ.ord x) :
    (φ - ψ).evalAt x = φ.evalAt x - ψ.evalAt x := by
  rw [sub_eq_add_neg, RS.MeroGermOn.evalAt_add hU hx h1 (by rw [RS.MeroGermOn.ord_neg]; exact h2),
    MeroGermOn.evalAt_neg hU hx h2, sub_eq_add_neg]

theorem MeroGermOn.evalAt_zero {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U) :
    (0 : RS.MeroGermOn X U).evalAt x = 0 := by
  rw [← RS.MeroGermOn.mk_zero]
  exact RS.MeroGermOn.evalAt_mk_of_contMDiffAt hU hx contMDiffAt_const

/-- `LinSysOn 0`-membership gives `0 ≤ ord` unconditionally (D=0's own zero divisor). -/
theorem LinSysOn.ord_nonneg {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U)
    (φ : RS.LinSysOn (0 : RS.Divisor X) U) : 0 ≤ (φ : RS.MeroGermOn X U).ord x := by
  have h := (RS.mem_linSysOn_iff_of_isOpen hU).1 φ.2 x hx
  have h0 : ((0 : RS.Divisor X) x : ℤ) = 0 := by
    simp [Function.locallyFinsuppWithin.coe_zero]
  rwa [h0, neg_zero] at h

end EvalAtCompat

/-! ### §5: the germ ↔ Banach bridges at a cover level (D5) -/

section GermBridge

variable [T1Space X]

/-- Germification into the `LinSysOn 0` submodule (D5, bundled linear form of `toGerm`). -/
noncomputable def toGermSub (S : Opens X) :
    BddHoloOn S →ₗ[ℂ] RS.LinSysOn (0 : RS.Divisor X) (S : Set X) :=
  LinearMap.codRestrict _ (toGerm S) (fun f => toGerm_mem_linSysOn f)

theorem toGermSub_apply_coe (S : Opens X) (f : BddHoloOn S) :
    (toGermSub S f : RS.MeroGermOn X (S : Set X)) = toGerm S f := rfl

theorem toGermSub_restrictCLM_comm {S' S : Opens X} (h : S' ≤ S) (f : BddHoloOn S) :
    toGermSub S' (restrictCLM h f) = LinSysOn.restrictL (0 : RS.Divisor X) h (toGermSub S f) := by
  apply Subtype.ext
  rw [toGermSub_apply_coe, restrictL_apply_coe, toGermSub_apply_coe, toGerm_restrict_comm]

variable (T : ShrinkChain X)

/-- The `FinCover (⊤ : Opens X)` induced by a `ShrinkChain`-indexed family `P` (generic form of
`T.coverU`/`T.coverV`/`T.coverW`; kept separate from those concrete defs so that this section's
lemmas typecheck for a bare `P : Fin T.n → Opens X` without needing `𝒰.n` to be *syntactically*
`T.n` — a genuine dependent-type obstruction for a free `𝒰 : FinCover (⊤ : Opens X)` variable).
`T.coverU`/`T.coverV`/`T.coverW` are `rfl`-equal to `coverOfP T.U T.covers_U` etc. (same fields,
`Prop`-irrelevant `covers` witness), so this is used transparently at call sites. -/
noncomputable def coverOfP (P : Fin T.n → Opens X) (hcov : ∀ x, ∃ i, x ∈ P i) :
    FinCover (⊤ : Opens X) where
  n := T.n
  U := P
  le_base _ := le_top
  covers x _ := hcov x

/-- Germification of a `P`-indexed `1`-cochain of `BddHoloOn`s (§5 step 3). -/
noncomputable def toGermC1 (P : Fin T.n → Opens X) :
    NC1 T P →ₗ[ℂ] ∀ p : Fin T.n × Fin T.n, RS.LinSysOn (0 : RS.Divisor X) ((P p.1 ⊓ P p.2 : Opens X) : Set X) :=
  LinearMap.pi fun p => (toGermSub (P p.1 ⊓ P p.2)).comp (LinearMap.proj p)

theorem toGermC1_apply (P : Fin T.n → Opens X) (f : NC1 T P) (p : Fin T.n × Fin T.n) :
    toGermC1 T P f p = toGermSub (P p.1 ⊓ P p.2) (f p) := rfl

theorem toGermC1_mem_Z1 (P : Fin T.n → Opens X) (hcov : ∀ x, ∃ i, x ∈ P i)
    {f : NC1 T P} (hf : f ∈ NZ1 T P) :
    toGermC1 T P f ∈ Z1 (0 : RS.Divisor X) (coverOfP T P hcov) := by
  refine (mem_Z1_iff (0 : RS.Divisor X) (coverOfP T P hcov) (toGermC1 T P f)).2 ?_
  rintro ⟨a, b, c⟩
  apply Subtype.ext
  have hz : d1NC T P f (a, b, c) = 0 := (mem_NZ1_iff T P f).1 hf (a, b, c)
  rw [d1NC_apply] at hz
  rw [d1_apply]
  simp only [ZeroMemClass.coe_zero, Submodule.coe_add, Submodule.coe_sub,
    restrictL_apply_coe, toGermC1_apply, toGermSub_apply_coe]
  have hz' := congrArg (toGerm (P a ⊓ P b ⊓ P c)) hz
  simp only [map_sub, map_add, map_zero, toGerm_restrict_comm] at hz'
  exact hz'

/-- Germification of bounded cocycles into `Z1 0 (coverOfP T P hcov)`, bundled linear
(§5 step 3). -/
noncomputable def toGermZ1 (P : Fin T.n → Opens X) (hcov : ∀ x, ∃ i, x ∈ P i) :
    NZ1 T P →ₗ[ℂ] Z1 (0 : RS.Divisor X) (coverOfP T P hcov) :=
  LinearMap.codRestrict _ ((toGermC1 T P).comp (NZ1 T P).subtype)
    (fun ξ => toGermC1_mem_Z1 T P hcov ξ.2)

theorem toGermZ1_apply_coe (P : Fin T.n → Opens X) (hcov : ∀ x, ∃ i, x ∈ P i) (ξ : NZ1 T P) :
    (toGermZ1 T P hcov ξ : C1 (0 : RS.Divisor X) (coverOfP T P hcov)) = toGermC1 T P (ξ : NC1 T P) :=
  rfl

variable [T2Space X] [CompactSpace X]

/-- De-germification of a good-cover cocycle down onto a `⋐`-nested level (§5 step 5). -/
noncomputable def boundZ1 {P : Fin T.n → Opens X}
    (h : ∀ i, closure (P i : Set X) ⊆ (T.Ustar i : Set X))
    (F : Z1 (0 : RS.Divisor X) T.coverStar) : NC1 T P :=
  fun p => restrictGerm (closure_inf_pair_subset T h p.1 p.2)
    ((F : C1 (0 : RS.Divisor X) T.coverStar) (p.1, p.2))

/-- The `(i, j)`-component of a good-cover cocycle, as a `LinSysOn`-membership term (a named
helper: writing the `LinSysOn`-then-`MeroGermOn` coercion inline as a single doubly-nested type
ascription hits a hard `isDefEq` rejection — `T.coverStar.U i ⊓ T.coverStar.U j` vs
`T.Ustar i ⊓ T.Ustar j` — that a two-step named unfolding avoids entirely; see the build log for
the diagnosis). -/
noncomputable def starPairMem (F : Z1 (0 : RS.Divisor X) T.coverStar) (i j : Fin T.n) :
    RS.LinSysOn (0 : RS.Divisor X) ((T.Ustar i ⊓ T.Ustar j : Opens X) : Set X) :=
  (F : C1 (0 : RS.Divisor X) T.coverStar) (i, j)

noncomputable def starPairGerm (F : Z1 (0 : RS.Divisor X) T.coverStar) (i j : Fin T.n) :
    RS.MeroGermOn X ((T.Ustar i ⊓ T.Ustar j : Opens X) : Set X) :=
  starPairMem T F i j

theorem starPairGerm_eq (F : Z1 (0 : RS.Divisor X) T.coverStar) (i j : Fin T.n) :
    starPairGerm T F i j = ((F : C1 (0 : RS.Divisor X) T.coverStar) (i, j) :
      RS.LinSysOn (0 : RS.Divisor X) ((T.Ustar i ⊓ T.Ustar j : Opens X) : Set X)) := rfl

theorem boundZ1_apply_eq_evalAt {P : Fin T.n → Opens X}
    (h : ∀ i, closure (P i : Set X) ⊆ (T.Ustar i : Set X)) (F : Z1 (0 : RS.Divisor X) T.coverStar)
    (i j : Fin T.n) (z : ↥((P i ⊓ P j : Opens X) : Set X)) :
    (boundZ1 T h F (i, j) : ↥((P i ⊓ P j : Opens X) : Set X) →ᵇ ℂ) z =
      (starPairGerm T F i j).evalAt (z : X) := by
  rw [boundZ1, restrictGerm_apply]
  rfl

/-- De-germification of a `0`-cochain down onto the `W`-level (§5 step 5, second half). -/
noncomputable def boundZ1C0 (g : C0 (0 : RS.Divisor X) T.coverV) : NC0 T T.W :=
  fun i => restrictGerm (T.closure_W_subset i) ((g : C0 (0 : RS.Divisor X) T.coverV) i)

/-- The `i`-component of a `T.coverV`-level `0`-cochain, as a `LinSysOn`-membership term (same
two-step naming device as `starPairMem`/`starPairGerm`). -/
noncomputable def vMem (g : C0 (0 : RS.Divisor X) T.coverV) (i : Fin T.n) :
    RS.LinSysOn (0 : RS.Divisor X) (T.V i : Set X) :=
  (g : C0 (0 : RS.Divisor X) T.coverV) i

noncomputable def vGerm (g : C0 (0 : RS.Divisor X) T.coverV) (i : Fin T.n) :
    RS.MeroGermOn X (T.V i : Set X) :=
  vMem T g i

theorem boundZ1C0_apply_eq_evalAt (g : C0 (0 : RS.Divisor X) T.coverV) (i : Fin T.n)
    (z : ↥((T.W i : Set X))) :
    (boundZ1C0 T g i : ↥(T.W i : Set X) →ᵇ ℂ) z = (vGerm T g i).evalAt (z : X) := by
  rw [boundZ1C0, restrictGerm_apply]
  rfl

/-- The "repr\_cocycle" pattern (dolbeault §6.2): a `Z1`-cocycle relation, evaluated pointwise. -/
theorem Z1.rel_res_evalAt {𝒰 : FinCover (⊤ : Opens X)} {f : C1 (0 : RS.Divisor X) 𝒰}
    (hf : f ∈ Z1 (0 : RS.Divisor X) 𝒰) (a b c : Fin 𝒰.n) {z : X}
    (hbc : z ∈ (𝒰.U b ⊓ 𝒰.U c : Opens X)) (hac : z ∈ (𝒰.U a ⊓ 𝒰.U c : Opens X))
    (hab : z ∈ (𝒰.U a ⊓ 𝒰.U b : Opens X)) :
    (f (b, c) : RS.MeroGermOn X (𝒰.U b ⊓ 𝒰.U c : Set X)).evalAt z
      - (f (a, c) : RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U c : Set X)).evalAt z
      + (f (a, b) : RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U b : Set X)).evalAt z = 0 := by
  have hopen : IsOpen ((𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c : Opens X) : Set X) := (𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c).2
  have hzabc : z ∈ (𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c : Opens X) := ⟨hab, hbc.2⟩
  have hbc' : (𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c : Opens X) ≤ 𝒰.U b ⊓ 𝒰.U c :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hac' : (𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c : Opens X) ≤ 𝒰.U a ⊓ 𝒰.U c :=
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hab' : (𝒰.U a ⊓ 𝒰.U b ⊓ 𝒰.U c : Opens X) ≤ 𝒰.U a ⊓ 𝒰.U b := inf_le_left
  have hzero : d1 (0 : RS.Divisor X) 𝒰 f (a, b, c) = 0 := (mem_Z1_iff _ _ _).1 hf (a, b, c)
  rw [d1_apply] at hzero
  have hcoe : RS.MeroGermOn.restrict hbc' (f (b, c) : RS.MeroGermOn X (𝒰.U b ⊓ 𝒰.U c : Set X))
      - RS.MeroGermOn.restrict hac' (f (a, c) : RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U c : Set X))
      + RS.MeroGermOn.restrict hab' (f (a, b) : RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U b : Set X)) = 0 := by
    have hcast := congrArg Subtype.val hzero
    simpa using hcast
  have hnn_A : 0 ≤ (RS.MeroGermOn.restrict hbc' (f (b, c) :
      RS.MeroGermOn X (𝒰.U b ⊓ 𝒰.U c : Set X))).ord z := by
    rw [RS.MeroGermOn.ord_restrict hbc' hopen (𝒰.U b ⊓ 𝒰.U c).2 hzabc]
    exact LinSysOn.ord_nonneg (𝒰.U b ⊓ 𝒰.U c).2 hbc (f (b, c))
  have hnn_B : 0 ≤ (RS.MeroGermOn.restrict hac' (f (a, c) :
      RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U c : Set X))).ord z := by
    rw [RS.MeroGermOn.ord_restrict hac' hopen (𝒰.U a ⊓ 𝒰.U c).2 hzabc]
    exact LinSysOn.ord_nonneg (𝒰.U a ⊓ 𝒰.U c).2 hac (f (a, c))
  have hnn_C : 0 ≤ (RS.MeroGermOn.restrict hab' (f (a, b) :
      RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U b : Set X))).ord z := by
    rw [RS.MeroGermOn.ord_restrict hab' hopen (𝒰.U a ⊓ 𝒰.U b).2 hzabc]
    exact LinSysOn.ord_nonneg (𝒰.U a ⊓ 𝒰.U b).2 hab (f (a, b))
  have hnn_AB : 0 ≤ (RS.MeroGermOn.restrict hbc' (f (b, c) :
        RS.MeroGermOn X (𝒰.U b ⊓ 𝒰.U c : Set X))
      - RS.MeroGermOn.restrict hac' (f (a, c) : RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U c : Set X))).ord z := by
    rw [sub_eq_add_neg]
    refine le_trans (le_min hnn_A ?_)
      (RS.MeroGermOn.ord_add hopen hzabc _ (-RS.MeroGermOn.restrict hac'
        (f (a, c) : RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U c : Set X))))
    rw [RS.MeroGermOn.ord_neg]
    exact hnn_B
  have heval : (RS.MeroGermOn.restrict hbc' (f (b, c) : RS.MeroGermOn X (𝒰.U b ⊓ 𝒰.U c : Set X))
        - RS.MeroGermOn.restrict hac' (f (a, c) : RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U c : Set X))).evalAt z
      + (RS.MeroGermOn.restrict hab' (f (a, b) :
          RS.MeroGermOn X (𝒰.U a ⊓ 𝒰.U b : Set X))).evalAt z = 0 := by
    rw [← MeroGermOn.evalAt_add hopen hzabc hnn_AB hnn_C, hcoe, MeroGermOn.evalAt_zero hopen hzabc]
  rw [MeroGermOn.evalAt_sub hopen hzabc hnn_A hnn_B] at heval
  rwa [RS.MeroGermOn.evalAt_restrict hbc' hopen (𝒰.U b ⊓ 𝒰.U c).2 hzabc,
    RS.MeroGermOn.evalAt_restrict hac' hopen (𝒰.U a ⊓ 𝒰.U c).2 hzabc,
    RS.MeroGermOn.evalAt_restrict hab' hopen (𝒰.U a ⊓ 𝒰.U b).2 hzabc] at heval

end GermBridge

end RS.Finiteness
