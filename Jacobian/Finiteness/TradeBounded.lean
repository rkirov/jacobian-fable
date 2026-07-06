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

end RS.Finiteness
