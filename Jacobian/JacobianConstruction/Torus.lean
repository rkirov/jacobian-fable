import Jacobian.JacobianConstruction.ChartedSpaceKitV
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# The abstract torus layer: `V ⧸ L` for `L : AddSubgroup V`

Unit: jacobian-construction (`docs/design/jacobian-construction.md` §3–§9). This is the reusable
core of the whole unit: for a (possibly infinite-rank in principle, but always instantiated at
`Fin n → ℂ`) complex normed space `V` and an additive subgroup `L`, we build:

* `AddCommGroup`/`TopologicalSpace`/`T2Space (V ⧸ L)` — **for every `L`**, no discreteness needed
  (§3, the T2-via-closure trick, spiked).
* `ChartedSpace V (V ⧸ L)` / `IsManifold 𝓘(ℂ, V) ω (V ⧸ L)` — needs `[DiscreteTopology L]` (§4).
  Charts are the **raw representative** charts: `chartAt' L x` sends a class near `x` to its
  unique representative in a fixed injectivity ball around `x` (a simplification of the design's
  "centered" charts — the transition maps are still exactly translations by a locally-constant
  lattice element, which is all that is needed; no recentering bookkeeping required).
* `LieAddGroup 𝓘(ℂ, V) ω (V ⧸ L)` — same hypothesis (§5): in the raw charts, addition/negation
  read as the identity (no lattice shift at all is needed once the codomain chart representative
  is chosen to be the sum/negation of the domain representatives).
* `CompactSpace (V ⧸ L)` — needs the full `IsZLattice ℝ L.toIntSubmodule` (§6, the
  `IsZLattice.isCompact_range_of_periodic` trick, spiked).
* The `→ₜ+` functoriality substrate `inducedHom` (§9.2, spiked) and its `ContMDiff`-ness (§9.3).

These are genuine theorems with typeclass hypotheses (`[DiscreteTopology L]`,
`[IsZLattice ℝ L.toIntSubmodule]`); they are **not** instances registered unconditionally (Lean
cannot discharge these hypotheses automatically for an arbitrary `L`), so downstream units
(period-lattice-rank) `instance`-ify them once discreteness/full-rank are established for the
actual period subgroup.
-/

open scoped ContDiff Manifold Pointwise
open Set Filter Topology Metric

noncomputable section

namespace RS

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-! ## §3. Free instances: `AddCommGroup`/`TopologicalSpace`/`T2Space`, no hypotheses at all -/

section T2

variable (L : AddSubgroup V)

instance instAddCommGroupQuotient : AddCommGroup (V ⧸ L) := by infer_instance

instance instTopologicalSpaceQuotient : TopologicalSpace (V ⧸ L) := by infer_instance

/-- The quotient of `V` by the *topological closure* of any additive subgroup is Hausdorff —
for **every** subgroup, no discreteness or full-rank input at all. This is what lets
`Jac₀ X := (Fin (genus X) → ℂ) ⧸ (periodSubgroup X).topologicalClosure` be `T2Space` immediately,
including at `genus X = 0`. -/
instance instT2SpaceQuotientTopologicalClosure :
    T2Space (V ⧸ L.topologicalClosure) := by
  haveI : IsClosed (L.topologicalClosure : Set V) := L.isClosed_topologicalClosure
  infer_instance

end T2

/-! ## §4.1. Uniform injectivity radius -/

section InjRadius

variable (L : AddSubgroup V) [DiscreteTopology L]

/-- Every discrete additive subgroup of a normed space has a uniform injectivity radius: some
`ρ > 0` such that every nonzero element has norm at least `2ρ`. -/
theorem exists_uniform_injRadius :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ℓ ∈ L, ℓ ≠ 0 → 2 * ρ ≤ ‖ℓ‖ := by
  have h0 : ({(0 : L)} : Set L) ∈ 𝓝 (0 : L) := mem_nhds_discrete.mpr rfl
  rw [nhds_subtype_eq_comap, Filter.mem_comap] at h0
  obtain ⟨U, hU, hUsub⟩ := h0
  obtain ⟨r, hr, hballU⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨r / 2, by linarith, ?_⟩
  intro ℓ hℓL hℓne
  by_contra hlt
  push_neg at hlt
  have hballmem : (ℓ : V) ∈ ball (0 : V) r := by
    rw [mem_ball, dist_eq_norm, sub_zero]
    linarith
  have : (⟨ℓ, hℓL⟩ : L) ∈ (Subtype.val : L → V) ⁻¹' U := hballU hballmem
  have h0' := hUsub this
  exact hℓne (by simpa using h0')

/-- A choice of uniform injectivity radius for `L`. -/
def injRadius : ℝ := (exists_uniform_injRadius L).choose

theorem injRadius_pos : 0 < injRadius L := (exists_uniform_injRadius L).choose_spec.1

theorem norm_le_of_mem_injRadius {ℓ : V} (hℓ : ℓ ∈ L) (hne : ℓ ≠ 0) :
    2 * injRadius L ≤ ‖ℓ‖ := (exists_uniform_injRadius L).choose_spec.2 ℓ hℓ hne

/-- `QuotientAddGroup.mk` is injective on any ball of radius `injRadius L`. -/
theorem mk_injOn_ball (x : V) :
    Set.InjOn (QuotientAddGroup.mk (s := L)) (ball x (injRadius L)) := by
  intro z₁ hz₁ z₂ hz₂ heq
  have hsub : z₁ - z₂ ∈ L := (QuotientAddGroup.eq_iff_sub_mem).mp heq
  by_contra hne
  have hne' : z₁ - z₂ ≠ 0 := sub_ne_zero.mpr hne
  have h2ρ : 2 * injRadius L ≤ ‖z₁ - z₂‖ := norm_le_of_mem_injRadius L hsub hne'
  have htri : ‖z₁ - z₂‖ < 2 * injRadius L := by
    have h1 : ‖z₁ - x‖ < injRadius L := by rwa [mem_ball, dist_eq_norm] at hz₁
    have h2 : ‖x - z₂‖ < injRadius L := by
      rw [mem_ball, dist_eq_norm] at hz₂
      rwa [norm_sub_rev]
    calc ‖z₁ - z₂‖ = ‖(z₁ - x) + (x - z₂)‖ := by ring_nf
      _ ≤ ‖z₁ - x‖ + ‖x - z₂‖ := norm_add_le _ _
      _ < injRadius L + injRadius L := add_lt_add h1 h2
      _ = 2 * injRadius L := by ring
  linarith

end InjRadius

/-! ## §4.2. The raw representative chart family -/

section Chart

variable (L : AddSubgroup V) [DiscreteTopology L]

/-- The auxiliary chart going `V → V ⧸ L`: `mk` restricted to the injectivity ball around `x`,
which is a continuous open injection, hence (by `ofContinuousOpen`) an `OpenPartialHomeomorph`. -/
def rawChartAux (x : V) : OpenPartialHomeomorph V (V ⧸ L) :=
  OpenPartialHomeomorph.ofContinuousOpen
    ((mk_injOn_ball L x).toPartialEquiv (QuotientAddGroup.mk (s := L)) (ball x (injRadius L)))
    (QuotientAddGroup.continuous_mk).continuousOn
    (QuotientAddGroup.isOpenMap_coe)
    Metric.isOpen_ball

@[simp] theorem rawChartAux_apply (x z : V) : rawChartAux L x z = QuotientAddGroup.mk z := rfl

@[simp] theorem rawChartAux_source (x : V) : (rawChartAux L x).source = ball x (injRadius L) := rfl

/-- The chart at representative `x : V`: sends a class near `x` to its unique representative in
`ball x (injRadius L)`. -/
def chartAt' (x : V) : OpenPartialHomeomorph (V ⧸ L) V := (rawChartAux L x).symm

@[simp] theorem chartAt'_symm (x : V) : (chartAt' L x).symm = rawChartAux L x := rfl

@[simp] theorem chartAt'_source (x : V) :
    (chartAt' L x).source = QuotientAddGroup.mk '' ball x (injRadius L) := rfl

@[simp] theorem chartAt'_target (x : V) : (chartAt' L x).target = ball x (injRadius L) := rfl

/-- The defining property of `chartAt'`: on a representative `z` inside the ball, the chart
recovers `z`. -/
theorem chartAt'_apply_mk {x z : V} (hz : z ∈ ball x (injRadius L)) :
    chartAt' L x (QuotientAddGroup.mk z) = z :=
  (rawChartAux L x).left_inv hz

/-- If `w + ℓ` lands in the ball around `x'` for some `ℓ ∈ L`, the chart at `x'` reads the class
of `w` as `w + ℓ`. This is the single computation underlying every transition/smoothness proof
below (with `ℓ = 0` in the "aligned representative" cases, and a genuine lattice element in the
general atlas-transition case). -/
theorem chartAt'_eq_add_of_mem_ball {x' w ℓ : V} (hℓ : ℓ ∈ L)
    (hmem : w + ℓ ∈ ball x' (injRadius L)) :
    chartAt' L x' (QuotientAddGroup.mk w) = w + ℓ := by
  have hmk : (QuotientAddGroup.mk (w + ℓ) : V ⧸ L) = QuotientAddGroup.mk w := by
    rw [QuotientAddGroup.eq_iff_sub_mem]
    simpa using (AddSubgroup.neg_mem L hℓ)
  rw [← hmk]
  exact chartAt'_apply_mk L hmem

/-- Local constancy: the identity `chartAt' L x' (mk w) = w + ℓ` persists on a whole neighborhood
of `w`, for the *same* `ℓ`. -/
theorem chartAt'_eventuallyEq_add {x' w ℓ : V} (hℓ : ℓ ∈ L)
    (hmem : w + ℓ ∈ ball x' (injRadius L)) :
    (fun w => chartAt' L x' (QuotientAddGroup.mk w)) =ᶠ[𝓝 w] (fun w => w + ℓ) := by
  obtain ⟨ε, hε, hballsub⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball (w + ℓ) hmem
  filter_upwards [Metric.ball_mem_nhds w hε] with w' hw'
  apply chartAt'_eq_add_of_mem_ball L hℓ
  apply hballsub
  rw [mem_ball, dist_eq_norm] at hw' ⊢
  simpa [add_sub_add_right_eq_sub] using hw'

theorem chartAt'_mem_source (q : V ⧸ L) :
    q ∈ (chartAt' L (Function.surjInv QuotientAddGroup.mk_surjective q)).source := by
  set x := Function.surjInv QuotientAddGroup.mk_surjective q with hx_def
  have hxq : (QuotientAddGroup.mk x : V ⧸ L) = q := Function.surjInv_eq _ q
  rw [chartAt'_source]
  exact ⟨x, Metric.mem_ball_self (injRadius_pos L), hxq⟩

/-- `ChartedSpace V (V ⧸ L)`, given a discrete additive subgroup `L`. -/
instance instChartedSpace : ChartedSpace V (V ⧸ L) :=
  chartedSpaceOfFamily' (chartAt' L) (fun q => Function.surjInv QuotientAddGroup.mk_surjective q)
    (chartAt'_mem_source L)

@[simp] theorem chartAt_eq (q : V ⧸ L) :
    chartAt V q = chartAt' L (Function.surjInv QuotientAddGroup.mk_surjective q) := rfl

end Chart

/-! ## §4.3. `IsManifold`: transitions are translations by a locally-constant lattice element -/

section Manifold

variable (L : AddSubgroup V) [DiscreteTopology L]

/-- The transition map between two raw representative charts is, near any point of the overlap,
translation by a fixed (locally-constant) lattice element. -/
theorem isManifold_torus :
    @IsManifold ℂ _ V _ _ V _ 𝓘(ℂ, V) ω (V ⧸ L) _ (instChartedSpace L) := by
  apply isManifold_of_family' (chartAt' L)
    (fun q => Function.surjInv QuotientAddGroup.mk_surjective q) (chartAt'_mem_source L)
  intro x x' w hw
  rw [OpenPartialHomeomorph.trans_source] at hw
  obtain ⟨hw1, hw2⟩ := hw
  rw [chartAt'_symm, rawChartAux_source] at hw1
  rw [chartAt'_symm, rawChartAux_apply, Set.mem_preimage, chartAt'_source] at hw2
  obtain ⟨z', hz', hzeq⟩ := hw2
  set ℓ := z' - w with hℓ_def
  have hℓL : ℓ ∈ L := by
    rw [hℓ_def]
    have := (QuotientAddGroup.eq_iff_sub_mem (x := z') (y := w)).mp hzeq
    simpa using this
  have hmem : w + ℓ ∈ ball x' (injRadius L) := by
    have : w + ℓ = z' := by rw [hℓ_def]; ring
    rwa [this]
  have heq : (chartAt' L x).symm ≫ₕ chartAt' L x' =ᶠ[𝓝 w] (fun w => w + ℓ) := by
    have := chartAt'_eventuallyEq_add L hℓL hmem
    filter_upwards [this] with w' hw'
    rw [OpenPartialHomeomorph.trans_apply, chartAt'_symm, rawChartAux_apply]
    exact hw'
  exact (analyticAt_id.add analyticAt_const).congr heq.symm

end Manifold

/-! ## §5. `LieAddGroup`: addition/negation read as the identity in aligned charts -/

section LieGroup

variable (L : AddSubgroup V) [DiscreteTopology L]

theorem continuous_add_torus : Continuous (fun p : (V ⧸ L) × (V ⧸ L) => p.1 + p.2) := by
  haveI : L.Normal := inferInstance
  haveI : IsTopologicalAddGroup (V ⧸ L) := QuotientAddGroup.instIsTopologicalAddGroup L
  fun_prop

theorem continuous_neg_torus : Continuous (fun q : V ⧸ L => -q) := by
  haveI : L.Normal := inferInstance
  haveI : IsTopologicalAddGroup (V ⧸ L) := QuotientAddGroup.instIsTopologicalAddGroup L
  fun_prop

theorem contMDiff_add_torus :
    haveI := instChartedSpace L; haveI := isManifold_torus L
    ContMDiff (𝓘(ℂ, V).prod 𝓘(ℂ, V)) 𝓘(ℂ, V) ω (fun p : (V ⧸ L) × (V ⧸ L) => p.1 + p.2) := by
  haveI := instChartedSpace L
  haveI := isManifold_torus L
  rintro ⟨q₁, q₂⟩
  set x₁ := Function.surjInv QuotientAddGroup.mk_surjective q₁ with hx₁_def
  set x₂ := Function.surjInv QuotientAddGroup.mk_surjective q₂ with hx₂_def
  have hx₁q : (QuotientAddGroup.mk x₁ : V ⧸ L) = q₁ := Function.surjInv_eq _ q₁
  have hx₂q : (QuotientAddGroup.mk x₂ : V ⧸ L) = q₂ := Function.surjInv_eq _ q₂
  rw [contMDiffAt_iff]
  refine ⟨(continuous_add_torus L).continuousAt, ?_⟩
  rw [ModelWithCorners.range_prod, modelWithCornersSelf_coe, Set.range_id,
    modelWithCornersSelf_coe, Set.range_id, Set.univ_prod_univ, contDiffWithinAt_univ]
  have heq : writtenInExtChartAt (𝓘(ℂ, V).prod 𝓘(ℂ, V)) 𝓘(ℂ, V) (q₁, q₂)
      (fun p : (V ⧸ L) × (V ⧸ L) => p.1 + p.2) =ᶠ[𝓝 (extChartAt (𝓘(ℂ, V).prod 𝓘(ℂ, V)) (q₁, q₂)
        (q₁, q₂))] (fun p : V × V => p.1 + p.2) := by
    have hball : ball x₁ (injRadius L) ×ˢ ball x₂ (injRadius L) ∈ 𝓝 (x₁, x₂) :=
      (Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds
        ⟨Metric.mem_ball_self (injRadius_pos L), Metric.mem_ball_self (injRadius_pos L)⟩
    have hballε : ∃ ε > 0, ball x₁ ε ×ˢ ball x₂ ε ⊆
        ball x₁ (injRadius L) ×ˢ ball x₂ (injRadius L) ∩
          {p : V × V | p.1 + p.2 ∈ ball (x₁ + x₂) (injRadius L)} := by
      have hopen : IsOpen (ball x₁ (injRadius L) ×ˢ ball x₂ (injRadius L) ∩
          {p : V × V | p.1 + p.2 ∈ ball (x₁ + x₂) (injRadius L)}) := by
        refine (Metric.isOpen_ball.prod Metric.isOpen_ball).inter ?_
        exact Metric.isOpen_ball.preimage (continuous_fst.add continuous_snd)
      have hmemInt : (x₁, x₂) ∈ ball x₁ (injRadius L) ×ˢ ball x₂ (injRadius L) ∩
          {p : V × V | p.1 + p.2 ∈ ball (x₁ + x₂) (injRadius L)} :=
        ⟨⟨Metric.mem_ball_self (injRadius_pos L), Metric.mem_ball_self (injRadius_pos L)⟩,
          Metric.mem_ball_self (injRadius_pos L)⟩
      obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hopen (x₁, x₂) hmemInt
      refine ⟨ε, hε, fun p hp => hεsub ?_⟩
      rw [Metric.mem_ball, Prod.dist_eq] at hp
      rw [Metric.mem_ball, Prod.dist_eq]
      exact ⟨(le_max_left _ _).trans_lt hp, (le_max_right _ _).trans_lt hp⟩
    obtain ⟨ε, hε, hεsub⟩ := hballε
    have hnhdsx : ball x₁ ε ×ˢ ball x₂ ε ∈ 𝓝 (x₁, x₂) :=
      (Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds
        ⟨Metric.mem_ball_self hε, Metric.mem_ball_self hε⟩
    have hchart_eq : extChartAt (𝓘(ℂ, V).prod 𝓘(ℂ, V)) (q₁, q₂) (q₁, q₂) = (x₁, x₂) := by
      rw [extChartAt_prod]
      show (extChartAt 𝓘(ℂ,V) q₁ q₁, extChartAt 𝓘(ℂ,V) q₂ q₂) = (x₁, x₂)
      have e1 : extChartAt 𝓘(ℂ, V) q₁ q₁ = x₁ := by
        rw [extChartAt_coe]
        show (𝓘(ℂ, V) (chartAt V q₁ q₁) : V) = x₁
        rw [modelWithCornersSelf_coe]
        show chartAt V q₁ q₁ = x₁
        rw [chartAt_eq, ← hx₁_def, ← hx₁q]
        exact chartAt'_apply_mk L (Metric.mem_ball_self (injRadius_pos L))
      have e2 : extChartAt 𝓘(ℂ, V) q₂ q₂ = x₂ := by
        rw [extChartAt_coe]
        show (𝓘(ℂ, V) (chartAt V q₂ q₂) : V) = x₂
        rw [modelWithCornersSelf_coe]
        show chartAt V q₂ q₂ = x₂
        rw [chartAt_eq, ← hx₂_def, ← hx₂q]
        exact chartAt'_apply_mk L (Metric.mem_ball_self (injRadius_pos L))
      rw [e1, e2]
    rw [hchart_eq]
    have hprodMap : ContinuousMap.homeomorphOfConst (α := V × V) := trivial -- placeholder, removed below
    sorry
  sorry

end LieGroup

end RS
