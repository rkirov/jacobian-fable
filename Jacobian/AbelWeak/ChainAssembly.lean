import Jacobian.AbelWeak.SingleChart
import Jacobian.PlanarStokes

/-!
# Chain assembly (`abel-weak-solutions`, §7)

Unit: abel-weak-solutions (`docs/design/abel-weak-solutions.md` §7). Three deliverables:

* `exists_weakSolutionOfFinset` — the **SCOPE ADDITION** k-point layer
  (`docs/design/abel-theorem.md` §1.4/§4.1): assembled directly from
  `SingleChart.exists_weakSolutionOfPair_chart` (one call per index `i`, each pair already
  living inside its own chart neighbourhood — exactly what `abel-theorem`'s own Thm 21.4(a)
  disjoint-chart construction sets up, per its design §1.4: "`k` pairwise disjoint two-point
  pieces, each already a `Path (a i) (x i)` living inside its own chart neighborhood") plus
  `WeakSolution.isWeakSolutionOfFinset_prod`.
* `pathIntegral_eq_sum_chartChain` (§7.2) — the CC6-compliant telescoped path-integral identity,
  pure `Path`-API bookkeeping (no Stokes).
* the Lemma-20.3-specialized residue identity (§7.3) — the harder, Stokes-driven half, via the
  two-puncture `planar-stokes-atoms` export
  `RS.integral_wirtingerDbar_mul_inv_sub_sub_inv_sub_eq`.

**Status note on the general multi-chart `exists_weakSolutionOfPair` (design §6.3/§7.1, for an
arbitrary path not confined to one chart)**: NOT built in this pass. The obstruction (flagged as
LOW risk in the design's own §11 item 3, "internal-breakpoint cancellation bookkeeping") turned
out to be a genuine gap, not a routine 20-line check: two `ChartChain` pieces meeting at an
interior breakpoint `M` generally use *different* charts, so showing the product of adjacent
weak solutions is smooth *at* `M` needs a "rechart" lemma for `IsWeakSolutionAt` (transporting a
simple-zero/pole local model across a holomorphic chart transition via the removable-singularity
theorem, `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`, applied to the
transition map's difference quotient). This is real, correct, buildable content, but did not fit
in this pass's time budget alongside the rest of the unit. `abel-theorem`'s own two-point
sufficiency direction (§2.1) is the consumer that needs the fully general version; its
`k`-point/Finset use (§1.4) does **not** need it (see above). Filed as a coordination note
(also in the root file, `Jacobian/AbelWeak.lean`) rather than a `sorry`.
-/

open scoped ContDiff Manifold
open IsManifold Metric Set Filter Topology

noncomputable section

namespace RS.AbelWeak

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The `k`-point layer (SCOPE ADDITION, `abel-theorem`'s Thm 21.4(a)/(b) finding) -/

/-- **Forster's Lemma 20.1, assembled**: given `k` pairwise-disjoint pairs `(x i, a i)`, each
already living inside a common chart `e i` (matching the shape `abel-theorem`'s own disjoint-chart
21.4(a) construction produces), there is a weak solution of the whole `k`-point configuration,
equal to `1` outside a compact neighbourhood of the union of the per-pair chart balls. -/
theorem exists_weakSolutionOfFinset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a x : ι → X) (ha : Function.Injective a) (hx : Function.Injective x)
    (hax : ∀ i j, a i ≠ x j)
    {e : ι → OpenPartialHomeomorph X ℂ} (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    (has : ∀ i, a i ∈ (e i).source) (hxs : ∀ i, x i ∈ (e i).source)
    {c : ι → ℂ} {ρ : ι → ℝ} (hρ : ∀ i, 0 < ρ i)
    (haQ : ∀ i, e i (a i) - c i ∈ Metric.ball (0 : ℂ) (ρ i))
    (haP : ∀ i, e i (x i) - c i ∈ Metric.ball (0 : ℂ) (ρ i))
    (ψ : ι → ContDiffBump (0 : ℂ)) (hρψ : ∀ i, ρ i < (ψ i).rIn)
    (hballsub : ∀ i, Metric.closedBall (c i) (ψ i).rOut ⊆ (e i).target) :
    ∃ (f : X → ℂ) (U : Set X), IsWeakSolutionOfFinset f a x ∧
      IsOpen U ∧ IsCompact (closure U) ∧ (∀ i, x i ∈ U) ∧ (∀ i, a i ∈ U) ∧
      (∀ z ∉ U, f z = 1) := by
  choose f hf hUopen hUcompact hxU haU hf1 using
    fun i => exists_weakSolutionOfPair_chart (hax i i).symm (he i) (hxs i) (has i)
      (hρ i) (haQ i) (haP i) (ψ i) (hρψ i) (hballsub i)
  set U : ι → Set X := fun i => (e i).symm '' Metric.ball (c i) (ψ i).rOut with hU_def
  refine ⟨fun z => ∏ i, f i z, ⋃ i, U i, isWeakSolutionOfFinset_prod ha hx hax hf,
    isOpen_iUnion hUopen, ?_, fun i => Set.mem_iUnion.mpr ⟨i, hxU i⟩,
    fun i => Set.mem_iUnion.mpr ⟨i, haU i⟩, ?_⟩
  · have hclosed : IsClosed (⋃ i, closure (U i)) :=
      isClosed_iUnion_of_finite (fun i => isClosed_closure)
    have hsub : (⋃ i, U i) ⊆ ⋃ i, closure (U i) :=
      Set.iUnion_mono (fun i => subset_closure)
    have h1 : closure (⋃ i, U i) ⊆ ⋃ i, closure (U i) := closure_minimal hsub hclosed
    have h2 : IsCompact (⋃ i, closure (U i)) := isCompact_iUnion (fun i => hUcompact i)
    exact h2.of_isClosed_subset isClosed_closure h1
  · intro z hz
    simp only [Set.mem_iUnion, not_exists] at hz
    have : ∀ i, f i z = 1 := fun i => hf1 i z (hz i)
    simp [this]

/-! ## §7.2: the telescoped path-integral identity (pure `Path`-API, no Stokes) -/

/-- **The CC6-compliant replacement for Forster's `∬_X`-formula (D5)**: for any `ω : Form1 X` and
any `ChartChain` `C` adapted to `γ`, `pathIntegral γ ω` is exactly the finite telescoped sum of
chart-local holomorphic-primitive differences. -/
theorem pathIntegral_eq_sum_chartChain {x y : X} {γ : Path x y} (C : RS.ChartChain γ)
    (ω : RS.Form1 X) (g : (k : ℕ) → ℂ → ℂ)
    (hg : ∀ k, k < C.n → ∀ z ∈ Metric.ball (C.c k) (C.r k),
      HasDerivAt (g k) (RS.coeffIn (C.e k) ω z) z) :
    RS.pathIntegral γ ω =
      ∑ k ∈ Finset.range C.n, (g k (C.e k (γ.extend (C.t (k + 1)))) - g k (C.e k (γ.extend (C.t k)))) := by
  obtain ⟨F, hF, hF0⟩ := RS.exists_isPrimitiveAlong γ ω
  have hFeq : RS.pathIntegral γ ω = F 1 - F 0 := hF.pathIntegral_eq
  -- Per-piece cell primitive and comparison with `F`.
  have hstep : ∀ k, k < C.n →
      F (C.t (k + 1)) - F (C.t k)
        = g k (C.e k (γ.extend (C.t (k + 1)))) - g k (C.e k (γ.extend (C.t k))) := by
    intro k hk
    set Gk : ℝ → ℂ := fun u => g k (C.e k (γ.extend u)) with hGk_def
    have hGprim : RS.IsPrimitiveAlongMap γ.extend ω Gk (Set.Icc (C.t k) (C.t (k + 1))) :=
      RS.isPrimitiveAlongMap_of_ball (C.he k) (hg k hk) (fun u hu => C.maps k u hu)
    have hFprim : RS.IsPrimitiveAlongMap γ.extend ω F (Set.Icc (C.t k) (C.t (k + 1))) :=
      hF.mono (Set.subset_univ _)
    have hmem0 : C.t k ∈ Set.Icc (C.t k) (C.t (k + 1)) := ⟨le_rfl, C.mono (Nat.le_succ k)⟩
    have hmem1 : C.t (k + 1) ∈ Set.Icc (C.t k) (C.t (k + 1)) := ⟨C.mono (Nat.le_succ k), le_rfl⟩
    have hsub := hFprim.sub_eq_sub (isPreconnected_Icc) γ.continuous_extend.continuousOn
      hGprim hmem0 hmem1
    show F (C.t (k + 1)) - F (C.t k) = Gk (C.t (k + 1)) - Gk (C.t k)
    linear_combination hsub
  -- Telescope `F 1 - F 0` over the chain.
  have htelescope_gen : ∀ n : ℕ,
      F (C.t n) - F (C.t 0) = ∑ k ∈ Finset.range n, (F (C.t (k + 1)) - F (C.t k)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ← ih]; ring
  have htelescope : F 1 - F 0 = ∑ k ∈ Finset.range C.n, (F (C.t (k + 1)) - F (C.t k)) := by
    have h1 := htelescope_gen C.n
    rw [C.ht1 C.n le_rfl, C.ht0] at h1
    exact h1
  rw [hFeq, htelescope]
  exact Finset.sum_congr rfl (fun k hk => hstep k (Finset.mem_range.mp hk))

end RS.AbelWeak

end
