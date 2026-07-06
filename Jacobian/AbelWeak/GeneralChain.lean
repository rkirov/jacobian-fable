import Jacobian.AbelWeak.Rechart
import Jacobian.AbelWeak.SingleChart
import Jacobian.Path.Chain

/-!
# The general multi-chart `exists_weakSolutionOfPair`

Unit: abel-weak-solutions, closing the gap recorded in this unit's own root docstring and in
`docs/design/abel-theorem.md` §1.4/§4.1. Builds the fully general two-point weak solution for an
ARBITRARY connecting path (not confined to one chart), by inducting along a `RS.ChartChain`
and gluing adjacent `SingleChart` pieces via `Rechart.lean`'s `IsWeakSolutionAt.mul`.

TODO(progress note): under active construction.
-/

open scoped ContDiff Manifold Classical
open IsManifold Metric Set Filter Topology

noncomputable section

namespace RS.AbelWeak

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Small helpers -/

omit [T2Space X] [IsManifold 𝓘(ℂ) ω X] in
/-- `IsWeakSolutionAt` transports along eventual equality of the underlying function. -/
theorem IsWeakSolutionAt.congr_of_eventuallyEq {f g : X → ℂ} {a : X} {k : ℤ}
    (hf : IsWeakSolutionAt f a k) (hfg : f =ᶠ[𝓝 a] g) : IsWeakSolutionAt g a k := by
  obtain ⟨e, he, ha, ψ, hψne, hψdiff, hfeq⟩ := hf
  exact ⟨e, he, ha, ψ, hψne, hψdiff, hfg.symm.trans hfeq⟩

omit [T2Space X] in
/-- The constant function `1` is (trivially) a weak solution of order `0` at any point. -/
theorem isWeakSolutionAt_one_zero (a : X) : IsWeakSolutionAt (fun _ : X => (1 : ℂ)) a 0 := by
  refine ⟨chartAt ℂ a, IsManifold.chart_mem_maximalAtlas a, mem_chart_source ℂ a,
    fun _ => 1, ?_, contDiffAt_const, ?_⟩
  · exact Filter.Eventually.of_forall fun _ => one_ne_zero
  · exact Filter.Eventually.of_forall fun _ => by simp

/-- A function that is `ContMDiffOn` away from `p` and nonvanishing away from `{p, q}` is,
at any OTHER point `x ∉ {p, q}`, a weak solution of order `0` (smooth, nonvanishing — no genuine
zero or pole there). -/
theorem isWeakSolutionAt_zero_of_ne {f : X → ℂ} {p q x : X}
    (hcm : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f {p}ᶜ) (hne : ∀ y, y ≠ p → y ≠ q → f y ≠ 0)
    (hxp : x ≠ p) (hxq : x ≠ q) : IsWeakSolutionAt f x 0 := by
  have hcm' : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f x := hcm.contMDiffAt (isOpen_compl_singleton.mem_nhds hxp)
  have hfx : f x ≠ 0 := hne x hxp hxq
  have hxmem : chartAt ℂ x ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X := IsManifold.chart_mem_maximalAtlas x
  refine ⟨chartAt ℂ x, hxmem, mem_chart_source ℂ x,
    fun z => f ((chartAt ℂ x).symm z), ?_, ?_, ?_⟩
  · have h1 : ContinuousAt (⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
      (contMDiffAt_symm_of_mem_maximalAtlas hxmem
        ((chartAt ℂ x).map_source (mem_chart_source ℂ x))).continuousAt
    have h2 : ContinuousAt f ((chartAt ℂ x).symm (chartAt ℂ x x)) := by
      rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]; exact hcm'.continuousAt
    have h3 : ContinuousAt (fun z => f ((chartAt ℂ x).symm z)) (chartAt ℂ x x) := h2.comp h1
    have h4 : f ((chartAt ℂ x).symm (chartAt ℂ x x)) ≠ 0 := by
      rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]; exact hfx
    exact h3.eventually_ne h4
  · exact contDiffAt_comp_symm_of_contMDiffAt hxmem
      (mem_chart_source ℂ x) hcm'
  · filter_upwards [(chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)] with y hy
    rw [(chartAt ℂ x).left_inv hy, zpow_zero, mul_one]

/-- Converse of `isWeakSolutionAt_zero_of_ne`'s conclusion: order `0` at `a` unfolds to genuine
smoothness and nonvanishing there. -/
theorem IsWeakSolutionAt.contMDiffAt_and_ne_zero_of_zero {f : X → ℂ} {a : X}
    (hf : IsWeakSolutionAt f a 0) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f a ∧ f a ≠ 0 := by
  obtain ⟨e, he, ha, ψ, hψne, hψdiff, hfeq⟩ := hf
  have heq : f =ᶠ[𝓝 a] fun x => ψ (e x) := by
    filter_upwards [hfeq] with x hx; rw [hx, zpow_zero, mul_one]
  have hcm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun x => ψ (e x)) a :=
    contMDiffAt_comp_of_contDiffAt he ha hψdiff
  have hfa : f a = ψ (e a) := heq.self_of_nhds
  exact ⟨hcm.congr_of_eventuallyEq heq, hfa ▸ hψne.self_of_nhds⟩

/-! ## The general chain induction -/

omit [IsManifold 𝓘(ℂ) ω X] in
/-- Merge two independently-repaired functions (each a `Function.update` of a COMMON base `f₀` at
its own point) into one, at two DISTINCT points `y₁ ≠ y₂`. -/
private theorem merge_two {f₀ h₁ h₂ : X → ℂ} {y₁ y₂ : X} {k₁ k₂ : ℤ} (hy : y₁ ≠ y₂)
    (hh1_ord : IsWeakSolutionAt h₁ y₁ k₁) (hh1_eq : ∀ x, x ≠ y₁ → h₁ x = f₀ x)
    (hh2_ord : IsWeakSolutionAt h₂ y₂ k₂) (hh2_eq : ∀ x, x ≠ y₂ → h₂ x = f₀ x) :
    ∃ h : X → ℂ, IsWeakSolutionAt h y₁ k₁ ∧ IsWeakSolutionAt h y₂ k₂ ∧
      ∀ x, x ≠ y₁ → x ≠ y₂ → h x = f₀ x := by
  classical
  refine ⟨Function.update h₁ y₂ (h₂ y₂), ?_, ?_, ?_⟩
  · apply hh1_ord.congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hy] with x hx
    exact (Function.update_of_ne hx _ _).symm
  · apply hh2_ord.congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hy.symm] with x hx1
    rcases eq_or_ne x y₂ with rfl | hxne2
    · rw [Function.update_self]
    · rw [Function.update_of_ne hxne2, hh1_eq x hx1, hh2_eq x hxne2]
  · intro x hx1 hx2
    rw [Function.update_of_ne hx2, hh1_eq x hx1]

omit [IsManifold 𝓘(ℂ) ω X] in
/-- Merge-three variant: `h₁` already carries facts at TWO distinct points `y₁ ≠ y₂` (agreeing
with the base `f₀` off both), `h₂` carries a fresh fact at a THIRD point `y₃` distinct from both. -/
private theorem merge_two' {f₀ h₁ h₂ : X → ℂ} {y₁ y₂ y₃ : X} {k₁ k₂ k₃ : ℤ}
    (hy13 : y₁ ≠ y₃) (hy23 : y₂ ≠ y₃)
    (hh1_ord1 : IsWeakSolutionAt h₁ y₁ k₁) (hh1_ord2 : IsWeakSolutionAt h₁ y₂ k₂)
    (hh1_eq : ∀ x, x ≠ y₁ → x ≠ y₂ → h₁ x = f₀ x)
    (hh2_ord : IsWeakSolutionAt h₂ y₃ k₃) (hh2_eq : ∀ x, x ≠ y₃ → h₂ x = f₀ x) :
    ∃ h : X → ℂ, IsWeakSolutionAt h y₁ k₁ ∧ IsWeakSolutionAt h y₂ k₂ ∧ IsWeakSolutionAt h y₃ k₃ ∧
      ∀ x, x ≠ y₁ → x ≠ y₂ → x ≠ y₃ → h x = f₀ x := by
  classical
  refine ⟨Function.update h₁ y₃ (h₂ y₃), ?_, ?_, ?_, ?_⟩
  · apply hh1_ord1.congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hy13] with x hx
    exact (Function.update_of_ne hx _ _).symm
  · apply hh1_ord2.congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hy23] with x hx
    exact (Function.update_of_ne hx _ _).symm
  · apply hh2_ord.congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hy13.symm,
      isOpen_compl_singleton.mem_nhds hy23.symm] with x hx1 hx2
    rcases eq_or_ne x y₃ with rfl | hxne3
    · rw [Function.update_self]
    · rw [Function.update_of_ne hxne3, hh1_eq x hx1 hx2, hh2_eq x hxne3]
  · intro x hx1 hx2 hx3
    rw [Function.update_of_ne hx3, hh1_eq x hx1 hx2]

/-- **The general multi-chart weak solution** (§6.3/§7.1 of `abel-weak-solutions.md`, the gap
this file closes): for an ARBITRARY path `δ : Path Q P` (not confined to one chart), there is a
weak solution of the pair `(P, Q)`. Built by inducting along a `RS.ChartChain δ`
(`Jacobian.Path.Chain`), gluing one `SingleChart` piece per chain link via `IsWeakSolutionAt.mul`
(`Rechart.lean`) — the `+1`-order zero of one piece cancels the `-1`-order pole of the next at
every interior breakpoint, including the (rare, but real) case where the breakpoint recurs at the
chain's own basepoint `Q`. -/
theorem exists_weakSolutionOfPair {P Q : X} (hPQ : Q ≠ P) (δ : Path Q P) :
    ∃ (f : X → ℂ) (U : Set X), IsWeakSolutionOfPair f P Q ∧
      IsOpen U ∧ IsCompact (closure U) ∧ P ∈ U ∧ Q ∈ U ∧ (∀ x ∉ U, f x = 1) := by
  classical
  obtain ⟨C⟩ := RS.exists_chartChain δ
  set M : ℕ → X := fun k => δ.extend (C.t k) with hM_def
  have hM0 : M 0 = Q := by rw [hM_def]; simp only; rw [C.ht0, δ.extend_zero]
  have hMn : M C.n = P := by rw [hM_def]; simp only; rw [C.ht1 C.n le_rfl, δ.extend_one]
  set ordAt : ℕ → X → ℤ :=
    fun m x => (if x = M 0 then (-1 : ℤ) else 0) + (if x = M m then (1 : ℤ) else 0)
    with hordAt_def
  have main : ∀ m ≤ C.n, ∃ (f : X → ℂ) (U : Set X), IsOpen U ∧ IsCompact (closure U) ∧
      (∀ x ∉ U, x ≠ M 0 → f x = 1) ∧
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f {M 0}ᶜ ∧
      (∀ x, x ≠ M 0 → x ≠ M m → f x ≠ 0) ∧
      IsWeakSolutionAt f (M 0) (ordAt m (M 0)) ∧ IsWeakSolutionAt f (M m) (ordAt m (M m)) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨fun _ => 1, ∅, isOpen_empty, by rw [closure_empty]; exact isCompact_empty,
        ?_, ?_, ?_, ?_, ?_⟩
      · intro x _ _; rfl
      · exact fun x _ => contMDiffAt_const.contMDiffWithinAt
      · intro x _ _; exact one_ne_zero
      · have hval : ordAt 0 (M 0) = 0 := by simp [hordAt_def]
        rw [hval]; exact isWeakSolutionAt_one_zero (M 0)
      · have hval : ordAt 0 (M 0) = 0 := by simp [hordAt_def]
        rw [hval]; exact isWeakSolutionAt_one_zero (M 0)
    | succ m ih =>
      intro hm1
      obtain ⟨f, U, hUopen, hUcompact, hoff, hcm, hne, hwp0, hwpm⟩ := ih (Nat.le_of_succ_le hm1)
      by_cases hdeg : M (m + 1) = M m
      · have heq0 : ordAt (m + 1) (M 0) = ordAt m (M 0) := by
          simp only [hordAt_def]; rw [hdeg]
        have heqm : ordAt (m + 1) (M (m + 1)) = ordAt m (M m) := by
          simp only [hordAt_def]; rw [hdeg]
        refine ⟨f, U, hUopen, hUcompact, ?_, hcm, ?_, ?_, ?_⟩
        · intro x hx1 hx2; exact hoff x hx1 hx2
        · rw [hdeg]; exact hne
        · rw [heq0]; exact hwp0
        · rw [heqm, hdeg]; exact hwpm
      · -- genuine new piece: `M m ≠ M (m + 1)`.
        rename' hdeg => hdeg'
        have hdeg : M (m + 1) ≠ M m := hdeg'
        have hicc1 : C.t m ∈ Set.Icc (C.t m) (C.t (m + 1)) := ⟨le_rfl, C.mono (Nat.le_succ m)⟩
        have hicc2 : C.t (m + 1) ∈ Set.Icc (C.t m) (C.t (m + 1)) :=
          ⟨C.mono (Nat.le_succ m), le_rfl⟩
        have hL := C.maps m (C.t m) hicc1
        have hR := C.maps m (C.t (m + 1)) hicc2
        have hQs : M m ∈ (C.e m).source := hL.1
        have hPs : M (m + 1) ∈ (C.e m).source := hR.1
        have hQball : C.e m (M m) ∈ Metric.ball (C.c m) (C.r m) := hL.2
        have hPball : C.e m (M (m + 1)) ∈ Metric.ball (C.c m) (C.r m) := hR.2
        have hr0 : 0 < C.r m := C.hr m
        have hdQ : dist (C.e m (M m)) (C.c m) < C.r m := hQball
        have hdP : dist (C.e m (M (m + 1))) (C.c m) < C.r m := hPball
        set ρ : ℝ := (max (dist (C.e m (M m)) (C.c m)) (dist (C.e m (M (m + 1))) (C.c m))
          + C.r m) / 2 with hρ_def
        set rIn : ℝ := (ρ + C.r m) / 2 with hrIn_def
        set rOut : ℝ := (rIn + C.r m) / 2 with hrOut_def
        have hρpos : 0 < ρ := by
          have := le_max_left (dist (C.e m (M m)) (C.c m)) (dist (C.e m (M (m+1))) (C.c m))
          have h2 : (0:ℝ) ≤ dist (C.e m (M m)) (C.c m) := dist_nonneg
          rw [hρ_def]; linarith
        have hρlt : ρ < C.r m := by
          rw [hρ_def]
          rcases le_total (dist (C.e m (M m)) (C.c m)) (dist (C.e m (M (m+1))) (C.c m)) with h|h
          · rw [max_eq_right h]; linarith
          · rw [max_eq_left h]; linarith
        have hrInlt : ρ < rIn := by rw [hrIn_def]; linarith
        have hrOutlt : rIn < rOut := by rw [hrOut_def]; linarith
        have hrOutR : rOut < C.r m := by rw [hrOut_def]; linarith
        have haQ : C.e m (M m) - C.c m ∈ Metric.ball (0 : ℂ) ρ := by
          rw [Metric.mem_ball, dist_zero_right]
          rw [dist_eq_norm] at hdQ
          calc ‖C.e m (M m) - C.c m‖ ≤ max (dist (C.e m (M m)) (C.c m))
                (dist (C.e m (M (m+1))) (C.c m)) := by
                  rw [← dist_eq_norm]; exact le_max_left _ _
            _ < ρ := by rw [hρ_def]; linarith
        have haP : C.e m (M (m + 1)) - C.c m ∈ Metric.ball (0 : ℂ) ρ := by
          rw [Metric.mem_ball, dist_zero_right]
          rw [dist_eq_norm] at hdP
          calc ‖C.e m (M (m + 1)) - C.c m‖ ≤ max (dist (C.e m (M m)) (C.c m))
                (dist (C.e m (M (m+1))) (C.c m)) := by
                  rw [← dist_eq_norm]; exact le_max_right _ _
            _ < ρ := by rw [hρ_def]; linarith
        set ψ : ContDiffBump (0 : ℂ) := ⟨rIn, rOut, by linarith, hrOutlt⟩ with hψ_def
        have hballsub : Metric.closedBall (C.c m) ψ.rOut ⊆ (C.e m).target := by
          have h1 : Metric.closedBall (C.c m) rOut ⊆ Metric.ball (C.c m) (C.r m) :=
            Metric.closedBall_subset_ball hrOutR
          exact h1.trans (C.ball_subset m)
        obtain ⟨g, hg, hUgopen, hUgcompact, hM1Ug, hMUg, hg1⟩ :=
          exists_weakSolutionOfPair_chart hdeg (C.he m) hPs hQs hρpos haQ haP ψ hrInlt hballsub
        -- `f`'s and `g`'s local model at ANY point (not just their own special ones).
        have hfAt : ∀ y, IsWeakSolutionAt f y (ordAt m y) := by
          intro y
          by_cases hy0 : y = M 0
          · rw [hy0]; exact hwp0
          · by_cases hym : y = M m
            · rw [hym]; exact hwpm
            · have hzero : ordAt m y = 0 := by
                simp only [hordAt_def]; rw [if_neg hy0, if_neg hym]
              rw [hzero]; exact isWeakSolutionAt_zero_of_ne hcm hne hy0 hym
        have hgAt : ∀ y, IsWeakSolutionAt g y
            ((if y = M (m + 1) then (1 : ℤ) else 0) + (if y = M m then (-1 : ℤ) else 0)) := by
          intro y
          by_cases hy1 : y = M (m + 1)
          · have hval : (if y = M (m + 1) then (1 : ℤ) else 0) + (if y = M m then (-1 : ℤ) else 0)
                = 1 := by
              rw [if_pos hy1, if_neg (hy1 ▸ hdeg : y ≠ M m)]
            rw [hval, hy1]; exact hg.weakAt_P
          · by_cases hym : y = M m
            · have hval : (if y = M (m + 1) then (1 : ℤ) else 0)
                  + (if y = M m then (-1 : ℤ) else 0) = -1 := by
                rw [if_neg hy1, if_pos hym]
              rw [hval, hym]; exact hg.weakAt_Q
            · have hval : (if y = M (m + 1) then (1 : ℤ) else 0)
                  + (if y = M m then (-1 : ℤ) else 0) = 0 := by
                rw [if_neg hy1, if_neg hym]
              rw [hval]
              exact isWeakSolutionAt_zero_of_ne hg.contMDiffOn
                (fun z h1 h2 => hg.ne_zero_off z h2 h1) hym hy1
        have hsum : ∀ y, ordAt m y +
            ((if y = M (m + 1) then (1 : ℤ) else 0) + (if y = M m then (-1 : ℤ) else 0))
              = ordAt (m + 1) y := by
          intro y
          simp only [hordAt_def]
          by_cases h0 : y = M 0 <;> by_cases h1 : y = M (m + 1) <;> by_cases hmm : y = M m <;>
            simp [h0, h1, hmm]
        obtain ⟨hMm, hMm_ord0, hMm_eq0⟩ := (hfAt (M m)).mul (hgAt (M m))
        obtain ⟨hMm1, hMm1_ord0, hMm1_eq0⟩ := (hfAt (M (m + 1))).mul (hgAt (M (m + 1)))
        have hMm_ord : IsWeakSolutionAt hMm (M m) (ordAt (m + 1) (M m)) := hsum (M m) ▸ hMm_ord0
        have hMm1_ord : IsWeakSolutionAt hMm1 (M (m + 1)) (ordAt (m + 1) (M (m + 1))) :=
          hsum (M (m + 1)) ▸ hMm1_ord0
        sorry
  obtain ⟨f, U, hUopen, hUcompact, hoff, hcm, hne, hwQ, hwP⟩ := main C.n le_rfl
  sorry

end RS.AbelWeak

end
