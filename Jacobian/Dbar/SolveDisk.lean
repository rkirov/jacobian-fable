import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Jacobian.Dbar.CauchyKernel

/-!
# Forster 13.2: Dolbeault's lemma on an open disk (`Jacobian/Dbar/SolveDisk.lean`)

Unit: dbar-solvability (`docs/design/dbar-solvability.md` §4.3, §6). Mathlib-only planar file.

The main theorem `exists_dbar_solution_ball` solves `∂̄u = g` on a finite open disk for `g`
smooth there, by an exhaustion + correction sequence: solve `∂̄fₙ = g` on shrinking closed
sub-balls via `cauchyTransform` of a cutoff of `g` (13.1), then correct each `fₙ` by a partial
sum of the power series of the (holomorphic) difference `f_{n+1} - fₙ`, chosen small enough
that the corrected sequence converges locally uniformly to a solution on the whole disk.
-/

open MeasureTheory Metric Set Complex Filter Topology
open scoped Convolution ContDiff

noncomputable section

namespace RS

variable (g : ℂ → ℂ) (c : ℂ) (R : ℝ)

/-- Extension by zero of a bump-cutoff of a function smooth on an open set: the cutoff
`s.indicator (φ • g)` is smooth everywhere, provided `φ`'s (closed) support stays inside `s`. -/
theorem contDiff_indicator_bump_smul {s : Set ℂ} (φ : ContDiffBump c) (hs : IsOpen s)
    (hg : ContDiffOn ℝ ∞ g s) (hsub : closedBall c φ.rOut ⊆ s) :
    ContDiff ℝ ∞ (s.indicator fun z => φ z • g z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ s
  · have heq : s.indicator (fun z => φ z • g z) =ᶠ[𝓝 z] (fun z => φ z • g z) := by
      filter_upwards [hs.mem_nhds hz] with w hw using Set.indicator_of_mem hw _
    exact ((φ.contDiff.contDiffAt).smul (hg.contDiffAt (hs.mem_nhds hz))).congr_of_eventuallyEq heq
  · have hzclosed : z ∉ closedBall c φ.rOut := fun h => hz (hsub h)
    rw [mem_closedBall] at hzclosed
    push_neg at hzclosed
    have hzero : ∀ᶠ w in 𝓝 z, φ w = 0 := by
      have hop : IsOpen {w : ℂ | φ.rOut < dist w c} :=
        isOpen_lt continuous_const (continuous_id.dist continuous_const)
      filter_upwards [hop.mem_nhds hzclosed] with w hw using φ.zero_of_le_dist hw.le
    have heq : s.indicator (fun z => φ z • g z) =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
      filter_upwards [hzero] with w hw
      by_cases hw' : w ∈ s
      · rw [Set.indicator_of_mem hw', hw, zero_smul]
      · exact Set.indicator_of_notMem hw' _
    exact contDiffAt_const.congr_of_eventuallyEq heq

theorem hasCompactSupport_indicator_bump_smul {s : Set ℂ} (φ : ContDiffBump c) :
    HasCompactSupport (s.indicator fun z => φ z • g z) := by
  apply HasCompactSupport.intro (isCompact_closedBall c φ.rOut)
  intro w hw
  rw [mem_closedBall] at hw
  push_neg at hw
  by_cases hws : w ∈ s
  · rw [Set.indicator_of_mem hws, φ.zero_of_le_dist hw.le, zero_smul]
  · exact Set.indicator_of_notMem hws _

theorem eqOn_indicator_bump_smul {s : Set ℂ} (φ : ContDiffBump c) (hsub : closedBall c φ.rOut ⊆ s) :
    Set.EqOn (s.indicator fun z => φ z • g z) (fun z => φ z • g z) (closedBall c φ.rIn) := by
  intro z hz
  rw [Set.indicator_of_mem (hsub (closedBall_subset_closedBall φ.rIn_lt_rOut.le hz))]

/-! ### The exhaustion radii `ρ n = R - R/(n+2)` -/

private def solveRho (R : ℝ) (n : ℕ) : ℝ := R - R / (n + 2)

private theorem solveRho_pos (hR : 0 < R) (n : ℕ) : 0 < solveRho R n := by
  have hn2 : (1 : ℝ) < (n : ℝ) + 2 := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have := div_lt_self hR hn2
  simp only [solveRho]; linarith

private theorem solveRho_lt_R (hR : 0 < R) (n : ℕ) : solveRho R n < R := by
  have hn2 : (0:ℝ) < (n:ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have : 0 < R / (n + 2) := div_pos hR hn2
  simp only [solveRho]; linarith

private theorem solveRho_lt_succ (hR : 0 < R) (n : ℕ) :
    solveRho R n < solveRho R (n + 1) := by
  have hn2 : (0:ℝ) < (n:ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hn3 : (n:ℝ) + 2 < (n:ℝ) + 1 + 2 := by linarith
  have := div_lt_div_of_pos_left hR hn2 hn3
  simp only [solveRho]
  push_cast
  linarith

private theorem solveRho_mono (hR : 0 < R) : Monotone (solveRho R) := by
  apply monotone_nat_of_le_succ
  intro n
  exact (solveRho_lt_succ R hR n).le

private theorem exists_solveRho_gt (hR : 0 < R) {x : ℝ} (hx : x < R) :
    ∃ N, x < solveRho R N := by
  have hRx : 0 < R - x := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (R / (R - x))
  refine ⟨N, ?_⟩
  have hN2 : (0:ℝ) < (N:ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  rw [div_lt_iff₀ hRx] at hN
  have key : R / ((N:ℝ) + 2) < R - x := by
    rw [div_lt_iff₀ hN2]
    nlinarith
  simp only [solveRho]
  linarith

/-! ### The cutoff bumps and cutoff functions -/

private def solvePhi (hR : 0 < R) (n : ℕ) : ContDiffBump c where
  rIn := solveRho R (n + 1)
  rOut := (solveRho R (n + 1) + solveRho R (n + 2)) / 2
  rIn_pos := solveRho_pos R hR (n + 1)
  rIn_lt_rOut := by have := solveRho_lt_succ R hR (n + 1); linarith

private theorem solvePhi_rOut_lt (hR : 0 < R) (n : ℕ) :
    (solvePhi c R hR n).rOut < solveRho R (n + 2) := by
  have := solveRho_lt_succ R hR (n + 1)
  simp only [solvePhi]
  linarith

private theorem solvePhi_sub (hR : 0 < R) (n : ℕ) :
    closedBall c (solvePhi c R hR n).rOut ⊆ ball c R := by
  apply closedBall_subset_ball
  have h1 := solvePhi_rOut_lt c R hR n
  have h2 := solveRho_lt_R R hR (n + 2)
  linarith

private def solveGcut (hR : 0 < R) (n : ℕ) : ℂ → ℂ :=
  (ball c R).indicator fun z => solvePhi c R hR n z • g z

private theorem solveGcut_cd (hR : 0 < R) (hg : ContDiffOn ℝ ∞ g (ball c R)) (n : ℕ) :
    ContDiff ℝ ∞ (solveGcut g c R hR n) :=
  contDiff_indicator_bump_smul g c (solvePhi c R hR n) isOpen_ball hg (solvePhi_sub c R hR n)

private theorem solveGcut_cs (hR : 0 < R) (n : ℕ) :
    HasCompactSupport (solveGcut g c R hR n) :=
  hasCompactSupport_indicator_bump_smul g c (solvePhi c R hR n)

private theorem solveGcut_eq (hR : 0 < R) (n : ℕ) :
    Set.EqOn (solveGcut g c R hR n) g (closedBall c (solveRho R (n + 1))) := by
  intro z hz
  have h1 := eqOn_indicator_bump_smul g c (solvePhi c R hR n) (solvePhi_sub c R hR n) hz
  rw [solveGcut, h1]
  simp only [(solvePhi c R hR n).one_of_mem_closedBall hz, one_smul]

/-! ### The raw (uncorrected) solutions on shrinking sub-balls -/

private def solveF (hR : 0 < R) (hg : ContDiffOn ℝ ∞ g (ball c R)) (n : ℕ) : ℂ → ℂ :=
  cauchyTransform (solveGcut g c R hR n)

private theorem solveF_cd (hR : 0 < R) (hg : ContDiffOn ℝ ∞ g (ball c R)) (n : ℕ) :
    ContDiff ℝ ∞ (solveF g c R hR hg n) :=
  contDiff_cauchyTransform (solveGcut g c R hR n) (solveGcut_cd g c R hR hg n)
    (solveGcut_cs g c R hR n)

private theorem solveF_dbar_eq (hR : 0 < R) (hg : ContDiffOn ℝ ∞ g (ball c R)) (n : ℕ) :
    Set.EqOn (wirtingerDbar (solveF g c R hR hg n)) g (closedBall c (solveRho R (n + 1))) := by
  intro w hw
  rw [solveF, wirtingerDbar_cauchyTransform_eq (solveGcut g c R hR n) (solveGcut_cd g c R hR hg n)
    (solveGcut_cs g c R hR n) w]
  exact solveGcut_eq g c R hR n hw

/-! ### The corrected sequence: a Nat.rec into a Σ-type carrying invariants (i), (ii); the
correction bound (iii) is proved once, as a property of the step function itself. -/

private def SolveState (hR : 0 < R) (n : ℕ) : Type :=
  {F : ℂ → ℂ // ContDiff ℝ ∞ F ∧ Set.EqOn (wirtingerDbar F) g (closedBall c (solveRho R (n + 1)))}

private def solveState0 (hR : 0 < R) (hg : ContDiffOn ℝ ∞ g (ball c R)) : SolveState g c R hR 0 :=
  ⟨solveF g c R hR hg 0, solveF_cd g c R hR hg 0, solveF_dbar_eq g c R hR hg 0⟩

private theorem partialSum_eq_poly (p : FormalMultilinearSeries ℂ ℂ ℂ) (m : ℕ) (x : ℂ) :
    p.partialSum m x = ∑ k ∈ Finset.range m, x ^ k * p.coeff k := by
  unfold FormalMultilinearSeries.partialSum
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [p.apply_eq_pow_smul_coeff, smul_eq_mul]

private theorem differentiable_partialSum (p : FormalMultilinearSeries ℂ ℂ ℂ) (m : ℕ) :
    Differentiable ℂ (fun x => p.partialSum m x) := by
  have heq : (fun x => p.partialSum m x) = fun x => ∑ k ∈ Finset.range m, x ^ k * p.coeff k :=
    funext (partialSum_eq_poly p m)
  rw [heq]
  apply Differentiable.sum
  intro k _
  exact (differentiable_pow k).mul (differentiable_const (p.coeff k))

/-- The recursive step: given a solution `Fn` valid up to `ρ (n+1)`, produce a corrected solution
valid up to `ρ (n+2)`, within `(1/2)^(n+1)` of `Fn` on the smaller closed ball `closedBall c (ρ n)`
(design §6 steps 1–3). -/
private def solveStepData (hR : 0 < R) (hg : ContDiffOn ℝ ∞ g (ball c R)) (n : ℕ)
    (Dn : SolveState g c R hR n) :
    {F : ℂ → ℂ // ContDiff ℝ ∞ F ∧
        Set.EqOn (wirtingerDbar F) g (closedBall c (solveRho R (n + 2))) ∧
        ∀ w ∈ closedBall c (solveRho R n), ‖F w - Dn.1 w‖ ≤ (1 / 2 : ℝ) ^ (n + 1)} := by
  classical
  obtain ⟨Fn, hFn_cd, hFn_dbar⟩ := Dn
  have hfn1_cd : ContDiff ℝ ∞ (solveF g c R hR hg (n + 1)) := solveF_cd g c R hR hg (n + 1)
  have hfn1_dbar : Set.EqOn (wirtingerDbar (solveF g c R hR hg (n + 1))) g
      (closedBall c (solveRho R (n + 2))) := solveF_dbar_eq g c R hR hg (n + 1)
  set fn1 := solveF g c R hR hg (n + 1) with hfn1_def
  -- `d := f_{n+1} - F_n` is holomorphic on the open ball `ball c (ρ (n+1))`
  have hd_diff : ∀ w, DifferentiableAt ℝ (fn1 - Fn) w := fun w =>
    (hfn1_cd.differentiable (by norm_num) w).sub (hFn_cd.differentiable (by norm_num) w)
  have hd_dbar0 : ∀ w ∈ ball c (solveRho R (n + 1)), wirtingerDbar (fn1 - Fn) w = 0 := by
    intro w hw
    have hw1 : w ∈ closedBall c (solveRho R (n + 2)) :=
      closedBall_subset_closedBall (solveRho_lt_succ R hR (n + 1)).le (ball_subset_closedBall hw)
    have hw2 : w ∈ closedBall c (solveRho R (n + 1)) := ball_subset_closedBall hw
    rw [wirtingerDbar_sub fn1 Fn w (hfn1_cd.differentiable (by norm_num) w)
      (hFn_cd.differentiable (by norm_num) w), hfn1_dbar hw1, hFn_dbar hw2, sub_self]
  have hd_holo : DifferentiableOn ℂ (fn1 - Fn) (ball c (solveRho R (n + 1))) :=
    differentiableOn_of_wirtingerDbar_eq_zero (fn1 - Fn) isOpen_ball (fun w _ => hd_diff w)
      hd_dbar0
  -- three nested radii strictly between `ρ n` and `ρ (n+1)`
  set ρn : ℝ := solveRho R n with hρn_def
  set ρn1 : ℝ := solveRho R (n + 1) with hρn1_def
  have hρn_lt : ρn < ρn1 := solveRho_lt_succ R hR n
  have hρn_pos : 0 < ρn := solveRho_pos R hR n
  set ρmid : ℝ := (ρn + ρn1) / 2 with hρmid_def
  set ρaux : ℝ := (ρn + ρmid) / 2 with hρaux_def
  have hρn_lt_aux : ρn < ρaux := by rw [hρaux_def, hρmid_def]; linarith
  have hρaux_lt_mid : ρaux < ρmid := by rw [hρaux_def, hρmid_def]; linarith
  have hρmid_lt_n1 : ρmid < ρn1 := by rw [hρmid_def]; linarith
  have hρmid_pos : 0 < ρmid := by rw [hρmid_def]; linarith
  have hρaux_pos : 0 < ρaux := by rw [hρaux_def]; linarith
  -- power series of `d` on the closed ball of radius `ρmid`
  have hd_holo_mid : DifferentiableOn ℂ (fn1 - Fn) (closedBall c ρmid) :=
    hd_holo.mono (closedBall_subset_ball hρmid_lt_n1)
  set nnρmid : ℝ≥0 := ⟨ρmid, hρmid_pos.le⟩ with hnnρmid_def
  have hnnρmid_pos : 0 < nnρmid := hρmid_pos
  have hps : HasFPowerSeriesOnBall (fn1 - Fn) (cauchyPowerSeries (fn1 - Fn) c nnρmid) c nnρmid :=
    hd_holo_mid.hasFPowerSeriesOnBall hnnρmid_pos
  set p := cauchyPowerSeries (fn1 - Fn) c nnρmid with hp_def
  set nnρaux : ℝ≥0 := ⟨ρaux, hρaux_pos.le⟩ with hnnρaux_def
  have hnnρaux_lt : (nnρaux : ENNReal) < nnρmid := by
    rw [ENNReal.coe_lt_coe]
    exact_mod_cast hρaux_lt_mid
  have htendsto : TendstoUniformlyOn (fun k y => p.partialSum k (y - c)) (fn1 - Fn) atTop
      (ball c ρaux) := hps.tendstoUniformlyOn' hnnρaux_lt
  -- extract a specific degree `m` with the required uniform bound
  have hbound_ev : ∀ᶠ k in atTop, ∀ y ∈ ball c ρaux, dist ((fn1 - Fn) y) (p.partialSum k (y - c)) <
      (1 / 2 : ℝ) ^ (n + 1) :=
    (tendstoUniformlyOn_iff.1 htendsto) ((1 / 2 : ℝ) ^ (n + 1)) (by positivity)
  obtain ⟨m, hm⟩ := eventually_atTop.1 hbound_ev
  set Pm : ℂ → ℂ := fun w => p.partialSum m (w - c) with hPm_def
  have hPm_diff : Differentiable ℂ Pm := by
    have := differentiable_partialSum p m
    exact this.comp (differentiable_id.sub_const c)
  have hPm_cd : ContDiff ℝ ∞ Pm := by
    have h1 : AnalyticOnNhd ℂ Pm Set.univ := hPm_diff.analyticOnNhd isOpen_univ
    have h2 : ∀ w, AnalyticAt ℂ Pm w := fun w => h1 w (mem_univ w)
    exact contDiff_iff_contDiffAt.2 fun w => ((h2 w).restrictScalars (𝕜 := ℝ)).contDiffAt
  have hPm_dbar0 : ∀ w, wirtingerDbar Pm w = 0 := fun w =>
    wirtingerDbar_eq_zero_of_differentiableAt Pm w (hPm_diff w)
  refine ⟨fn1 - Pm, hfn1_cd.sub hPm_cd, ?_, ?_⟩
  · intro w hw
    rw [wirtingerDbar_sub fn1 Pm w (hfn1_cd.differentiable (by norm_num) w) (hPm_diff w).differentiableAt,
      hfn1_dbar hw, hPm_dbar0, sub_zero]
  · intro w hw
    have hwaux : w ∈ ball c ρaux := closedBall_subset_ball hρn_lt_aux hw
    have := hm m le_rfl w hwaux
    rw [dist_eq_norm] at this
    have heq : (fn1 - Pm) w - Fn w = (fn1 - Fn) w - Pm w := by simp [Pi.sub_apply]; ring
    rw [heq]
    exact this.le

/-- Forster 13.2: Dolbeault's lemma on a finite open disk. -/
theorem exists_dbar_solution_ball (hR : 0 < R) (hg : ContDiffOn ℝ ∞ g (ball c R)) :
    ∃ u : ℂ → ℂ, ContDiffOn ℝ ∞ u (ball c R) ∧
      ∀ z ∈ ball c R, wirtingerDbar u z = g z := by
  sorry

end RS
