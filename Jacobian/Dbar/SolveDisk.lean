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

/-- Forster 13.2: Dolbeault's lemma on a finite open disk. -/
theorem exists_dbar_solution_ball (hR : 0 < R) (hg : ContDiffOn ℝ ∞ g (ball c R)) :
    ∃ u : ℂ → ℂ, ContDiffOn ℝ ∞ u (ball c R) ∧
      ∀ z ∈ ball c R, wirtingerDbar u z = g z := by
  sorry

end RS
