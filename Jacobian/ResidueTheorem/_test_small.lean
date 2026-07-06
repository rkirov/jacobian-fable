import Jacobian.ResidueCalculus.IntegralBridge
import Mathlib.MeasureTheory.Integral.CircleAverage

open Filter Topology Metric Function Real Complex MeasureTheory

noncomputable section

theorem circleIntegral_inv_eq_neg (R_mid : ℂ → ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∮ w in C(0, ρ), -(w ^ 2)⁻¹ * R_mid w⁻¹) = -(∮ z in C(0, ρ⁻¹), R_mid z) := by
  have hρne : ρ ≠ 0 := hρ.ne'
  have hshift : (∫ x : ℝ in (0:ℝ)..2 * π,
        deriv (circleMap 0 ρ⁻¹) (-x) • R_mid (circleMap 0 ρ⁻¹ (-x)))
      = ∫ θ : ℝ in (0:ℝ)..2 * π, deriv (circleMap 0 ρ⁻¹) θ • R_mid (circleMap 0 ρ⁻¹ θ) := by
    rw [intervalIntegral.integral_comp_neg
      (fun θ => deriv (circleMap 0 ρ⁻¹) θ • R_mid (circleMap 0 ρ⁻¹ θ))]
    have hper : Function.Periodic
        (fun θ : ℝ => deriv (circleMap 0 ρ⁻¹) θ • R_mid (circleMap 0 ρ⁻¹ θ)) (2 * π) := by
      intro θ
      simp only [deriv_circleMap]
      rw [periodic_circleMap 0 ρ⁻¹ θ]
    simpa using hper.intervalIntegral_add_eq (-(2 * π)) 0
  show (∫ θ : ℝ in (0:ℝ)..2 * π,
      deriv (circleMap 0 ρ) θ • (-(circleMap 0 ρ θ ^ 2)⁻¹ * R_mid (circleMap 0 ρ θ)⁻¹))
    = -(∫ θ : ℝ in (0:ℝ)..2 * π, deriv (circleMap 0 ρ⁻¹) θ • R_mid (circleMap 0 ρ⁻¹ θ))
  rw [← hshift]
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [smul_eq_mul, deriv_circleMap]
  rw [circleMap_zero_inv]
  have hcnz : circleMap 0 ρ θ ≠ 0 := circleMap_ne_center hρne
  rw [show circleMap 0 ρ θ * I * (-(circleMap 0 ρ θ ^ 2)⁻¹ * R_mid (circleMap 0 ρ⁻¹ (-θ)))
      = -(circleMap 0 ρ⁻¹ (-θ) * I) * R_mid (circleMap 0 ρ⁻¹ (-θ)) by
    rw [← circleMap_zero_inv]; field_simp]
  ring

/-- The residue "at infinity" of an entire function's `invChart`-transported reading always
vanishes: no Liouville-growth-polynomial machinery needed, just Cauchy's theorem (`R_mid` entire
⟹ every circle integral of it is `0`) transported through the `z ↦ z⁻¹` reindexing above. -/
theorem resAt_neg_sq_inv_mul_comp_inv_eq_zero {R_mid : ℂ → ℂ} (hdiff : Differentiable ℂ R_mid)
    (hg : MeromorphicAt (fun w => -(w ^ 2)⁻¹ * R_mid w⁻¹) 0) :
    RS.resAt (fun w => -(w ^ 2)⁻¹ * R_mid w⁻¹) 0 = 0 := by
  set g : ℂ → ℂ := fun w => -(w ^ 2)⁻¹ * R_mid w⁻¹ with hg_def
  have hgdiff : ∀ w : ℂ, w ∈ Metric.closedBall (0:ℂ) 1 \ {0} → DifferentiableAt ℂ g w := by
    rintro w ⟨-, hw0⟩
    have hwne : w ≠ 0 := hw0
    have h1 : DifferentiableAt ℂ (fun v : ℂ => v⁻¹) w := differentiableAt_inv hwne
    have h2 : DifferentiableAt ℂ (fun v : ℂ => R_mid v⁻¹) w := (hdiff (w⁻¹)).comp w h1
    have h3 : DifferentiableAt ℂ (fun v : ℂ => -(v ^ 2)⁻¹) w := by
      have hp : DifferentiableAt ℂ (fun v : ℂ => v ^ 2) w := by fun_prop
      exact (hp.inv (pow_ne_zero 2 hwne)).neg
    exact h3.mul h2
  have hkey := RS.circleIntegral_eq_two_pi_I_mul_resAt (f := g) (z₀ := 0) one_pos hg hgdiff
  have hzero : (∮ w in C(0, (1:ℝ)), g w) = 0 := by
    rw [hg_def, circleIntegral_inv_eq_neg R_mid one_pos]
    have hRanalytic : AnalyticAt ℂ R_mid 0 := hdiff.analyticAt 0
    have hRres : RS.resAt R_mid 0 = 0 := RS.resAt_of_analyticAt hRanalytic
    have hRint := RS.circleIntegral_eq_two_pi_I_mul_resAt (f := R_mid) (z₀ := 0)
      (show (0:ℝ) < 1⁻¹ by norm_num) hRanalytic.meromorphicAt
      (fun z _ => hdiff z)
    rw [hRres, mul_zero] at hRint
    rw [hRint]
    ring
  rw [hzero] at hkey
  have h2pi : (2 * (π:ℂ) * I) ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero two_ne_zero
    · exact_mod_cast Real.pi_ne_zero
    · exact Complex.I_ne_zero
  exact (mul_eq_zero.mp hkey.symm).resolve_left h2pi

end
