import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Jacobian.Dbar.Wirtinger

/-!
# The Cauchy kernel, the Cauchy transform, and Cauchy–Pompeiu (Forster 13.1)

Unit: dbar-solvability (`docs/design/dbar-solvability.md` §4.2, §5). Mathlib-only planar file.

`cauchyKernel w := (π w)⁻¹`; `cauchyTransform g := cauchyKernel ⋆[mul ℝ ℂ] g`. The pointwise
identity `∂̄(cauchyKernel ⋆ g) = g` for compactly supported `C¹` `g` (`cauchyPompeiu`) is proved by
polar coordinates + 1-D FTC in the radial and angular directions (design §5): the convolution
derivative package handles "differentiate under the integral", and the polar substitution makes
the kernel singularity cancel exactly.
-/

open MeasureTheory Metric Set Complex
open scoped Convolution ContDiff

noncomputable section

namespace RS

/-- The Cauchy kernel `1/(π w)`. -/
def cauchyKernel : ℂ → ℂ := fun w => (Real.pi * w)⁻¹

theorem measurable_cauchyKernel : Measurable cauchyKernel :=
  (measurable_id.const_mul _).inv

theorem aestronglyMeasurable_cauchyKernel : AEStronglyMeasurable cauchyKernel volume :=
  measurable_cauchyKernel.aestronglyMeasurable

theorem norm_cauchyKernel (w : ℂ) : ‖cauchyKernel w‖ = (Real.pi * ‖w‖)⁻¹ := by
  simp [cauchyKernel, norm_inv, Real.norm_of_nonneg Real.pi_pos.le]

/-- Step 1 of the design: `cauchyKernel` is integrable on every ball centred at `0`. -/
theorem integrableOn_cauchyKernel_ball (ρ : ℝ) :
    IntegrableOn cauchyKernel (ball (0 : ℂ) ρ) volume := by
  by_cases hρ0 : ρ ≤ 0
  · simp [ball_eq_empty.2 hρ0]
  push_neg at hρ0
  have hρ : 0 < ρ := hρ0
  refine ⟨aestronglyMeasurable_cauchyKernel.restrict, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hind : (∫⁻ w in ball (0 : ℂ) ρ, ‖cauchyKernel w‖ₑ ∂volume) =
      ∫⁻ w, (ball (0 : ℂ) ρ).indicator (fun w => ‖cauchyKernel w‖ₑ) w ∂volume := by
    rw [lintegral_indicator measurableSet_ball]
  rw [hind, ← Complex.lintegral_comp_polarCoord_symm]
  -- pointwise bound, valid on the whole plane (both sides are `0` off the relevant boxes)
  have hbound : ∀ p : ℝ × ℝ,
      Complex.polarCoord.target.indicator
          (fun p => ENNReal.ofReal p.1 • (ball (0 : ℂ) ρ).indicator (fun w => ‖cauchyKernel w‖ₑ)
              (Complex.polarCoord.symm p)) p ≤
        (Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
          (fun _ => ENNReal.ofReal (Real.pi⁻¹)) p := by
    intro p
    by_cases hp : p ∈ Complex.polarCoord.target
    · rw [Set.indicator_of_mem hp]
      obtain ⟨r, θ⟩ := p
      have hr : 0 < r := hp.1
      by_cases hrρ : r < ρ
      · have hmem1 : (r, θ) ∈ Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi := ⟨⟨hr, hrρ⟩, hp.2⟩
        have hnorm : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
          rw [Complex.norm_polarCoord_symm]; exact abs_of_pos hr
        have hmem2 : Complex.polarCoord.symm (r, θ) ∈ ball (0 : ℂ) ρ := by
          rw [mem_ball_zero_iff, hnorm]; exact hrρ
        rw [Set.indicator_of_mem hmem1, Set.indicator_of_mem hmem2, ← ofReal_norm_eq_enorm,
          norm_cauchyKernel, hnorm, smul_eq_mul, ← ENNReal.ofReal_mul hr.le]
        have heq : r * (Real.pi * r)⁻¹ = Real.pi⁻¹ := by field_simp
        rw [heq]
      · push_neg at hrρ
        have hnotmem_ball : Complex.polarCoord.symm (r, θ) ∉ ball (0 : ℂ) ρ := by
          rw [mem_ball_zero_iff, Complex.norm_polarCoord_symm, abs_of_pos hr]
          exact not_lt.2 hrρ
        rw [Set.indicator_of_notMem hnotmem_ball, smul_zero]
        exact (bot_le : (0 : ENNReal) ≤ _)
    · rw [Set.indicator_of_notMem hp]
      exact (bot_le : (0 : ENNReal) ≤ _)
  calc ∫⁻ p in Complex.polarCoord.target,
      ENNReal.ofReal p.1 • (ball (0 : ℂ) ρ).indicator (fun w => ‖cauchyKernel w‖ₑ)
          (Complex.polarCoord.symm p)
      = ∫⁻ p, Complex.polarCoord.target.indicator
          (fun p => ENNReal.ofReal p.1 • (ball (0 : ℂ) ρ).indicator (fun w => ‖cauchyKernel w‖ₑ)
              (Complex.polarCoord.symm p)) p :=
        (lintegral_indicator Complex.polarCoord.open_target.measurableSet _).symm
    _ ≤ ∫⁻ p, (Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
          (fun _ => ENNReal.ofReal (Real.pi⁻¹)) p := lintegral_mono hbound
    _ = ∫⁻ p in Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi, ENNReal.ofReal (Real.pi⁻¹) :=
        lintegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo) _
    _ < ⊤ := by
        rw [MeasureTheory.setLIntegral_const,
          show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
          Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

theorem locallyIntegrable_cauchyKernel : LocallyIntegrable cauchyKernel volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨ρ, hρ⟩ := hK.isBounded.subset_ball (0 : ℂ)
  exact (integrableOn_cauchyKernel_ball ρ).mono_set hρ

/-! ## The Cauchy transform and its derivative (design §5, step 2) -/

/-- The Cauchy transform `cauchyKernel ⋆ g`. -/
noncomputable def cauchyTransform (g : ℂ → ℂ) : ℂ → ℂ :=
  cauchyKernel ⋆[ContinuousLinearMap.mul ℝ ℂ] g

theorem contDiff_cauchyTransform (hg : ContDiff ℝ ∞ g) (hcs : HasCompactSupport g) :
    ContDiff ℝ ∞ (cauchyTransform g) :=
  hcs.contDiff_convolution_right _ locallyIntegrable_cauchyKernel hg

/-- Step 2: differentiation under the integral, via the convolution-derivative package. -/
theorem wirtingerDbar_cauchyTransform (hg : ContDiff ℝ ∞ g) (hcs : HasCompactSupport g) (z : ℂ) :
    wirtingerDbar (cauchyTransform g) z = ∫ w : ℂ, cauchyKernel w * wirtingerDbar g (z - w) := by
  have hg1 : ContDiff ℝ (1 : ℕ∞) g := hg.of_le (by norm_num)
  have hfd : HasFDerivAt (cauchyTransform g)
      ((cauchyKernel ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompR ℂ] fderiv ℝ g) z) z :=
    hcs.hasFDerivAt_convolution_right _ locallyIntegrable_cauchyKernel hg1 z
  have hcompv : ∀ v : ℂ,
      (cauchyKernel ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompR ℂ] fderiv ℝ g) z v =
        ∫ w, cauchyKernel w * fderiv ℝ g (z - w) v := by
    intro v
    rw [convolution_precompR_apply _ locallyIntegrable_cauchyKernel (hcs.fderiv ℝ)
      (hg1.continuous_fderiv (by norm_num))]
    simp [convolution_def]
  have hInt1 : Integrable (fun w => cauchyKernel w * fderiv ℝ g (z - w) 1) :=
    (hcs.fderiv_apply ℝ (1 : ℂ)).convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ)
      locallyIntegrable_cauchyKernel
      ((hg1.continuous_fderiv (by norm_num)).clm_apply continuous_const) z
  have hIntI : Integrable (fun w => cauchyKernel w * fderiv ℝ g (z - w) Complex.I) :=
    (hcs.fderiv_apply ℝ Complex.I).convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ)
      locallyIntegrable_cauchyKernel
      ((hg1.continuous_fderiv (by norm_num)).clm_apply continuous_const) z
  have key : ∀ w, cauchyKernel w * wirtingerDbar g (z - w) =
      (cauchyKernel w * fderiv ℝ g (z - w) 1
        + Complex.I * (cauchyKernel w * fderiv ℝ g (z - w) Complex.I)) / 2 := by
    intro w; simp only [wirtingerDbar]; ring
  rw [wirtingerDbar, hfd.fderiv, hcompv 1, hcompv Complex.I]
  simp_rw [key]
  rw [integral_div, integral_add hInt1 (hIntI.const_mul _), integral_const_mul]

/-! ## Cauchy–Pompeiu (design §5, steps 0, 1, 3–8) -/

/-- `circleMap` computes `Complex.polarCoord.symm`. -/
private theorem polarCoord_symm_eq_circleMap (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I, Complex.ofReal_cos,
    Complex.ofReal_sin]

private theorem hasDerivAt_circleMap_r (c : ℂ) (θ r : ℝ) :
    HasDerivAt (fun r : ℝ => circleMap c r θ) (Complex.exp (θ * Complex.I)) r := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := r)).mul_const
    (Complex.exp (θ * Complex.I))).const_add c
  simpa [circleMap] using h

/-- Forster 13.1 / Cauchy–Pompeiu, proved by the polar-FTC computation of design §5. -/
theorem cauchyPompeiu (hg : ContDiff ℝ 1 g) (hcs : HasCompactSupport g) (z : ℂ) :
    ∫ w : ℂ, cauchyKernel w * wirtingerDbar g (z - w) = g z := by
  have hgdiff : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hfc : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  set h : ℂ → ℂ := wirtingerDbar g with hh_def
  have hhc : Continuous h := by
    have h1 : Continuous (fun w => fderiv ℝ g w 1) := hfc.clm_apply continuous_const
    have h2 : Continuous (fun w => fderiv ℝ g w Complex.I) := hfc.clm_apply continuous_const
    simpa [hh_def, wirtingerDbar] using (h1.add (continuous_const.mul h2)).div_const 2
  -- R0, R'
  obtain ⟨R0', hR0'⟩ := hcs.isBounded.subset_closedBall (0 : ℂ)
  set R0 : ℝ := max R0' 0 with hR0_def
  have hR0nonneg : 0 ≤ R0 := le_max_right _ _
  have hR0 : tsupport g ⊆ Metric.closedBall (0 : ℂ) R0 :=
    hR0'.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  set R' : ℝ := ‖z‖ + R0 + 1 with hR'_def
  have hR'pos : 0 < R' := by positivity
  have hnotmem_tsupport : ∀ r θ : ℝ, R' ≤ r → z - circleMap 0 r θ ∉ tsupport g := by
    intro r θ hr hmem
    have h1 := hR0 hmem
    rw [mem_closedBall_zero_iff] at h1
    have h2 : ‖circleMap 0 r θ‖ = r := by
      rw [circleMap, zero_add, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_of_nonneg (hR'pos.le.trans hr)]
    have h3 : ‖circleMap 0 r θ‖ - ‖z‖ ≤ ‖z - circleMap 0 r θ‖ := by
      have h4 := norm_sub_norm_le (circleMap 0 r θ) z
      rwa [norm_sub_rev] at h4
    rw [h2] at h3
    linarith
  have hvanish : ∀ r θ : ℝ, R' ≤ r → g (z - circleMap 0 r θ) = 0 := fun r θ hr =>
    image_eq_zero_of_notMem_tsupport (hnotmem_tsupport r θ hr)
  have hvanish_h_gen : ∀ x : ℂ, x ∉ tsupport g → h x = 0 := by
    intro x hx
    have hnhds : g =ᶠ[nhds x] (fun _ => (0 : ℂ)) := by
      filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hx] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    rw [hh_def, wirtingerDbar_congr_nhds g (fun _ => (0:ℂ)) x hnhds, wirtingerDbar_const]
  have hvanish_h : ∀ r θ : ℝ, R' ≤ r → h (z - circleMap 0 r θ) = 0 := fun r θ hr =>
    hvanish_h_gen _ (hnotmem_tsupport r θ hr)
  -- the derivative facts (design step 4)
  set Gr : ℝ × ℝ → ℂ := fun p => -(fderiv ℝ g (z - circleMap 0 p.1 p.2))
    (Complex.exp (p.2 * Complex.I)) with hGr_def
  set Gθ : ℝ × ℝ → ℂ := fun p => -(fderiv ℝ g (z - circleMap 0 p.1 p.2))
    (Complex.I * p.1 * Complex.exp (p.2 * Complex.I)) with hGθ_def
  have hGr_deriv : ∀ p : ℝ × ℝ, HasDerivAt (fun r => g (z - circleMap 0 r p.2)) (Gr p) p.1 := by
    intro p
    have h1 : HasDerivAt (fun r : ℝ => z - circleMap 0 r p.2)
        (-(Complex.exp (p.2 * Complex.I))) p.1 :=
      (hasDerivAt_circleMap_r 0 p.2 p.1).const_sub z
    have h3 : HasFDerivAt g (fderiv ℝ g (z - circleMap 0 p.1 p.2)) (z - circleMap 0 p.1 p.2) :=
      (hgdiff (z - circleMap 0 p.1 p.2)).hasFDerivAt
    simpa [Gr, map_neg] using HasFDerivAt.comp_hasDerivAt_of_eq p.1 h3 h1 rfl
  have hGθ_deriv : ∀ p : ℝ × ℝ, HasDerivAt (fun θ => g (z - circleMap 0 p.1 θ)) (Gθ p) p.2 := by
    intro p
    have h1 : HasDerivAt (fun θ : ℝ => z - circleMap 0 p.1 θ)
        (-(circleMap 0 p.1 p.2 * Complex.I)) p.2 :=
      (hasDerivAt_circleMap 0 p.1 p.2).const_sub z
    have h3 : HasFDerivAt g (fderiv ℝ g (z - circleMap 0 p.1 p.2)) (z - circleMap 0 p.1 p.2) :=
      (hgdiff (z - circleMap 0 p.1 p.2)).hasFDerivAt
    have h4 := HasFDerivAt.comp_hasDerivAt_of_eq p.2 h3 h1 rfl
    have heq : circleMap 0 p.1 p.2 * Complex.I = Complex.I * p.1 * Complex.exp (p.2 * Complex.I) := by
      rw [circleMap]; ring
    rw [heq] at h4
    simpa [Gθ, map_neg] using h4
  have hcirc_cont : Continuous (fun p : ℝ × ℝ => z - circleMap 0 p.1 p.2) := by
    unfold circleMap; fun_prop
  have hGr_cont : Continuous Gr := by
    have hc2 : Continuous (fun p : ℝ × ℝ => Complex.exp ((p.2 : ℂ) * Complex.I)) := by fun_prop
    exact ((hfc.comp hcirc_cont).clm_apply hc2).neg
  have hGθ_cont : Continuous Gθ := by
    have hc2 : Continuous (fun p : ℝ × ℝ =>
        Complex.I * (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)) := by fun_prop
    exact ((hfc.comp hcirc_cont).clm_apply hc2).neg
  sorry

end RS
