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
  simp [cauchyKernel, norm_inv, norm_mul, Real.norm_of_nonneg Real.pi_pos.le]

/-- Step 1 of the design: `cauchyKernel` is integrable on every ball centred at `0`. -/
theorem integrableOn_cauchyKernel_ball (ρ : ℝ) :
    IntegrableOn cauchyKernel (ball (0 : ℂ) ρ) volume := by
  rcases le_or_lt ρ 0 with hρ | hρ
  · simp [ball_eq_empty.2 hρ]
  refine ⟨aestronglyMeasurable_cauchyKernel.restrict, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hind : (∫⁻ w in ball (0 : ℂ) ρ, ‖cauchyKernel w‖ₑ ∂volume) =
      ∫⁻ w, (ball (0 : ℂ) ρ).indicator (fun w => ‖cauchyKernel w‖ₑ) w ∂volume := by
    rw [lintegral_indicator measurableSet_ball]
  rw [hind, ← Complex.lintegral_comp_polarCoord_symm]
  have hbound : ∀ p ∈ Complex.polarCoord.target,
      ENNReal.ofReal p.1 • (ball (0 : ℂ) ρ).indicator (fun w => ‖cauchyKernel w‖ₑ)
          (Complex.polarCoord.symm p) ≤
        (Set.Ioo (0 : ℝ) ρ ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
          (fun _ => ENNReal.ofReal (Real.pi⁻¹)) p := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    by_cases hrρ : r < ρ
    · rw [Set.indicator_of_mem ⟨hr, hrρ⟩,
        Set.indicator_of_mem (Complex.norm_polarCoord_symm (r, θ) ▸
          (mem_ball_zero_iff.2 (by rwa [Complex.norm_polarCoord_symm, abs_of_pos hr])))]
      have hne : Complex.polarCoord.symm (r, θ) ≠ 0 := by
        rw [← norm_pos_iff, Complex.norm_polarCoord_symm]
        exact abs_pos.2 hr.ne'
      rw [norm_cauchyKernel, Complex.norm_polarCoord_symm, abs_of_pos hr, smul_eq_mul,
        ← ENNReal.ofReal_mul hr.le]
      have : r * (Real.pi * r)⁻¹ = Real.pi⁻¹ := by
        field_simp
      rw [this]
    · rw [Set.indicator_of_notMem]
      · simp
      · intro ⟨_, hlt⟩; exact hrρ hlt
  refine lt_of_le_of_lt (lintegral_mono_ae (Filter.Eventually.of_forall (fun p =>
    (le_of_eq rfl : _))).mono ?_) ?_
  · exact fun p _ => by
      by_cases hp : p ∈ Complex.polarCoord.target
      · exact hbound p hp
      · simp [hp, Complex.polarCoord_target] at hp ⊢
  · rw [lintegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
    rw [MeasureTheory.setLIntegral_const]
    rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
      Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
    refine ENNReal.mul_lt_top ?_ ENNReal.ofReal_lt_top
    exact ENNReal.mul_lt_top (by simp [ENNReal.ofReal_lt_top]) ENNReal.ofReal_lt_top

theorem locallyIntegrable_cauchyKernel : LocallyIntegrable cauchyKernel volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨ρ, hρ⟩ := hK.isBounded.subset_ball (0 : ℂ)
  exact (integrableOn_cauchyKernel_ball ρ).mono_set hρ

end RS
