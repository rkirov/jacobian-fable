import Jacobian.PlanarStokes.CompactSupport
import Jacobian.ResidueCalculus.IntegralBridge
import Jacobian.ResidueCalculus.Residue
import Jacobian.ResidueCalculus.PrincipalPart
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The annulus Stokes identity and the smeared residue theorem

Unit: planar-stokes-atoms (`docs/design/planar-stokes.md` §7–§8). Two theorems:

* `circleIntegral_sub_circleIntegral_eq_two_mul_I_mul_integral_wirtingerDbar` (Atom 1′): the
  area-to-boundary identity for the `∂̄` of an arbitrary `C¹` function on a closed annulus, proved
  by the exponential substitution `w = c + exp ζ` mapping a rectangle onto the annulus. No
  meromorphy, no residues.
* `integral_wirtingerDbar_mul_eq_neg_pi_mul_resAt` (Atom 2, the smeared residue theorem) and its
  model-case regression check `integral_wirtingerDbar_mul_inv_sub_eq` (`f = 1/(z-p)`, proved a
  second, independent way via `RS.cauchyPompeiu`).

Deviation from the design's §7 proof sketch: instead of routing the area term through
`Complex.polarCoord` (whose target `Ioi 0 ×ˢ Ioo(-π,π)` forces a periodicity-shift reconciliation
against the `[0,2π]` circle parametrization), we apply
`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul` directly to the substitution
`τ ζ = c + exp ζ` on the half-open-in-angle rectangle `Icc a b ×ℂ Ico 0 (2π)` (`a = log r`,
`b = log R`), which `τ` maps *bijectively* onto the annulus (no missing ray, unlike the open
rectangle) — a shorter route to the same identity, using the same mathlib machinery flagged as
the design's own R2 fallback.
-/

open Complex MeasureTheory Set Filter Metric
open scoped Real

noncomputable section

namespace RS

/-! ## Helper facts -/

section Helpers

variable {u : ℂ → ℂ}

/-- The determinant (as a real-linear self-map of `ℂ`) of the real differential of a
holomorphic map, in closed form: `|det| = normSq (deriv)`. -/
private theorem det_fderiv_of_differentiableAt {τ : ℂ → ℂ} {ζ : ℂ}
    (hτ : DifferentiableAt ℂ τ ζ) :
    (fderiv ℝ τ ζ).det = Complex.normSq (deriv τ ζ) := by
  have hr : fderiv ℝ τ ζ = (fderiv ℂ τ ζ).restrictScalars ℝ := hτ.fderiv_restrictScalars ℝ
  have hspan : fderiv ℂ τ ζ = ContinuousLinearMap.toSpanSingleton ℂ (deriv τ ζ) := by
    ext v
    rw [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, fderiv_eq_deriv_mul]
    ring
  rw [hr, hspan]
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]

/-- A horizontal segment (fixed imaginary part, real part ranging over any set) is Lebesgue-null
in `ℂ`. -/
private theorem measure_reProdIm_im_singleton (y0 : ℝ) (s : Set ℝ) :
    volume (Complex.reProdIm s {y0}) = 0 := by
  have heq : (Complex.reProdIm s {y0} : Set ℂ)
      = Complex.measurableEquivRealProd ⁻¹' (s ×ˢ ({y0} : Set ℝ)) := by
    ext w; simp [Complex.reProdIm, Complex.measurableEquivRealProd_apply]
  rw [heq, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    MeasureTheory.Measure.prod_prod, Real.volume_singleton, mul_zero]

/-- A vertical segment (fixed real part, imaginary part ranging over any set) is Lebesgue-null
in `ℂ`. -/
private theorem measure_reProdIm_re_singleton (x0 : ℝ) (t : Set ℝ) :
    volume (Complex.reProdIm ({x0} : Set ℝ) t) = 0 := by
  have heq : (Complex.reProdIm ({x0} : Set ℝ) t : Set ℂ)
      = Complex.measurableEquivRealProd ⁻¹' (({x0} : Set ℝ) ×ˢ t) := by
    ext w; simp [Complex.reProdIm, Complex.measurableEquivRealProd_apply]
  rw [heq, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    MeasureTheory.Measure.prod_prod, Real.volume_singleton, zero_mul]

private theorem measure_reProdIm_pair_re (x0 x1 : ℝ) (t : Set ℝ) :
    volume (Complex.reProdIm ({x0, x1} : Set ℝ) t) = 0 := by
  have hset : (Complex.reProdIm ({x0, x1} : Set ℝ) t : Set ℂ)
      = Complex.reProdIm {x0} t ∪ Complex.reProdIm {x1} t := by
    ext w; simp [Complex.reProdIm, or_and_right]
  rw [hset]
  exact measure_union_null (measure_reProdIm_re_singleton x0 t) (measure_reProdIm_re_singleton x1 t)

private theorem measure_reProdIm_pair_im (s : Set ℝ) (y0 y1 : ℝ) :
    volume (Complex.reProdIm s ({y0, y1} : Set ℝ)) = 0 := by
  have hset : (Complex.reProdIm s ({y0, y1} : Set ℝ) : Set ℂ)
      = Complex.reProdIm s {y0} ∪ Complex.reProdIm s {y1} := by
    ext w; simp [Complex.reProdIm, and_or_left]
  rw [hset]
  exact measure_union_null (measure_reProdIm_im_singleton y0 s) (measure_reProdIm_im_singleton y1 s)

/-- The frame (closed rectangle minus open rectangle) is Lebesgue-null. -/
private theorem measure_frame_null (a b lo hi : ℝ) (hab : a ≤ b) (hlohi : lo ≤ hi) :
    volume (Complex.reProdIm (Set.Icc a b) (Set.Icc lo hi)
      \ Complex.reProdIm (Set.Ioo a b) (Set.Ioo lo hi)) = 0 := by
  have hsub : Complex.reProdIm (Set.Icc a b) (Set.Icc lo hi)
      \ Complex.reProdIm (Set.Ioo a b) (Set.Ioo lo hi)
      ⊆ Complex.reProdIm ({a, b} : Set ℝ) (Set.Icc lo hi)
        ∪ Complex.reProdIm (Set.Icc a b) ({lo, hi} : Set ℝ) := by
    rintro w ⟨hw, hw'⟩
    rw [Complex.mem_reProdIm] at hw
    by_cases hre : w.re ∈ Set.Ioo a b
    · right
      rw [Complex.mem_reProdIm]
      refine ⟨hw.1, ?_⟩
      have hnotim : w.im ∉ Set.Ioo lo hi := fun h => hw' (Complex.mem_reProdIm.mpr ⟨hre, h⟩)
      have hmem : w.im ∈ Set.Icc lo hi \ Set.Ioo lo hi := ⟨hw.2, hnotim⟩
      rwa [Icc_diff_Ioo_same hlohi] at hmem
    · left
      rw [Complex.mem_reProdIm]
      refine ⟨?_, hw.2⟩
      have hmem : w.re ∈ Set.Icc a b \ Set.Ioo a b := ⟨hw.1, hre⟩
      rwa [Icc_diff_Ioo_same hab] at hmem
  have hbound : volume (Complex.reProdIm ({a, b} : Set ℝ) (Set.Icc lo hi)
      ∪ Complex.reProdIm (Set.Icc a b) ({lo, hi} : Set ℝ)) = 0 :=
    measure_union_null (measure_reProdIm_pair_re a b (Set.Icc lo hi))
      (measure_reProdIm_pair_im (Set.Icc a b) lo hi)
  exact measure_mono_null hsub hbound

/-- The exp-substitution algebraic core (de-risked in the design's spike, §9): the `∂̄` of the
transported function `u(c + exp ·) * exp` sees `u`'s `∂̄` scaled by `‖exp ζ‖²`. -/
private theorem wirtingerDbar_expSubst_eq {c ζ : ℂ}
    (hu : DifferentiableAt ℝ u (c + Complex.exp ζ)) :
    wirtingerDbar (fun w => u (c + Complex.exp w) * Complex.exp w) ζ =
      Complex.exp ζ * (starRingEnd ℂ) (Complex.exp ζ) * wirtingerDbar u (c + Complex.exp ζ) := by
  have hexp : DifferentiableAt ℂ Complex.exp ζ := Complex.differentiableAt_exp
  have hexpR : DifferentiableAt ℝ Complex.exp ζ := hexp.restrictScalars ℝ
  have hcexp : DifferentiableAt ℝ (fun w => c + Complex.exp w) ζ :=
    (differentiableAt_const c).add hexpR
  have hcomp : DifferentiableAt ℝ (fun w => u (c + Complex.exp w)) ζ := hu.comp ζ hcexp
  rw [wirtingerDbar_mul hcomp hexpR]
  have hchain : wirtingerDbar (fun w => u (c + Complex.exp w)) ζ =
      (starRingEnd ℂ) (deriv (fun w => c + Complex.exp w) ζ)
        * wirtingerDbar u (c + Complex.exp ζ) :=
    wirtingerDbar_comp_differentiableAt (τ := fun w => c + Complex.exp w) u ζ hu
      (hexp.const_add c)
  have hderivexp : deriv (fun w => c + Complex.exp w) ζ = Complex.exp ζ := by
    rw [deriv_const_add, congrFun Complex.deriv_exp ζ]
  have hbar0 : wirtingerDbar Complex.exp ζ = 0 :=
    wirtingerDbar_eq_zero_of_differentiableAt Complex.exp ζ hexp
  rw [hchain, hderivexp, hbar0]
  ring

end Helpers

/-! ## The annulus identity (Atom 1′) -/

/-- **Atom 1′** (annulus Stokes, general — no meromorphy, no residue): area-to-boundary identity
for the `∂̄` of an arbitrary `C¹` function on a closed annulus. -/
theorem circleIntegral_sub_circleIntegral_eq_two_mul_I_mul_integral_wirtingerDbar
    {u : ℂ → ℂ} {c : ℂ} {r R : ℝ} (h0 : 0 < r) (hle : r ≤ R)
    (hu : ContDiffOn ℝ 1 u (Metric.closedBall c R \ Metric.ball c r)) :
    (∮ w in C(c, R), u w) - (∮ w in C(c, r), u w) =
      2 * I * ∫ w in (Metric.closedBall c R \ Metric.ball c r), wirtingerDbar u w := by
  rcases hle.lt_or_eq with hRr | hRr
  swap
  · -- Degenerate case `r = R`: the annulus collapses to a circle (measure zero).
    subst hRr
    have hAeq : Metric.closedBall c r \ Metric.ball c r = Metric.sphere c r := by
      ext w
      simp only [Metric.mem_closedBall, Metric.mem_ball, Metric.mem_sphere, Set.mem_diff, not_lt]
      exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩
    rw [hAeq, MeasureTheory.setIntegral_measure_zero _ (Measure.addHaar_sphere volume c r),
      mul_zero, sub_self]
  · -- Main case `r < R`.
    have hRpos : 0 < R := h0.trans hRr
    set a : ℝ := Real.log r with ha_def
    set b : ℝ := Real.log R with hb_def
    have hea : Real.exp a = r := Real.exp_log h0
    have heb : Real.exp b = R := Real.exp_log hRpos
    have hab : a < b := (Real.log_lt_log_iff h0 hRpos).mpr hRr
    set τ : ℂ → ℂ := fun ζ => c + Complex.exp ζ with hτ_def
    set A : Set ℂ := Metric.closedBall c R \ Metric.ball c r with hA_def
    set Rec : Set ℂ := Complex.reProdIm (Set.Icc a b) (Set.Icc (0 : ℝ) (2 * π)) with hRec_def
    set F : ℂ → ℂ := fun ζ => u (τ ζ) * Complex.exp ζ with hF_def
    -- `τ` is entire.
    have hτ_diffC : ∀ ζ, DifferentiableAt ℂ τ ζ := fun ζ =>
      (Complex.differentiableAt_exp).const_add c
    have hτ_diffR : ∀ ζ, DifferentiableAt ℝ τ ζ := fun ζ => (hτ_diffC ζ).restrictScalars ℝ
    have hderivτ : ∀ ζ, deriv τ ζ = Complex.exp ζ := by
      intro ζ
      rw [hτ_def, deriv_const_add, congrFun Complex.deriv_exp ζ]
    -- `τ` maps `Rec` into `A`.
    have hτ_maps : Set.MapsTo τ Rec A := by
      intro ζ hζ
      rw [hRec_def, Complex.mem_reProdIm] at hζ
      have hdist : dist (τ ζ) c = Real.exp ζ.re := by
        rw [hτ_def, dist_eq_norm, show c + Complex.exp ζ - c = Complex.exp ζ from by ring,
          Complex.norm_exp]
      have hlow : r ≤ Real.exp ζ.re := by
        rw [← hea]; exact Real.exp_le_exp.mpr hζ.1.1
      have hhigh : Real.exp ζ.re ≤ R := by
        rw [← heb]; exact Real.exp_le_exp.mpr hζ.1.2
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_closedBall, hdist]; exact hhigh
      · rw [Metric.mem_ball, not_lt, hdist] at *; exact hlow
    -- The half-open-in-angle domain, on which `τ` is a genuine bijection onto `A`.
    set s : Set ℂ := Complex.reProdIm (Set.Icc a b) (Set.Ico (0 : ℝ) (2 * π)) with hs_def
    have hs_sub_Rec : s ⊆ Rec := by
      intro ζ hζ
      rw [hs_def, Complex.mem_reProdIm] at hζ
      rw [hRec_def, Complex.mem_reProdIm]
      exact ⟨hζ.1, ⟨hζ.2.1, hζ.2.2.le⟩⟩
    have hs_maps : Set.MapsTo τ s A := hτ_maps.mono_left hs_sub_Rec
    -- Injectivity of `τ` on `s`.
    have hτ_inj : Set.InjOn τ s := by
      intro ζ1 hζ1 ζ2 hζ2 heq
      rw [hs_def, Complex.mem_reProdIm] at hζ1 hζ2
      have heq' : Complex.exp ζ1 = Complex.exp ζ2 := by
        have hh : c + Complex.exp ζ1 = c + Complex.exp ζ2 := by simpa [hτ_def] using heq
        exact add_left_cancel hh
      rw [Complex.exp_eq_exp_iff_exists_int] at heq'
      obtain ⟨n, hn⟩ := heq'
      have hre : ζ1.re = ζ2.re := by
        have := congrArg Complex.re hn; simpa using this
      have him : ζ1.im = ζ2.im + n * (2 * π) := by
        have := congrArg Complex.im hn; simpa using this
      have hn0 : n = 0 := by
        have hb1 := hζ1.2.1; have hb2 := hζ1.2.2
        have hc1 := hζ2.2.1; have hc2 := hζ2.2.2
        have hbound1 : -(2 * π) < (n : ℝ) * (2 * π) := by nlinarith
        have hbound2 : (n : ℝ) * (2 * π) < 2 * π := by nlinarith
        have hpi : (0 : ℝ) < 2 * π := Real.two_pi_pos
        have hn1 : (-1 : ℝ) < (n : ℝ) := by nlinarith
        have hn2 : (n : ℝ) < 1 := by nlinarith
        have h1' : (-1 : ℤ) < n := by exact_mod_cast hn1
        have h2' : n < (1 : ℤ) := by exact_mod_cast hn2
        omega
      rw [hn0] at him
      simp only [Int.cast_zero, zero_mul, add_zero] at him
      exact Complex.ext hre him
    -- `τ '' s = A` exactly.
    have hτ_image : τ '' s = A := by
      apply Set.Subset.antisymm (Set.image_subset_iff.mpr hs_maps)
      intro w hw
      set ρ : ℝ := ‖w - c‖ with hρ_def
      have hρpos : 0 < ρ := by
        rw [hρ_def, norm_pos_iff, sub_ne_zero]
        rintro rfl
        exact hw.2 (Metric.mem_ball_self h0)
      have hρr : r ≤ ρ := by
        have hh := hw.2
        rw [Metric.mem_ball, not_lt] at hh
        rwa [hρ_def, ← dist_eq_norm]
      have hρR : ρ ≤ R := by
        have hh := hw.1
        rw [Metric.mem_closedBall] at hh
        rwa [hρ_def, ← dist_eq_norm]
      set θ₀ : ℝ := Complex.arg (w - c) with hθ₀_def
      have hθ₀range := Complex.arg_mem_Ioc (w - c)
      set y : ℝ := if θ₀ < 0 then θ₀ + 2 * π else θ₀ with hy_def
      have hyrange : y ∈ Set.Ico (0 : ℝ) (2 * π) := by
        rw [hy_def]
        split_ifs with hneg
        · exact ⟨by linarith [hθ₀range.1], by linarith [hθ₀range.2]⟩
        · push Not at hneg
          exact ⟨hneg, by linarith [hθ₀range.2, Real.pi_pos]⟩
      have hexpy : Complex.exp (y * I) = Complex.exp (θ₀ * I) := by
        rw [hy_def]
        split_ifs with hneg
        · rw [show ((θ₀ + 2 * π : ℝ) : ℂ) * I = θ₀ * I + 2 * π * I by push_cast; ring,
            Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
        · rfl
      set x : ℝ := Real.log ρ with hx_def
      have hxrange : x ∈ Set.Icc a b := by
        rw [hx_def, ha_def, hb_def]
        exact ⟨(Real.log_le_log_iff h0 hρpos).mpr hρr, (Real.log_le_log_iff hρpos hRpos).mpr hρR⟩
      refine ⟨x + y * I, ?_, ?_⟩
      · rw [hs_def, Complex.mem_reProdIm]
        simpa using ⟨hxrange, hyrange⟩
      · rw [hτ_def]
        simp only
        rw [Complex.exp_add, ← Complex.ofReal_exp, hx_def, Real.exp_log hρpos, hexpy,
          Complex.norm_mul_exp_arg_mul_I]
        ring
    -- `Rec` is convex with nonempty interior, hence a set of unique differentiability.
    have hRe_lin : IsLinearMap ℝ Complex.re := ⟨Complex.add_re, fun t v => by
      simp [Complex.real_smul, Complex.mul_re]⟩
    have hIm_lin : IsLinearMap ℝ Complex.im := ⟨Complex.add_im, fun t v => by
      simp [Complex.real_smul, Complex.mul_im]⟩
    have hRec_convex : Convex ℝ Rec := by
      rw [hRec_def, Complex.reProdIm]
      exact ((convex_Icc a b).is_linear_preimage hRe_lin).inter
        ((convex_Icc 0 (2 * π)).is_linear_preimage hIm_lin)
    set RecOpen : Set ℂ := Complex.reProdIm (Set.Ioo a b) (Set.Ioo (0 : ℝ) (2 * π)) with
      hRecOpen_def
    have hRecOpen_isOpen : IsOpen RecOpen := by
      rw [hRecOpen_def, Complex.reProdIm]
      exact (isOpen_Ioo.preimage Complex.continuous_re).inter
        (isOpen_Ioo.preimage Complex.continuous_im)
    have hRecOpen_sub : RecOpen ⊆ Rec := by
      rw [hRecOpen_def, hRec_def]
      exact Complex.reProdIm_subset_iff.mpr
        (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self)
    have hRecOpen_nonempty : RecOpen.Nonempty := by
      refine ⟨⟨(a + b) / 2, π⟩, ?_⟩
      rw [hRecOpen_def, Complex.mem_reProdIm]
      refine ⟨?_, ?_⟩
      · show (a + b) / 2 ∈ Set.Ioo a b
        constructor <;> linarith
      · show π ∈ Set.Ioo (0 : ℝ) (2 * π)
        constructor <;> linarith [Real.pi_pos]
    have hRec_int : (interior Rec).Nonempty :=
      hRecOpen_nonempty.mono (interior_maximal hRecOpen_sub hRecOpen_isOpen)
    have hRec_uniqueDiff : UniqueDiffOn ℝ Rec := uniqueDiffOn_convex hRec_convex hRec_int
    -- Regularity of `τ`, `exp`, and `F` on `Rec`.
    have hτ_CD : ContDiff ℝ 1 τ := by
      rw [hτ_def]; exact contDiff_const.add (Complex.contDiff_exp (𝕜 := ℝ))
    have hexp_CD : ContDiff ℝ 1 Complex.exp := Complex.contDiff_exp (𝕜 := ℝ)
    have hu_CDRec : ContDiffOn ℝ 1 (u ∘ τ) Rec := ContDiffOn.comp hu hτ_CD.contDiffOn hτ_maps
    have hF_CDRec : ContDiffOn ℝ 1 F Rec := by
      have h1 : ContDiffOn ℝ 1 (fun ζ => (u ∘ τ) ζ * Complex.exp ζ) Rec :=
        hu_CDRec.mul hexp_CD.contDiffOn
      simpa [hF_def, Function.comp] using h1
    -- The explicit derivative candidate `f'`, continuous on all of `Rec`.
    set f' : ℂ → (ℂ →L[ℝ] ℂ) := fderivWithin ℝ F Rec with hf'_def
    have hf'_cont : ContinuousOn f' Rec :=
      hF_CDRec.continuousOn_fderivWithin hRec_uniqueDiff (le_refl 1)
    have hu_contOn : ContinuousOn u A := hu.continuousOn
    have hHc : ContinuousOn F Rec := by
      have h1 : ContinuousOn (u ∘ τ) Rec := hu_contOn.comp (hτ_CD.continuous.continuousOn) hτ_maps
      have h2 : ContinuousOn (fun ζ => (u ∘ τ) ζ * Complex.exp ζ) Rec :=
        h1.mul (hexp_CD.continuous.continuousOn)
      simpa [hF_def, Function.comp] using h2
    have hHi : IntegrableOn (fun ζ => I • f' ζ 1 - f' ζ I) Rec := by
      have hcont : ContinuousOn (fun ζ => I • f' ζ 1 - f' ζ I) Rec := by
        have h1 : ContinuousOn (fun ζ => f' ζ 1) Rec := hf'_cont.clm_apply continuousOn_const
        have h2 : ContinuousOn (fun ζ => f' ζ I) Rec := hf'_cont.clm_apply continuousOn_const
        exact (continuousOn_const.smul h1).sub h2
      have hcompact : IsCompact Rec := by
        rw [hRec_def]; exact IsCompact.reProdIm isCompact_Icc isCompact_Icc
      exact hcont.integrableOn_compact hcompact
    -- Interior points of `Rec` (in the `ζ`-rectangle) map to interior points of `A`.
    have hInterior_diff : ∀ ζ ∈ RecOpen, DifferentiableAt ℝ u (τ ζ) := by
      intro ζ hζ
      rw [hRecOpen_def, Complex.mem_reProdIm] at hζ
      have hτζ_int : τ ζ ∈ Metric.ball c R \ Metric.closedBall c r := by
        have hdist : dist (τ ζ) c = Real.exp ζ.re := by
          rw [hτ_def, dist_eq_norm, show c + Complex.exp ζ - c = Complex.exp ζ from by ring,
            Complex.norm_exp]
        have hlt1 : Real.exp ζ.re < R := by rw [← heb]; exact Real.exp_lt_exp.mpr hζ.1.2
        have hlt2 : r < Real.exp ζ.re := by rw [← hea]; exact Real.exp_lt_exp.mpr hζ.1.1
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_ball, hdist]; exact hlt1
        · rw [Metric.mem_closedBall, not_le, hdist]; exact hlt2
      have hAmem : A ∈ nhds (τ ζ) := by
        have hopenset : IsOpen (Metric.ball c R \ Metric.closedBall c r) :=
          Metric.isOpen_ball.sdiff Metric.isClosed_closedBall
        have hsub2 : Metric.ball c R \ Metric.closedBall c r ⊆ A := by
          rw [hA_def]
          rintro x ⟨hx1, hx2⟩
          rw [Metric.mem_ball] at hx1
          rw [Metric.mem_closedBall, not_le] at hx2
          exact ⟨by rw [Metric.mem_closedBall]; linarith, by rw [Metric.mem_ball, not_lt]; linarith⟩
        exact Filter.mem_of_superset (hopenset.mem_nhds hτζ_int) hsub2
      exact (hu.contDiffAt hAmem).differentiableAt (by norm_num)
    have hHd : ∀ ζ ∈ RecOpen, HasFDerivAt F (f' ζ) ζ := by
      intro ζ hζ
      have hud : DifferentiableAt ℝ u (τ ζ) := hInterior_diff ζ hζ
      have hτd : DifferentiableAt ℝ τ ζ := hτ_diffR ζ
      have hexpd : DifferentiableAt ℝ Complex.exp ζ := Complex.differentiableAt_exp (𝕜 := ℝ)
      have hFd : DifferentiableAt ℝ F ζ := by
        have h1 : DifferentiableAt ℝ (u ∘ τ) ζ := hud.comp ζ hτd
        have h2 : DifferentiableAt ℝ (fun ζ => (u ∘ τ) ζ * Complex.exp ζ) ζ := h1.mul hexpd
        simpa [hF_def, Function.comp] using h2
      have hnhds : Rec ∈ nhds ζ :=
        Filter.mem_of_superset (hRecOpen_isOpen.mem_nhds hζ) hRecOpen_sub
      rw [hf'_def, fderivWithin_of_mem_nhds hnhds]
      exact hFd.hasFDerivAt
    -- Apply the rectangle Stokes lemma with corners `z0 = a`, `w0 = b + 2πi`.
    set z0 : ℂ := (⟨a, 0⟩ : ℂ) with hz0_def
    set w0 : ℂ := (⟨b, 2 * π⟩ : ℂ) with hw0_def
    have hz0re : z0.re = a := rfl
    have hz0im : z0.im = 0 := rfl
    have hw0re : w0.re = b := rfl
    have hw0im : w0.im = 2 * π := rfl
    have hRec_eq : Complex.reProdIm (Set.uIcc z0.re w0.re) (Set.uIcc z0.im w0.im) = Rec := by
      rw [hz0re, hw0re, hz0im, hw0im, Set.uIcc_of_le hab.le, Set.uIcc_of_le Real.two_pi_pos.le]
    have hHc' : ContinuousOn F (Complex.reProdIm (Set.uIcc z0.re w0.re) (Set.uIcc z0.im w0.im)) := by
      rw [hRec_eq]; exact hHc
    have hHd' : ∀ x ∈ Set.Ioo (min z0.re w0.re) (max z0.re w0.re) ×ℂ
        Set.Ioo (min z0.im w0.im) (max z0.im w0.im), HasFDerivAt F (f' x) x := by
      rw [hz0re, hw0re, hz0im, hw0im, min_eq_left hab.le, max_eq_right hab.le,
        min_eq_left Real.two_pi_pos.le, max_eq_right Real.two_pi_pos.le]
      exact hHd
    have hHi' : IntegrableOn (fun ζ => I • f' ζ 1 - f' ζ I)
        (Complex.reProdIm (Set.uIcc z0.re w0.re) (Set.uIcc z0.im w0.im)) := by
      rw [hRec_eq]; exact hHi
    have hrect := Complex.integral_boundary_rect_of_continuousOn_of_hasFDerivAt_real F f' z0 w0
      hHc' hHd' hHi'
    rw [hz0re, hw0re, hz0im, hw0im] at hrect
    -- The `y`-boundary cancels by periodicity of `exp`.
    have hperiod : ∀ x : ℝ, F ((x : ℂ) + (0 : ℝ) * I) = F ((x : ℂ) + (2 * π : ℝ) * I) := by
      intro x
      have hx0 : (x : ℂ) + (0 : ℝ) * I = (x : ℂ) := by push_cast; ring
      have hx2pi : (x : ℂ) + (2 * π : ℝ) * I = (x : ℂ) + 2 * π * I := by push_cast; ring
      have hexp_eq : Complex.exp ((x : ℂ) + 2 * π * I) = Complex.exp (x : ℂ) :=
        Complex.exp_periodic x
      have hτ_eq : τ ((x : ℂ) + 2 * π * I) = τ (x : ℂ) := by
        rw [hτ_def]; simp only; rw [hexp_eq]
      rw [hF_def, hx0, hx2pi]
      simp only
      rw [hτ_eq, hexp_eq]
    have hLHS_yb : (∫ x : ℝ in a..b, F ((x : ℂ) + (0 : ℝ) * I))
        - (∫ x : ℝ in a..b, F ((x : ℂ) + (2 * π : ℝ) * I)) = 0 :=
      sub_eq_zero.mpr (intervalIntegral.integral_congr (fun x _ => hperiod x))
    -- The `x`-boundary identifies with the two circle integrals.
    have hFexp : ∀ (x0 ρ0 y : ℝ), Real.exp x0 = ρ0 →
        F ((x0 : ℂ) + y * I) = u (c + ρ0 * Complex.exp (y * I)) * (ρ0 * Complex.exp (y * I)) := by
      intro x0 ρ0 y hx0
      rw [hF_def, hτ_def]
      simp only
      have hexp_split : Complex.exp ((x0 : ℂ) + y * I) = ρ0 * Complex.exp (y * I) := by
        rw [Complex.exp_add, ← Complex.ofReal_exp, hx0]
      rw [hexp_split]
    have hcircleR : I • (∫ y : ℝ in (0 : ℝ)..(2 * π), F ((b : ℂ) + y * I)) = ∮ w in C(c, R), u w := by
      rw [← intervalIntegral.integral_smul]
      apply intervalIntegral.integral_congr
      intro y _
      show I • F ((b : ℂ) + y * I) = deriv (circleMap c R) y • u (circleMap c R y)
      rw [hFexp b R y heb, deriv_circleMap, circleMap, circleMap]
      simp only [zero_add, smul_eq_mul]
      ring
    have hcircler : I • (∫ y : ℝ in (0 : ℝ)..(2 * π), F ((a : ℂ) + y * I)) = ∮ w in C(c, r), u w := by
      rw [← intervalIntegral.integral_smul]
      apply intervalIntegral.integral_congr
      intro y _
      show I • F ((a : ℂ) + y * I) = deriv (circleMap c r) y • u (circleMap c r y)
      rw [hFexp a r y hea, deriv_circleMap, circleMap, circleMap]
      simp only [zero_add, smul_eq_mul]
      ring
    rw [hLHS_yb, zero_add, hcircleR, hcircler] at hrect
    -- Convert the RHS iterated integral to a set integral over `Rec`.
    have hiter_to_set : (∫ x : ℝ in a..b, ∫ y : ℝ in (0 : ℝ)..(2 * π),
        I • f' ((x : ℂ) + y * I) 1 - f' ((x : ℂ) + y * I) I) = ∫ ζ in Rec, I • f' ζ 1 - f' ζ I := by
      rw [hRec_def]
      exact (setIntegral_reProdIm_eq_intervalIntegral hab.le Real.two_pi_pos.le
        (hRec_def ▸ hHi)).symm
    rw [hiter_to_set] at hrect
    -- Pointwise, on `RecOpen`, the integrand matches `2i·normSq(exp ζ)·wirtingerDbar u (τ ζ)`.
    have hpt : ∀ ζ ∈ RecOpen, I • f' ζ 1 - f' ζ I
        = 2 * I * ((Complex.normSq (Complex.exp ζ) : ℝ) • wirtingerDbar u (τ ζ)) := by
      intro ζ hζ
      have hFderiv_eq : f' ζ = fderiv ℝ F ζ := by
        rw [hf'_def]
        exact fderivWithin_of_mem_nhds
          (Filter.mem_of_superset (hRecOpen_isOpen.mem_nhds hζ) hRecOpen_sub)
      rw [hFderiv_eq]
      have hud : DifferentiableAt ℝ u (τ ζ) := hInterior_diff ζ hζ
      have hFeq : F = fun w => u (c + Complex.exp w) * Complex.exp w := by rw [hF_def, hτ_def]
      have hwF : wirtingerDbar F ζ
          = Complex.exp ζ * (starRingEnd ℂ) (Complex.exp ζ) * wirtingerDbar u (τ ζ) := by
        rw [hFeq]
        exact wirtingerDbar_expSubst_eq (u := u) (c := c) (ζ := ζ) (by rwa [hτ_def] at hud)
      have h2i : I • fderiv ℝ F ζ 1 - fderiv ℝ F ζ I = 2 * I * wirtingerDbar F ζ := by
        simp only [wirtingerDbar, smul_eq_mul]
        have hI2 : I * I = -1 := Complex.I_mul_I
        linear_combination (-(fderiv ℝ F ζ I)) * hI2
      rw [h2i, hwF, Complex.mul_conj, Complex.real_smul]
      ring
    have hRecOpen_null_diff : volume (Rec \ RecOpen) = 0 := by
      rw [hRec_def, hRecOpen_def]
      exact measure_frame_null a b 0 (2 * π) hab.le Real.two_pi_pos.le
    have hae : ∀ᵐ ζ ∂volume, ζ ∈ Rec →
        I • f' ζ 1 - f' ζ I
          = 2 * I * ((Complex.normSq (Complex.exp ζ) : ℝ) • wirtingerDbar u (τ ζ)) := by
      have hnmem : ∀ᵐ ζ ∂volume, ζ ∉ Rec \ RecOpen :=
        MeasureTheory.ae_iff.mpr (by simpa using hRecOpen_null_diff)
      filter_upwards [hnmem] with ζ hζ hζRec
      by_contra hne
      exact hζ ⟨hζRec, fun hop => hne (hpt ζ hop)⟩
    have hRec_meas : MeasurableSet Rec := by
      rw [hRec_def, Complex.reProdIm]
      exact MeasurableSet.preimage (measurableSet_Icc.prod measurableSet_Icc)
        Complex.measurableEquivRealProd.measurable
    have hset_eq : (∫ ζ in Rec, I • f' ζ 1 - f' ζ I)
        = ∫ ζ in Rec, 2 * I * ((Complex.normSq (Complex.exp ζ) : ℝ) • wirtingerDbar u (τ ζ)) :=
      MeasureTheory.setIntegral_congr_ae hRec_meas hae
    rw [hset_eq] at hrect
    have hpull : (∫ ζ in Rec,
          2 * I * ((Complex.normSq (Complex.exp ζ) : ℝ) • wirtingerDbar u (τ ζ)))
        = 2 * I * ∫ ζ in Rec, (Complex.normSq (Complex.exp ζ) : ℝ) • wirtingerDbar u (τ ζ) :=
      MeasureTheory.integral_const_mul _ _
    rw [hpull] at hrect
    -- Restrict from `Rec` to `s` (differ by the one null edge `im = 2π`).
    have hs_meas : MeasurableSet s := by
      rw [hs_def, Complex.reProdIm]
      exact MeasurableSet.preimage (measurableSet_Icc.prod measurableSet_Ico)
        Complex.measurableEquivRealProd.measurable
    have hRecs_null_diff : volume (Rec \ s) = 0 := by
      have heq : Rec \ s = Complex.reProdIm (Set.Icc a b) ({2 * π} : Set ℝ) := by
        rw [hRec_def, hs_def, ← Icc_diff_Ico_same Real.two_pi_pos.le]
        ext w
        simp only [Complex.mem_reProdIm, Set.mem_diff]
        tauto
      rw [heq]
      exact measure_reProdIm_im_singleton (2 * π) (Set.Icc a b)
    have hRec_ae_s : Rec =ᵐ[volume] s := by
      rw [ae_eq_set]
      refine ⟨hRecs_null_diff, ?_⟩
      rw [Set.diff_eq_empty.mpr hs_sub_Rec]
      exact measure_empty
    have hRec_to_s : (∫ ζ in Rec, (Complex.normSq (Complex.exp ζ) : ℝ) • wirtingerDbar u (τ ζ))
        = ∫ ζ in s, (Complex.normSq (Complex.exp ζ) : ℝ) • wirtingerDbar u (τ ζ) :=
      MeasureTheory.setIntegral_congr_set hRec_ae_s
    rw [hRec_to_s] at hrect
    -- The Jacobian change of variables transports this to the area integral over `A`.
    have hJacobian : (∫ ζ in s, (Complex.normSq (Complex.exp ζ) : ℝ) • wirtingerDbar u (τ ζ))
        = ∫ w in A, wirtingerDbar u w := by
      have hderiv_eq : ∀ ζ ∈ s, HasFDerivWithinAt τ (fderiv ℝ τ ζ) s ζ :=
        fun ζ _ => (hτ_diffR ζ).hasFDerivAt.hasFDerivWithinAt
      have hjac := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume hs_meas
        hderiv_eq hτ_inj (wirtingerDbar u)
      rw [hτ_image] at hjac
      rw [hjac]
      apply MeasureTheory.setIntegral_congr_fun hs_meas
      intro ζ _
      congr 1
      rw [det_fderiv_of_differentiableAt (hτ_diffC ζ), hderivτ,
        abs_of_nonneg (Complex.normSq_nonneg _)]
    rw [hJacobian] at hrect
    exact hrect

