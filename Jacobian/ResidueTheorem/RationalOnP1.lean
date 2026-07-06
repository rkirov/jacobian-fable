import Jacobian.CanonicalForms
import Jacobian.ProjectiveLine.Charts

/-!
# residue-theorem: the `ℙ¹` base case (file 1/3)

Unit: residue-theorem (`docs/design/residue-theorem.md` §6, `docs/design/form-trace-tower.md`
§RationalOnP1). Builds the genus-0 instance of the deliverable directly at the `MForm` level:
`∑ᶠ p, θ.resAt p = 0` for `θ : MForm (OnePoint ℂ)`.

## Construction

`RS.P1.formOfCoeFn` packages an arbitrary meromorphic "coefficient in the finite chart" function
`R : ℂ → ℂ` into a genuine `MFormData (OnePoint ℂ)`, PROVIDED its `invChart`-transported reading
`fun w => -(w^2)⁻¹ * R w⁻¹` is *also* meromorphic everywhere (the extra "meromorphic at `∞`"
datum a bare `R` does not automatically carry). The two-chart `compat` check is a single
"apply the transition rule twice returns to the start" computation, independent of what `R` is.
-/

open scoped ContDiff Manifold OnePoint
open Set Filter Topology OnePoint

noncomputable section

namespace RS.P1

/-- `chartAt`'s target is `univ` at every point of `ℙ¹` (both charts have target `univ`). -/
theorem chartAt_target_eq_univ (x : OnePoint ℂ) : (chartAt ℂ x).target = Set.univ := by
  induction x using OnePoint.rec with
  | infty => rw [chartAt_infty, invChart_target]
  | coe z => rw [chartAt_coe, coeChart_target]

/-- The chart-coefficient family assembled from a "finite-chart" function `R`, forced to be a
genuine `MFormData (OnePoint ℂ)` by requiring its `invChart` reading (the transition-rule image)
to also be meromorphic. -/
def formOfCoeFn (R : ℂ → ℂ) (hR : MeromorphicOn R Set.univ)
    (hR' : MeromorphicOn (fun w => -(w ^ 2)⁻¹ * R w⁻¹) Set.univ) :
    RS.MFormData (OnePoint ℂ) where
  coeffAt x z := x.elim (-(z ^ 2)⁻¹ * R z⁻¹) (fun _ => R z)
  coeffAt_zero_off x z hz := absurd (chartAt_target_eq_univ x ▸ Set.mem_univ z) hz
  meromorphicOn_coeffAt x := by
    rw [chartAt_target_eq_univ x]
    induction x using OnePoint.rec with
    | infty =>
      have heq : (fun z => (∞ : OnePoint ℂ).elim (-(z ^ 2)⁻¹ * R z⁻¹) (fun _ => R z))
          = fun z => -(z ^ 2)⁻¹ * R z⁻¹ := by funext z; rfl
      rw [heq]; exact hR'
    | coe p =>
      have heq : (fun z => ((p : OnePoint ℂ)).elim (-(z ^ 2)⁻¹ * R z⁻¹) (fun _ => R z))
          = fun z => R z := by funext z; rfl
      rw [heq]; exact hR
  compat x y z hz := by
    induction x using OnePoint.rec with
    | infty =>
      induction y using OnePoint.rec with
      | infty =>
        show (∞ : OnePoint ℂ).elim (-(z ^ 2)⁻¹ * R z⁻¹) (fun _ => R z)
          = deriv (⇑invChart ∘ ⇑invChart.symm) z *
            (∞ : OnePoint ℂ).elim (-(z ^ 2)⁻¹ * R z⁻¹) (fun _ => R z)
        have hderiv1 : deriv (⇑invChart ∘ ⇑invChart.symm) z = 1 := by
          have heq : (⇑invChart ∘ ⇑invChart.symm : ℂ → ℂ) = id := by
            funext w; exact invChart.right_inv (Set.mem_univ w)
          rw [heq, deriv_id]
        rw [hderiv1, one_mul]
      | coe q =>
        obtain ⟨p, hp, rfl⟩ := hz
        have hzne : (q : ℂ) ≠ 0 := by
          have := hp.1
          rw [invChart_source, Set.mem_compl_iff, Set.mem_singleton_iff, coe_eq_coe] at this
          exact this
        show ((q : ℂ) : OnePoint ℂ).elim (-((coeChart (q:OnePoint ℂ)) ^ 2)⁻¹
            * R (coeChart (q:OnePoint ℂ))⁻¹) (fun _ => R (coeChart (q:OnePoint ℂ)))
          = deriv (⇑invChart ∘ ⇑coeChart.symm) (coeChart (q:OnePoint ℂ)) *
            (∞ : OnePoint ℂ).elim (-((coeChart (q:OnePoint ℂ)) ^ 2)⁻¹
              * R (coeChart (q:OnePoint ℂ))⁻¹) (fun _ => R (coeChart (q:OnePoint ℂ)))
        rw [coeChart_apply_coe]
        show R (q:ℂ) = deriv (⇑invChart ∘ ⇑coeChart.symm) (q:ℂ) * (-((q:ℂ) ^ 2)⁻¹ * R (q:ℂ)⁻¹)
        have hderivinv : deriv (⇑invChart ∘ ⇑coeChart.symm) (q:ℂ) = -((q:ℂ) ^ 2)⁻¹ := by
          have heq : (⇑invChart ∘ ⇑coeChart.symm : ℂ → ℂ) = Inv.inv := invChart_comp_coe
          rw [heq, deriv_inv]
        rw [hderivinv]
        have hz2 : ((q:ℂ)⁻¹)⁻¹ = (q:ℂ) := inv_inv _
        have hzz : (-((q:ℂ)⁻¹) ^ 2)⁻¹ = -((q:ℂ) ^ 2) := by
          field_simp
        rw [hz2]
        have : -((q:ℂ) ^ 2)⁻¹ * (-((q:ℂ) ^ 2) * R (q:ℂ)) = R (q:ℂ) := by
          field_simp
        rw [neg_mul, neg_mul, neg_neg, mul_assoc]
        rw [show ((q:ℂ) ^ 2)⁻¹ * ((q:ℂ) ^ 2 * R (q:ℂ)) = R (q:ℂ) by field_simp]
    | coe p =>
      induction y using OnePoint.rec with
      | infty =>
        obtain ⟨q, hq, rfl⟩ := hz
        have hzne : (q : ℂ) ≠ 0 := by
          have := hq.2
          rw [invChart_source, Set.mem_compl_iff, Set.mem_singleton_iff, coe_eq_coe] at this
          exact this
        show (∞ : OnePoint ℂ).elim (-((invChart (q:OnePoint ℂ)) ^ 2)⁻¹
            * R (invChart (q:OnePoint ℂ))⁻¹) (fun _ => R (invChart (q:OnePoint ℂ)))
          = deriv (⇑coeChart ∘ ⇑invChart.symm) (invChart (q:OnePoint ℂ)) *
            ((p:OnePoint ℂ)).elim (-((invChart (q:OnePoint ℂ)) ^ 2)⁻¹
              * R (invChart (q:OnePoint ℂ))⁻¹) (fun _ => R (invChart (q:OnePoint ℂ)))
        rw [invChart_apply_coe]
        show -(((q:ℂ)⁻¹) ^ 2)⁻¹ * R (((q:ℂ)⁻¹)⁻¹)
          = deriv (⇑coeChart ∘ ⇑invChart.symm) ((q:ℂ)⁻¹) * R ((q:ℂ)⁻¹)⁻¹
        have hz2 : (((q:ℂ)⁻¹)⁻¹) = (q:ℂ) := inv_inv _
        rw [hz2]
        have hderivinv : deriv (⇑coeChart ∘ ⇑invChart.symm) ((q:ℂ)⁻¹) = -(((q:ℂ)⁻¹) ^ 2)⁻¹ := by
          have heq : (⇑coeChart ∘ ⇑invChart.symm : ℂ → ℂ) = Inv.inv := by
            funext w
            show coeChart (invChart.symm w) = w⁻¹
            rw [invChart_symm_apply]
            by_cases hw : w = 0
            · subst hw; simp
            · rw [inversion_coe hw, coeChart_apply_coe]
          rw [heq, deriv_inv]
        rw [hderivinv]
      | coe q =>
        obtain ⟨r, hr, hrz⟩ := hz
        have hderiv1 : deriv (⇑coeChart ∘ ⇑coeChart.symm) z = 1 := by
          have heq : (⇑coeChart ∘ ⇑coeChart.symm : ℂ → ℂ) = id := by
            funext w; exact coeChart.right_inv (Set.mem_univ w)
          rw [heq, deriv_id]
        show ((q:ℂ) : OnePoint ℂ).elim (-(z ^ 2)⁻¹ * R z⁻¹) (fun _ => R z)
          = deriv (⇑coeChart ∘ ⇑coeChart.symm) z *
            (((p:ℂ)):OnePoint ℂ).elim (-(z ^ 2)⁻¹ * R z⁻¹) (fun _ => R z)
        rw [hderiv1, one_mul]

end RS.P1
