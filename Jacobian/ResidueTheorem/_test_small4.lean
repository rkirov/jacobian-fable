import Jacobian.ResidueTheorem.RationalOnP1

open scoped ContDiff Manifold OnePoint Classical
open Set Filter Topology OnePoint RS.P1

noncomputable section

theorem coeffAt_infty_eventuallyEq (θ : RS.MFormData (OnePoint ℂ)) :
    θ.coeffAt (∞ : OnePoint ℂ) =ᶠ[𝓝[≠] (0:ℂ)]
      fun z => -(z ^ 2)⁻¹ * θ.coeffAt ((0:ℂ):OnePoint ℂ) z⁻¹ := by
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzne : z ≠ 0 := hz
  have hz' : z ∈ ⇑(chartAt ℂ (∞:OnePoint ℂ)) ''
      ((chartAt ℂ ((0:ℂ):OnePoint ℂ)).source ∩ (chartAt ℂ (∞:OnePoint ℂ)).source) := by
    rw [chartAt_infty, chartAt_coe]
    refine ⟨invChart.symm z, ⟨?_, invChart.map_target (Set.mem_univ z)⟩,
      invChart.right_inv (Set.mem_univ z)⟩
    rw [coeChart_source, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcon
    exact hzne (by
      have := invChart.right_inv (Set.mem_univ z)
      rw [hcon] at this
      simpa using this.symm)
  have hc := θ.compat ((0:ℂ):OnePoint ℂ) (∞:OnePoint ℂ) z hz'
  rw [chartAt_infty, chartAt_coe] at hc
  rw [hc]
  rw [show (⇑coeChart (⇑invChart.symm z) : ℂ) = z⁻¹ by
    rw [invChart_symm_apply, coeChart_inversion_coe]]
  have hcomp : (⇑coeChart ∘ ⇑invChart.symm : ℂ → ℂ) = Inv.inv := by
    funext w
    show coeChart (invChart.symm w) = w⁻¹
    rw [invChart_symm_apply]
    by_cases hw : w = 0
    · subst hw; simp
    · rw [inversion_coe hw, coeChart_apply_coe]
  rw [hcomp, deriv_inv]

end
