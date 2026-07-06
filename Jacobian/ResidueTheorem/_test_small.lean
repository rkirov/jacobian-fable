import Jacobian.ResidueTheorem.RationalOnP1

set_option maxHeartbeats 1000000

open scoped ContDiff Manifold OnePoint Classical
open Set Filter Topology OnePoint RS.P1

noncomputable section

theorem sum_resAt_eq_zero_P1 (Θ : RS.MForm (OnePoint ℂ)) : ∑ᶠ p, Θ.resAt p = 0 := by
  obtain ⟨θ, rfl⟩ := Θ.exists_rep
  set R : ℂ → ℂ := θ.coeffAt ((0:ℂ):OnePoint ℂ) with hR_def
  have hRsame : ∀ a : ℂ, θ.coeffAt ((a:ℂ):OnePoint ℂ) = R :=
    fun a => coeffAt_coe_eq_coeffAt_coe θ a 0
  have hRmero : MeromorphicOn R Set.univ := by
    have h := θ.meromorphicOn_coeffAt ((0:ℂ):OnePoint ℂ)
    rwa [chartAt_coe, coeChart_target] at h
  have hordeq : ∀ a : ℂ, θ.ord ((a:ℂ):OnePoint ℂ) = meromorphicOrderAt R a := by
    intro a
    show meromorphicOrderAt (θ.coeffAt ((a:ℂ):OnePoint ℂ))
      (chartAt ℂ ((a:ℂ):OnePoint ℂ) ((a:ℂ):OnePoint ℂ)) = _
    rw [hRsame a, chartAt_coe, coeChart_apply_coe]
  have hSfin0 : (RS.MForm.mk θ).divisor.support.Finite :=
    (RS.MForm.mk θ).divisor.finiteSupport isCompact_univ
  have hSsub : {p : OnePoint ℂ | (RS.MForm.mk θ).ord p < 0} ⊆ (RS.MForm.mk θ).divisor.support := by
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    simp only [Function.mem_support, ne_eq, RS.MForm.divisor_apply]
    intro hcon
    rw [WithTop.untop₀_eq_zero] at hcon
    rcases hcon with hcon | hcon
    · rw [hcon] at hp; exact absurd hp (lt_irrefl 0)
    · rw [hcon] at hp; exact absurd hp (by simp)
  have hSfin : {p : OnePoint ℂ | (RS.MForm.mk θ).ord p < 0}.Finite := hSfin0.subset hSsub
  have hSfinC : {a : ℂ | meromorphicOrderAt R a < 0}.Finite := by
    have heq : {a : ℂ | meromorphicOrderAt R a < 0}
        = ((↑) : ℂ → OnePoint ℂ) ⁻¹' {p : OnePoint ℂ | (RS.MForm.mk θ).ord p < 0} := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_preimage, RS.MForm.ord_mk, hordeq]
    rw [heq]
    exact Set.Finite.preimage (Set.injOn_of_injective (fun x y => coe_eq_coe.mp)) hSfin
  set S : Finset ℂ := hSfinC.toFinset with hS_def
  have haS : ∀ a : ℂ, a ∈ S ↔ meromorphicOrderAt R a < 0 := by
    intro a; rw [hS_def, Set.Finite.mem_toFinset]; rfl
  -- The tail
  set R_tail : ℂ → ℂ := fun z => ∑ a ∈ S, RS.principalPartAt R a z with hRtail_def
  have hRtailMero : MeromorphicOn R_tail Set.univ := by
    intro z _
    apply MeromorphicAt.fun_sum
    intro a _
    exact RS.meromorphicAt_principalPartAt
  have hRtailInv : MeromorphicOn (fun w => -(w ^ 2)⁻¹ * R_tail w⁻¹) Set.univ := by
    intro w _
    have heq : (fun w => -(w ^ 2)⁻¹ * R_tail w⁻¹)
        = fun w => ∑ a ∈ S, (-(w ^ 2)⁻¹ * RS.principalPartAt R a w⁻¹) := by
      funext w; rw [hRtail_def]; simp [Finset.mul_sum]
    rw [heq]
    apply MeromorphicAt.fun_sum
    intro a _
    unfold RS.principalPartAt
    have heq2 : (fun w => -(w ^ 2)⁻¹ *
          ∑ k ∈ Finset.Icc (meromorphicOrderAt R a).untop₀ (-1), RS.laurentCoeffAt R a k * (w⁻¹ - a) ^ k)
        = fun w => ∑ k ∈ Finset.Icc (meromorphicOrderAt R a).untop₀ (-1),
          RS.laurentCoeffAt R a k * (-(w ^ 2)⁻¹ * (w⁻¹ - a) ^ k) := by
      funext w; rw [Finset.mul_sum]; congr 1; funext k; ring
    rw [heq2]
    apply MeromorphicAt.fun_sum
    intro k _
    exact (RS.meromorphicAt_neg_sq_inv_mul_sub_inv_zpow a k).const_mul _
  set Θtail : RS.MFormData (OnePoint ℂ) := formOfCoeFn R_tail hRtailMero hRtailInv with hΘtail_def
  have hΘtail_coe : ∀ a : ℂ, Θtail.coeffAt ((a:ℂ):OnePoint ℂ) = R_tail := by
    intro a; rfl
  have hΘtail_infty : Θtail.coeffAt (∞ : OnePoint ℂ) = fun w => -(w ^ 2)⁻¹ * R_tail w⁻¹ := by
    rfl
  sorry
