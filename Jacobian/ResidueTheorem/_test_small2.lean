import Jacobian.ResidueTheorem.RationalOnP1

open scoped ContDiff Manifold OnePoint Classical
open Set Filter Topology OnePoint RS.P1

noncomputable section

example (R : ℂ → ℂ) (S : Finset ℂ) (hRtailMero : MeromorphicOn (fun z => ∑ a ∈ S, RS.principalPartAt R a z) Set.univ) :
    MeromorphicOn (fun w => -(w ^ 2)⁻¹ * (∑ a ∈ S, RS.principalPartAt R a) w⁻¹) Set.univ := by
  intro w0 _
  by_cases hw0 : w0 = 0
  · subst hw0
    have heq : (fun w => -(w ^ 2)⁻¹ * (∑ a ∈ S, RS.principalPartAt R a) w⁻¹)
        = fun w => ∑ a ∈ S, (-(w ^ 2)⁻¹ * RS.principalPartAt R a w⁻¹) := by
      funext w; simp [Finset.mul_sum, Finset.sum_apply]
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
    exact (MeromorphicAt.const (RS.laurentCoeffAt R a k) 0).mul
      (meromorphicAt_neg_sq_inv_mul_sub_inv_zpow a k)
  · have hAnalyticInv : AnalyticAt ℂ (fun w : ℂ => w⁻¹) w0 := analyticAt_inv hw0
    have hcomp : MeromorphicAt ((fun z => ∑ a ∈ S, RS.principalPartAt R a z) ∘ (fun w : ℂ => w⁻¹)) w0 :=
      MeromorphicAt.comp_analyticAt (hRtailMero (w0⁻¹) (mem_univ _)) hAnalyticInv
    have hsq : MeromorphicAt (fun w : ℂ => -(w ^ 2)⁻¹) w0 := by
      have hp : AnalyticAt ℂ (fun w : ℂ => w ^ 2) w0 := by fun_prop
      exact hp.meromorphicAt.inv.neg
    have := hsq.mul hcomp
    simpa [Function.comp] using this
