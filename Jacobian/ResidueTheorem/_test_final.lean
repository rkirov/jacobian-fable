import Jacobian.ResidueTheorem.RationalOnP1

open scoped ContDiff Manifold OnePoint Classical
open Set Filter Topology OnePoint RS.P1

noncomputable section

namespace RS.P1

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

/-- Compat: residue vanishes off the pole set (the one-line gap canonical-forms's own design
flags for upstreaming). -/
theorem MFormData.resAt_eq_zero_of_ord_nonneg {θ : RS.MFormData (OnePoint ℂ)} {x : OnePoint ℂ}
    (h : 0 ≤ θ.ord x) : θ.resAt x = 0 :=
  RS.resAt_of_order_nonneg h

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
  set R_tail : ℂ → ℂ := fun z => ∑ a ∈ S, RS.principalPartAt R a z with hRtail_def
  have hRtailMero : MeromorphicOn R_tail Set.univ := by
    intro z0 _
    apply MeromorphicAt.fun_sum
    intro a _
    by_cases h : z0 = a
    · subst h; exact RS.meromorphicAt_principalPartAt
    · exact (RS.analyticOnNhd_principalPartAt z0 h).meromorphicAt
  have hRtailInv : MeromorphicOn (fun w => -(w ^ 2)⁻¹ * R_tail w⁻¹) Set.univ := by
    intro w0 _
    by_cases hw0 : w0 = 0
    · subst hw0
      have heq : (fun w => -(w ^ 2)⁻¹ * R_tail w⁻¹)
          = fun w => ∑ a ∈ S, (-(w ^ 2)⁻¹ * RS.principalPartAt R a w⁻¹) := by
        funext w; rw [hRtail_def]; simp [Finset.mul_sum]
      rw [heq]
      apply MeromorphicAt.fun_sum
      intro a _
      unfold RS.principalPartAt
      have heq2 : (fun w => -(w ^ 2)⁻¹ *
            ∑ k ∈ Finset.Icc (meromorphicOrderAt R a).untop₀ (-1),
              RS.laurentCoeffAt R a k * (w⁻¹ - a) ^ k)
          = fun w => ∑ k ∈ Finset.Icc (meromorphicOrderAt R a).untop₀ (-1),
            RS.laurentCoeffAt R a k * (-(w ^ 2)⁻¹ * (w⁻¹ - a) ^ k) := by
        funext w; rw [Finset.mul_sum]; congr 1; funext k; ring
      rw [heq2]
      apply MeromorphicAt.fun_sum
      intro k _
      exact (MeromorphicAt.const (RS.laurentCoeffAt R a k) 0).mul
        (meromorphicAt_neg_sq_inv_mul_sub_inv_zpow a k)
    · have hAnalyticInv : AnalyticAt ℂ (fun w : ℂ => w⁻¹) w0 := analyticAt_inv hw0
      have hcomp : MeromorphicAt ((fun z => ∑ a ∈ S, RS.principalPartAt R a z) ∘
          (fun w : ℂ => w⁻¹)) w0 :=
        MeromorphicAt.comp_analyticAt (hRtailMero (w0⁻¹) (mem_univ _)) hAnalyticInv
      have hsq : MeromorphicAt (fun w : ℂ => -(w ^ 2)⁻¹) w0 := by
        have hp : AnalyticAt ℂ (fun w : ℂ => w ^ 2) w0 := by fun_prop
        exact hp.meromorphicAt.inv.neg
      have hmul := hsq.mul hcomp
      exact hmul.congr (Filter.Eventually.of_forall fun w => by simp [Function.comp_def])
  set Θtail : RS.MFormData (OnePoint ℂ) := formOfCoeFn R_tail hRtailMero hRtailInv with hΘtail_def
  have hΘtail_coe : ∀ a : ℂ, Θtail.coeffAt ((a:ℂ):OnePoint ℂ) = R_tail := fun a => rfl
  have hΘtail_infty : Θtail.coeffAt (∞ : OnePoint ℂ) = fun w => -(w ^ 2)⁻¹ * R_tail w⁻¹ := rfl
  set θ' : RS.MFormData (OnePoint ℂ) := θ - Θtail with hθ'_def
  set R_mid : ℂ → ℂ := fun z => R z - R_tail z with hR_mid_def
  have hθ'_coe : ∀ a : ℂ, θ'.coeffAt ((a:ℂ):OnePoint ℂ) = R_mid := by
    intro a
    funext z
    show θ.coeffAt ((a:ℂ):OnePoint ℂ) z - Θtail.coeffAt ((a:ℂ):OnePoint ℂ) z = R_mid z
    rw [hRsame a, hΘtail_coe a]
  -- order ≥ 0 everywhere finite
  have hAnalyticTailAt : ∀ (T : Finset ℂ) (a : ℂ), a ∉ T →
      AnalyticAt ℂ (fun z => ∑ a' ∈ T, RS.principalPartAt R a' z) a := by
    intro T a haT
    apply Finset.analyticAt_fun_sum
    intro a' ha'
    have hane : a ≠ a' := fun heq => haT (heq ▸ ha')
    have hmem : a ∈ ({a'} : Set ℂ)ᶜ := by simpa using hane
    exact RS.analyticOnNhd_principalPartAt a hmem
  have hR_mid_ord : ∀ a : ℂ, 0 ≤ meromorphicOrderAt R_mid a := by
    intro a
    by_cases haS' : a ∈ S
    · have hsplit : R_mid
          = fun z => (R z - RS.principalPartAt R a z) -
            ∑ a' ∈ S.erase a, RS.principalPartAt R a' z := by
        funext z
        rw [hR_mid_def, hRtail_def]
        rw [← Finset.add_sum_erase S (RS.principalPartAt R · z) haS']
        ring
      rw [hsplit]
      have h1 : 0 ≤ meromorphicOrderAt (fun z => R z - RS.principalPartAt R a z) a :=
        RS.MeromorphicAt.orderAt_sub_principalPartAt_nonneg (hRmero a (mem_univ a))
      have h2 : AnalyticAt ℂ (fun z => ∑ a' ∈ S.erase a, RS.principalPartAt R a' z) a :=
        hAnalyticTailAt (S.erase a) a (Finset.notMem_erase a S)
      have h2' : 0 ≤ meromorphicOrderAt (fun z => ∑ a' ∈ S.erase a, RS.principalPartAt R a' z) a :=
        h2.meromorphicOrderAt_nonneg
      have hmero1 : MeromorphicAt (fun z => R z - RS.principalPartAt R a z) a :=
        (hRmero a (mem_univ a)).sub RS.meromorphicAt_principalPartAt
      have hmero2 : MeromorphicAt (fun z => -(∑ a' ∈ S.erase a, RS.principalPartAt R a' z)) a :=
        h2.meromorphicAt.neg
      have hkey := meromorphicOrderAt_add hmero1 hmero2
      have heq2 : meromorphicOrderAt (fun z => -(∑ a' ∈ S.erase a, RS.principalPartAt R a' z)) a
          = meromorphicOrderAt (fun z => ∑ a' ∈ S.erase a, RS.principalPartAt R a' z) a :=
        (meromorphicOrderAt_neg (f := fun z => ∑ a' ∈ S.erase a, RS.principalPartAt R a' z)
          (x := a)).symm
      have hsub_eq : (fun z => (R z - RS.principalPartAt R a z) -
          ∑ a' ∈ S.erase a, RS.principalPartAt R a' z)
          = fun z => (R z - RS.principalPartAt R a z) +
            (-(∑ a' ∈ S.erase a, RS.principalPartAt R a' z)) := by
        funext z; ring
      rw [hsub_eq]
      calc (0 : WithTop ℤ) = min 0 0 := by simp
        _ ≤ min (meromorphicOrderAt (fun z => R z - RS.principalPartAt R a z) a)
            (meromorphicOrderAt (fun z => -(∑ a' ∈ S.erase a, RS.principalPartAt R a' z)) a) := by
          apply min_le_min h1
          rw [heq2]; exact h2'
        _ ≤ _ := hkey
    · have hRa : 0 ≤ meromorphicOrderAt R a :=
        not_lt.mp (fun hlt => haS' ((haS a).mpr hlt))
      have hTa : AnalyticAt ℂ (fun z => ∑ a' ∈ S, RS.principalPartAt R a' z) a :=
        hAnalyticTailAt S a haS'
      have hTa' : 0 ≤ meromorphicOrderAt (fun z => ∑ a' ∈ S, RS.principalPartAt R a' z) a :=
        hTa.meromorphicOrderAt_nonneg
      have hmero1 : MeromorphicAt R a := hRmero a (mem_univ a)
      have hmero2 : MeromorphicAt (fun z => -(∑ a' ∈ S, RS.principalPartAt R a' z)) a :=
        hTa.meromorphicAt.neg
      have hkey := meromorphicOrderAt_add hmero1 hmero2
      have heq2 : meromorphicOrderAt (fun z => -(∑ a' ∈ S, RS.principalPartAt R a' z)) a
          = meromorphicOrderAt (fun z => ∑ a' ∈ S, RS.principalPartAt R a' z) a :=
        (meromorphicOrderAt_neg (f := fun z => ∑ a' ∈ S, RS.principalPartAt R a' z) (x := a)).symm
      have hsub_eq : R_mid = fun z => R z + (-(∑ a' ∈ S, RS.principalPartAt R a' z)) := by
        rw [hR_mid_def, hRtail_def]; funext z; ring
      rw [hsub_eq]
      calc (0 : WithTop ℤ) = min 0 0 := by simp
        _ ≤ min (meromorphicOrderAt R a)
            (meromorphicOrderAt (fun z => -(∑ a' ∈ S, RS.principalPartAt R a' z)) a) := by
          apply min_le_min hRa
          rw [heq2]; exact hTa'
        _ ≤ _ := hkey
  have hR_mid_mero : ∀ a : ℂ, MeromorphicAt R_mid a := fun a =>
    (hRmero a (mem_univ a)).sub (hRtailMero a (mem_univ a))
  have hR_mid_diff : Differentiable ℂ R_mid := by
    intro a
    exact ((hR_mid_mero a).analyticAt_of_order_nonneg (hR_mid_ord a)).differentiableAt
  -- θ'.resAt ∞ = 0
  have hθ'_ord_infty_zero : θ'.resAt (∞ : OnePoint ℂ) = 0 := by
    show RS.resAt (θ'.coeffAt (∞ : OnePoint ℂ)) (chartAt ℂ (∞:OnePoint ℂ) (∞:OnePoint ℂ)) = 0
    rw [chartAt_infty, invChart_apply_infty]
    have hcongr : θ'.coeffAt (∞ : OnePoint ℂ) =ᶠ[𝓝[≠] (0:ℂ)]
        fun z => -(z ^ 2)⁻¹ * R_mid z⁻¹ := by
      have := coeffAt_infty_eventuallyEq θ'
      rwa [hθ'_coe 0] at this
    rw [RS.resAt_congr hcongr]
    apply resAt_neg_sq_inv_mul_comp_inv_eq_zero hR_mid_diff
    have hcongr' : (fun z => -(z ^ 2)⁻¹ * R_mid z⁻¹) =ᶠ[𝓝[≠] (0:ℂ)] θ'.coeffAt (∞ : OnePoint ℂ) :=
      hcongr.symm
    exact MeromorphicAt.congr (θ'.meromorphicAt_coeffAt (∞ : OnePoint ℂ)) hcongr'
  sorry

end RS.P1
