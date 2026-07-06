import Jacobian.ResidueTheorem.RationalOnP1

open scoped ContDiff Manifold OnePoint Classical
open Set Filter Topology OnePoint RS.P1

noncomputable section

example (R : ℂ → ℂ) (hRmero : MeromorphicOn R Set.univ) (S : Finset ℂ)
    (haS : ∀ a : ℂ, a ∈ S ↔ meromorphicOrderAt R a < 0) :
    ∀ a : ℂ, 0 ≤ meromorphicOrderAt (fun z => R z - ∑ a' ∈ S, RS.principalPartAt R a' z) a := by
  have hAnalyticTailAt : ∀ (T : Finset ℂ) (a : ℂ), a ∉ T →
      AnalyticAt ℂ (fun z => ∑ a' ∈ T, RS.principalPartAt R a' z) a := by
    intro T a haT
    apply Finset.analyticAt_fun_sum
    intro a' ha'
    have hane : a ≠ a' := fun heq => haT (heq ▸ ha')
    have hmem : a ∈ ({a'} : Set ℂ)ᶜ := by simpa using hane
    exact RS.analyticOnNhd_principalPartAt a hmem
  intro a
  by_cases haS' : a ∈ S
  · have hsplit : (fun z => R z - ∑ a' ∈ S, RS.principalPartAt R a' z)
        = fun z => (R z - RS.principalPartAt R a z) -
          ∑ a' ∈ S.erase a, RS.principalPartAt R a' z := by
      funext z
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
      (meromorphicOrderAt_neg (f := fun z => ∑ a' ∈ S.erase a, RS.principalPartAt R a' z) (x := a)).symm
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
    have hsub_eq : (fun z => R z - ∑ a' ∈ S, RS.principalPartAt R a' z)
        = fun z => R z + (-(∑ a' ∈ S, RS.principalPartAt R a' z)) := by
      funext z; ring
    rw [hsub_eq]
    calc (0 : WithTop ℤ) = min 0 0 := by simp
      _ ≤ min (meromorphicOrderAt R a)
          (meromorphicOrderAt (fun z => -(∑ a' ∈ S, RS.principalPartAt R a' z)) a) := by
        apply min_le_min hRa
        rw [heq2]; exact hTa'
      _ ≤ _ := hkey
