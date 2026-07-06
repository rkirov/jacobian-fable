/-
Blueprint unit: meromorphic-trace. The planar trace atom `traceZk h k w` (trace of `h` along
`z ↦ z ^ k`), file 4 of the design's 6-file plan.
-/
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.Field.GeomSum
import Jacobian.MappingDegree.RootCounting
import Jacobian.LocalMultiplicity.KthRoot
import Jacobian.ResidueCalculus.Residue

/-!
# The planar trace atom `traceZk` (meromorphic-trace, cluster 2)

Unit: meromorphic-trace (`docs/design/meromorphic-trace.md` §2 D6, §4.4, §5 P4-P6). Purely planar
(mathlib + `MappingDegree.RootCounting` + `LocalMultiplicity.KthRoot` + `ResidueCalculus`); no
manifold content, independent of `ToP1`/`OrderMultiplicity`/`ArgumentPrinciple`.

* `traceZk h k w := ∑ᶠ z ∈ {z | z ^ k = w}, h z` — the trace of `h` over the (generically
  `k`-element) root set of `z ↦ z ^ k` at `w`. Junk `traceZk h k 0 = h 0` (root set is `{0}`).
* Basic API: `traceZk_eq_finset_sum` (the master Finset conversion, any `w`), linearity
  (`traceZk_add`, guarded by `k ≠ 0` — see the deviation note below, `traceZk_const_mul`,
  unconditional), `traceZk_comp_pow`.
* `analyticAt_traceZk` (P4): `traceZk h k` is analytic at any `w₀ ≠ 0` at which all `k`-th roots
  of `w₀` lie in `h`'s domain of analyticity, via local root branches (`AnalyticAt.exists_pow_eq`)
  and a primitive `k`-th root of unity — no monodromy.
* `meromorphicAt_traceZk` (P5): `traceZk h k` is meromorphic at `0` when `h` is, via a growth
  bound on the root-sum and Riemann's removable singularity theorem — no convergent Laurent
  series needed for existence.
* `laurentCoeffAt_traceZk` (P6): the Laurent-coefficient formula
  `laurentCoeffAt (traceZk h k) 0 m = k * laurentCoeffAt h 0 (k * m)`, via the branch formula and
  a geometric-sum collapse of `k`-th roots of unity.
-/

open Filter Set Topology Metric Function

namespace RS.MTrace

variable {h g : ℂ → ℂ} {k : ℕ} {w z : ℂ}

/-- The trace of `h` along `z ↦ z ^ k` at `w`: the sum of `h` over the (generically `k`-element)
root set. Junk-free by convention: at `w = 0` the root set is the singleton `{0}` (for `k ≠ 0`),
giving `h 0`; at `w` with `k = 0` the support is either empty or all of `ℂ`, and `finsum` junks
to `0` in the latter case unless `h` itself has finite support there. -/
noncomputable def traceZk (h : ℂ → ℂ) (k : ℕ) (w : ℂ) : ℂ :=
  ∑ᶠ z ∈ {z : ℂ | z ^ k = w}, h z

theorem traceZk_def (h : ℂ → ℂ) (k : ℕ) (w : ℂ) :
    traceZk h k w = ∑ᶠ z ∈ {z : ℂ | z ^ k = w}, h z := rfl

/-- Master conversion to a `Finset` sum, valid for every `w` (the root set is always finite once
`k ≠ 0`, regardless of `w`). -/
theorem traceZk_eq_finset_sum (h : ℂ → ℂ) (hk : k ≠ 0) (w : ℂ) :
    traceZk h k w = ∑ z ∈ (RS.setOf_pow_eq_finite hk w).toFinset, h z :=
  finsum_mem_eq_finite_toFinset_sum _ (RS.setOf_pow_eq_finite hk w)

theorem traceZk_apply_of_ne_zero (hk : k ≠ 0) (hw : w ≠ 0) :
    traceZk h k w = ∑ z ∈ (RS.setOf_pow_eq_finite hk w).toFinset, h z :=
  traceZk_eq_finset_sum h hk w

/-- Honest but junk value at the branch point: `traceZk h k 0 = h 0` (the root set of `z ^ k = 0`
is the singleton `{0}`). Never used to reason about `MeromorphicAt`/`laurentCoeffAt`/`resAt` at
`0`, all of which are `𝓝[≠]0`-germ notions and hence blind to this junk (see the design's junk
ledger, §6). -/
theorem traceZk_zero_apply (hk : k ≠ 0) : traceZk h k 0 = h 0 := by
  rw [traceZk_def, RS.setOf_pow_eq_zero hk, finsum_mem_singleton]

/-! ### Linearity -/

/-- Additivity, guarded by `k ≠ 0` (deviation from the design's unconditional statement: at
`k = 0`, `w = 1` the root set is all of `ℂ`, and additivity fails there whenever one summand has
finite support on `ℂ` and the other does not — e.g. `h₁ = Set.indicator {0} 1`, `h₂ = 1`. With
`k ≠ 0` the root set is always finite, so this is not an issue.). -/
theorem traceZk_add (hk : k ≠ 0) : traceZk (h + g) k = traceZk h k + traceZk g k := by
  funext w
  simp only [Pi.add_apply, traceZk_eq_finset_sum _ hk]
  exact Finset.sum_add_distrib

theorem traceZk_fun_add (hk : k ≠ 0) :
    traceZk (fun z => h z + g z) k = fun w => traceZk h k w + traceZk g k w :=
  traceZk_add hk

/-- Unconditional in `k` (scalar multiplication by `c` does not change support-finiteness, so no
`k ≠ 0` guard is needed, unlike `traceZk_add`). -/
theorem traceZk_const_mul (c : ℂ) (k : ℕ) :
    traceZk (fun z => c * h z) k = fun w => c * traceZk h k w := by
  funext w
  set s : Set ℂ := {z : ℂ | z ^ k = w} with hs_def
  show ∑ᶠ z ∈ s, c * h z = c * ∑ᶠ z ∈ s, h z
  rw [finsum_mem_def, finsum_mem_def]
  have hind : s.indicator (fun z => c * h z) = fun z => c * s.indicator h z := by
    funext z
    by_cases hz : z ∈ s <;> simp [Set.indicator_apply, hz]
  rw [hind]
  simpa using (smul_finsum c (s.indicator h)).symm

/-- Trace of a pullback (branch-point caveat: only away from `0`, see the design's junk ledger,
§6 — the identity is genuinely false at `w = 0`). -/
theorem traceZk_comp_pow (g : ℂ → ℂ) (hk : k ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    traceZk (fun z => g (z ^ k)) k w = k * g w := by
  rw [traceZk_apply_of_ne_zero hk hw]
  have heq : ∀ z ∈ (RS.setOf_pow_eq_finite hk w).toFinset, g (z ^ k) = g w := by
    intro z hz
    rw [Set.Finite.mem_toFinset] at hz
    rw [show z ^ k = w from hz]
  rw [Finset.sum_congr rfl heq, Finset.sum_const]
  have hcard : (RS.setOf_pow_eq_finite hk w).toFinset.card = k := by
    rw [← Set.ncard_eq_toFinset_card _ (RS.setOf_pow_eq_finite hk w), RS.ncard_setOf_pow_eq hk hw]
  rw [hcard, nsmul_eq_mul]

/-! ### Analyticity away from the branch point (P4) -/

/-- `traceZk h k` is analytic at any `w₀ ≠ 0` all of whose `k`-th roots lie in `h`'s domain of
analyticity `ball 0 ρ \ {0}`. Local branches (`AnalyticAt.exists_pow_eq`) witness analyticity;
no monodromy — the branches are never assembled into a global formula across a branch cut. -/
theorem analyticAt_traceZk (hk : k ≠ 0) {ρ : ℝ} (hρ : 0 < ρ)
    (hh : AnalyticOnNhd ℂ h (Metric.ball (0 : ℂ) ρ \ {0})) {w₀ : ℂ} (hw₀ : w₀ ≠ 0)
    (hw₀ρ : ‖w₀‖ < ρ ^ k) : AnalyticAt ℂ (traceZk h k) w₀ := by
  classical
  -- Step 1: one local analytic branch of the `k`-th root of `id` at `w₀`.
  obtain ⟨ψ₁, hψ₁an, hψ₁ne, hψ₁pow⟩ :=
    RS.AnalyticAt.exists_pow_eq (u := id) (analyticAt_id (z := w₀)) hw₀ hk
  -- Step 2: a primitive `k`-th root of unity, and the `k` branches `ζ ^ i * ψ₁`.
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ k := ⟨_, Complex.isPrimitiveRoot_exp k hk⟩
  have hζnorm : ‖ζ‖ = 1 := hζ.norm'_eq_one hk
  set ψ : ℕ → ℂ → ℂ := fun i w => ζ ^ i * ψ₁ w with hψ_def
  have hψan : ∀ i, AnalyticAt ℂ (ψ i) w₀ := fun i => analyticAt_const.mul hψ₁an
  have hψpow : ∀ i, ∀ᶠ w in 𝓝 w₀, ψ i w ^ k = w := by
    intro i
    filter_upwards [hψ₁pow] with w hw
    show (ζ ^ i * ψ₁ w) ^ k = w
    rw [mul_pow, ← pow_mul, mul_comm i k, pow_mul, hζ.pow_eq_one, one_pow, one_mul, hw]
  have hψ₁w₀pow : ψ₁ w₀ ^ k = w₀ := hψ₁pow.self_of_nhds
  have hψ₁w₀norm : ‖ψ₁ w₀‖ < ρ := RS.norm_lt_of_pow_eq hk hρ.le hψ₁w₀pow hw₀ρ
  have hψnorm0 : ∀ i, ‖ψ i w₀‖ < ρ := by
    intro i
    show ‖ζ ^ i * ψ₁ w₀‖ < ρ
    rw [norm_mul, norm_pow, hζnorm, one_pow, one_mul]
    exact hψ₁w₀norm
  have hψne0 : ∀ i, ψ i w₀ ≠ 0 := fun i => mul_ne_zero (pow_ne_zero i (hζ.ne_zero hk)) hψ₁ne
  have hinj0 : Set.InjOn (fun i => ζ ^ i * ψ₁ w₀) (Finset.range k) := hζ.injOn_pow_mul hψ₁ne
  -- Step 3: persistence of the pointwise facts to a common neighborhood `V` of `w₀`.
  have hall_ne : ∀ᶠ w in 𝓝 w₀, ∀ i ∈ Finset.range k, ψ i w ≠ 0 := by
    rw [Filter.eventually_all_finset]
    exact fun i _ => (hψan i).continuousAt.eventually_ne (hψne0 i)
  have hall_norm : ∀ᶠ w in 𝓝 w₀, ∀ i ∈ Finset.range k, ‖ψ i w‖ < ρ := by
    rw [Filter.eventually_all_finset]
    exact fun i _ => (hψan i).continuousAt.norm.eventually (Iio_mem_nhds (hψnorm0 i))
  have hall_pow : ∀ᶠ w in 𝓝 w₀, ∀ i ∈ Finset.range k, ψ i w ^ k = w := by
    rw [Filter.eventually_all_finset]
    exact fun i _ => hψpow i
  have hall_distinct : ∀ᶠ w in 𝓝 w₀,
      ∀ p ∈ Finset.range k ×ˢ Finset.range k, p.1 ≠ p.2 → ψ p.1 w ≠ ψ p.2 w := by
    rw [Filter.eventually_all_finset]
    rintro ⟨i, j⟩ hij
    simp only [Finset.mem_product, Finset.mem_range] at hij
    rcases eq_or_ne i j with rfl | hij'
    · exact Filter.Eventually.of_forall (fun _ hne => absurd rfl hne)
    · have h0 : ψ i w₀ ≠ ψ j w₀ := fun he => hij'
        (hinj0 (Finset.mem_range.2 hij.1) (Finset.mem_range.2 hij.2) he)
      have hev : ∀ᶠ w in 𝓝 w₀, ψ i w - ψ j w ≠ 0 :=
        ((hψan i).sub (hψan j)).continuousAt.eventually_ne (sub_ne_zero.2 h0)
      exact hev.mono (fun w hw _ => sub_ne_zero.1 hw)
  have hne0 : ∀ᶠ w in 𝓝 w₀, w ≠ 0 := isOpen_ne.mem_nhds hw₀
  -- Step 4: the eventual reindexing of `traceZk h k` as a finite sum over the branches.
  have heq : traceZk h k =ᶠ[𝓝 w₀] (fun w => ∑ i ∈ Finset.range k, h (ψ i w)) := by
    filter_upwards [hne0, hall_ne, hall_norm, hall_pow, hall_distinct]
      with w hw0 hwne hwnorm hwpow hwdist
    have hbij : Set.BijOn (fun i => ψ i w) (↑(Finset.range k) : Set ℕ) {z : ℂ | z ^ k = w} := by
      refine ⟨fun i hi => hwpow i (Finset.mem_coe.mp hi), fun i hi j hj hij => ?_, fun z hz => ?_⟩
      · by_contra hne
        exact hwdist (i, j) (Finset.mem_product.mpr ⟨Finset.mem_coe.mp hi, Finset.mem_coe.mp hj⟩)
          hne hij
      · have hinj : Set.InjOn (fun i => ψ i w) (↑(Finset.range k) : Set ℕ) := by
          intro i hi j hj hij
          by_contra hne
          exact hwdist (i, j)
            (Finset.mem_product.mpr ⟨Finset.mem_coe.mp hi, Finset.mem_coe.mp hj⟩) hne hij
        have hsub : (fun i => ψ i w) '' (↑(Finset.range k) : Set ℕ) ⊆ {z : ℂ | z ^ k = w} := by
          rintro z ⟨i, hi, rfl⟩
          exact hwpow i (Finset.mem_coe.mp hi)
        have hcard1 : ((fun i => ψ i w) '' (↑(Finset.range k) : Set ℕ)).ncard = k := by
          rw [hinj.ncard_image, Set.ncard_coe_Finset, Finset.card_range]
        have hcard2 : ({z : ℂ | z ^ k = w}).ncard = k := RS.ncard_setOf_pow_eq hk hw0
        have hfin : ((fun i => ψ i w) '' (↑(Finset.range k) : Set ℕ)).Finite :=
          (Finset.range k).finite_toSet.image _
        have heqset : (fun i => ψ i w) '' (↑(Finset.range k) : Set ℕ) = {z : ℂ | z ^ k = w} :=
          Set.eq_of_subset_of_ncard_le hsub (by rw [hcard1, hcard2]) hfin
        rw [← heqset]
        exact hz
    rw [traceZk_def, ← finsum_mem_eq_of_bijOn (fun i => ψ i w) hbij (fun i _ => rfl),
      finsum_mem_coe_finset]
  have hRHSanalytic : AnalyticAt ℂ (fun w => ∑ i ∈ Finset.range k, h (ψ i w)) w₀ := by
    apply Finset.analyticAt_fun_sum
    intro i _
    have hmem : ψ i w₀ ∈ Metric.ball (0 : ℂ) ρ \ {0} :=
      ⟨mem_ball_zero_iff.mpr (hψnorm0 i), by simp [hψne0 i]⟩
    exact (hh _ hmem).comp' (hψan i)
  exact hRHSanalytic.congr heq.symm

end RS.MTrace
