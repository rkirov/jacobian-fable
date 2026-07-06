/-
Blueprint unit: meromorphic-trace. The planar trace atom `traceZk h k w` (trace of `h` along
`z ↦ z ^ k`), file 4 of the design's 6-file plan.
-/
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.CauchyIntegral
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
    by_cases hz : z ∈ s <;> simp [hz]
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
    rw [mul_pow, ← pow_mul, mul_comm i k, pow_mul, hζ.pow_eq_one, one_pow, one_mul, hw, id_eq]
  have hψ₁w₀pow : ψ₁ w₀ ^ k = w₀ := by
    have := hψ₁pow.self_of_nhds; rwa [id_eq] at this
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
          rw [hinj.ncard_image, Set.ncard_coe_finset, Finset.card_range]
        have hcard2 : ({z : ℂ | z ^ k = w}).ncard = k := RS.ncard_setOf_pow_eq hk hw0
        have heqset : (fun i => ψ i w) '' (↑(Finset.range k) : Set ℕ) = {z : ℂ | z ^ k = w} :=
          Set.eq_of_subset_of_ncard_le hsub (by rw [hcard1, hcard2]) (RS.setOf_pow_eq_finite hk w)
        rw [heqset]
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

/-! ### Meromorphy at the branch point (P5) -/

/-- `traceZk h k` is meromorphic at `0` whenever `h` is, via a norm/`zpow` growth bound on the
root-sum and Riemann's removable-singularity theorem
(`Complex.differentiableOn_update_limUnder_of_bddAbove`) — no monodromy, no convergent global
Laurent series needed for existence. -/
theorem meromorphicAt_traceZk (hh : MeromorphicAt h 0) (hk : k ≠ 0) :
    MeromorphicAt (traceZk h k) 0 := by
  classical
  by_cases hordtop : meromorphicOrderAt h 0 = ⊤
  · -- Degenerate case: `h` vanishes identically near `0`, hence so does `traceZk h k`.
    have hh0 : h =ᶠ[𝓝[≠] (0 : ℂ)] 0 := meromorphicOrderAt_eq_top_iff.1 hordtop
    obtain ⟨ρ, hρ0, hρsub⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp hh0)
    have htrace0 : traceZk h k =ᶠ[𝓝[≠] (0 : ℂ)] 0 := by
      have hballmem : Metric.ball (0 : ℂ) (ρ ^ k) ∈ 𝓝 (0 : ℂ) :=
        Metric.ball_mem_nhds 0 (pow_pos hρ0 k)
      filter_upwards [mem_nhdsWithin_of_mem_nhds hballmem, self_mem_nhdsWithin]
        with w hwball hwne
      have hw0 : w ≠ 0 := hwne
      show traceZk h k w = 0
      rw [traceZk_apply_of_ne_zero hk hw0]
      apply Finset.sum_eq_zero
      intro z hz
      rw [Set.Finite.mem_toFinset] at hz
      have hzpow : z ^ k = w := hz
      have hzlt : ‖z‖ < ρ := RS.norm_lt_of_pow_eq hk hρ0.le hzpow (mem_ball_zero_iff.mp hwball)
      have hzne : z ≠ 0 := by
        rintro rfl; rw [zero_pow hk] at hzpow; exact hw0 hzpow.symm
      exact hρsub z (mem_ball_zero_iff.mpr hzlt) hzne
    exact analyticAt_const.meromorphicAt.congr htrace0.symm
  · -- Main case: honest order presentation `h =ᶠ[𝓝[≠]0] z ↦ z ^ n₀ * u z`, `u` analytic, `u 0 ≠ 0`.
    obtain ⟨u, hu, hune, hu_eq⟩ := (meromorphicOrderAt_ne_top_iff hh).1 hordtop
    generalize hn₀_def : (meromorphicOrderAt h 0).untop₀ = n₀ at hu_eq
    have hu_eq' : h =ᶠ[𝓝[≠] (0 : ℂ)] fun z => z ^ n₀ * u z := by
      filter_upwards [hu_eq] with z hz
      rw [hz, smul_eq_mul, sub_zero]
    -- Euclidean split of `n₀` by `k`: `n₀ = k * q + r`.
    have hkpos : (0 : ℤ) < (k : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    obtain ⟨q, r, hn₀_eq⟩ : ∃ (q : ℤ) (r : ℕ), n₀ = (k : ℤ) * q + (r : ℤ) := by
      refine ⟨n₀ / (k : ℤ), (n₀ % (k : ℤ)).toNat, ?_⟩
      have hmod_nonneg : 0 ≤ n₀ % (k : ℤ) := Int.emod_nonneg n₀ (by omega)
      rw [Int.toNat_of_nonneg hmod_nonneg]
      exact (Int.mul_ediv_add_emod n₀ (k : ℤ)).symm
    -- `V w := w ^ (-q) * traceZk h k w`; unconditional identity off `0`.
    set V : ℂ → ℂ := fun w => w ^ (-q) * traceZk h k w with hV_def
    have hstep3 : traceZk h k =ᶠ[𝓝[≠] (0 : ℂ)] fun w => w ^ q * V w := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      have hw0 : w ≠ 0 := hw
      show traceZk h k w = w ^ q * (w ^ (-q) * traceZk h k w)
      rw [← mul_assoc, ← zpow_add₀ hw0, add_neg_cancel, zpow_zero, one_mul]
    -- A single radius `ρ` on which `h` is analytic, presented, and `u` is bounded.
    have hcomb : ∀ᶠ z in 𝓝[≠] (0 : ℂ), AnalyticAt ℂ h z ∧ h z = z ^ n₀ * u z :=
      hh.eventually_analyticAt.and hu_eq'
    obtain ⟨ρ₁, hρ₁0, hρ₁sub⟩ :=
      Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp hcomb)
    set Cu : ℝ := ‖u 0‖ + 1 with hCu_def
    have hCu_bound : ∀ᶠ z in 𝓝 (0 : ℂ), ‖u z‖ < Cu :=
      hu.continuousAt.norm.tendsto.eventually (Iio_mem_nhds (by rw [hCu_def]; linarith))
    obtain ⟨ρ₂, hρ₂0, hρ₂sub⟩ := Metric.eventually_nhds_iff_ball.mp hCu_bound
    set ρ : ℝ := min (min ρ₁ ρ₂) 1 with hρ_def
    have hρ0 : 0 < ρ := lt_min (lt_min hρ₁0 hρ₂0) one_pos
    have hρ1 : ρ ≤ 1 := min_le_right _ _
    have hρle1 : ρ ≤ ρ₁ := (min_le_left _ _).trans (min_le_left _ _)
    have hρle2 : ρ ≤ ρ₂ := (min_le_left _ _).trans (min_le_right _ _)
    have hh_an : AnalyticOnNhd ℂ h (Metric.ball (0 : ℂ) ρ \ {0}) := by
      rintro z ⟨hz1, hz2⟩
      exact (hρ₁sub z (Metric.ball_subset_ball hρle1 hz1) hz2).1
    have hh_pres : ∀ z, z ∈ Metric.ball (0 : ℂ) ρ → z ≠ 0 → h z = z ^ n₀ * u z := fun z hz1 hz2 =>
      (hρ₁sub z (Metric.ball_subset_ball hρle1 hz1) hz2).2
    have hu_bound : ∀ z ∈ Metric.ball (0 : ℂ) ρ, ‖u z‖ < Cu := fun z hz =>
      hρ₂sub z (Metric.ball_subset_ball hρle2 hz)
    set ρ' : ℝ := ρ ^ k with hρ'_def
    have hρ'0 : 0 < ρ' := pow_pos hρ0 k
    -- Step 4: `V` analytic on `ball 0 ρ' \ {0}`.
    have hVan : ∀ z ∈ Metric.ball (0 : ℂ) ρ' \ {0}, AnalyticAt ℂ V z := by
      rintro z ⟨hz1, hz2⟩
      have hzne : z ≠ 0 := hz2
      have htz : AnalyticAt ℂ (traceZk h k) z :=
        analyticAt_traceZk hk hρ0 hh_an hzne (mem_ball_zero_iff.mp hz1)
      have hzp : AnalyticAt ℂ (fun w : ℂ => w ^ (-q)) z := by
        simpa using (analyticAt_id (𝕜 := ℂ) (z := z)).zpow (n := -q) hzne
      exact hzp.mul htz
    -- Step 5: uniform norm bound on `V` over `ball 0 ρ' \ {0}`.
    have hVbound : ∀ w ∈ Metric.ball (0 : ℂ) ρ' \ {0}, ‖V w‖ ≤ (k : ℝ) * Cu := by
      rintro w ⟨hw1, hw2⟩
      have hw0 : w ≠ 0 := hw2
      have hwlt : ‖w‖ < ρ ^ k := by rwa [mem_ball_zero_iff, hρ'_def] at hw1
      have hbound_term : ∀ z ∈ (RS.setOf_pow_eq_finite hk w).toFinset, ‖h z‖ ≤ ‖w‖ ^ q * Cu := by
        intro z hz
        rw [Set.Finite.mem_toFinset] at hz
        have hzpow : z ^ k = w := hz
        have hzlt : ‖z‖ < ρ := RS.norm_lt_of_pow_eq hk hρ0.le hzpow hwlt
        have hzne : z ≠ 0 := by
          rintro rfl; rw [zero_pow hk] at hzpow; exact hw0 hzpow.symm
        have hzr : z ^ n₀ = w ^ q * z ^ (r : ℤ) := by
          have hexp : z ^ n₀ = z ^ ((k : ℤ) * q + (r : ℤ)) := by rw [← hn₀_eq]
          rw [hexp, zpow_add₀ hzne, zpow_mul, zpow_natCast, hzpow]
        rw [hh_pres z (mem_ball_zero_iff.mpr hzlt) hzne, hzr, zpow_natCast]
        calc ‖w ^ q * z ^ r * u z‖ = ‖w‖ ^ q * ‖z‖ ^ r * ‖u z‖ := by
                rw [norm_mul, norm_mul, norm_zpow, norm_pow]
          _ ≤ ‖w‖ ^ q * 1 * Cu := by
                have h1 : ‖z‖ ^ r ≤ 1 := pow_le_one₀ (norm_nonneg z) (by linarith [hzlt, hρ1])
                have h2 : (0 : ℝ) ≤ ‖w‖ ^ q := zpow_nonneg (norm_nonneg w) q
                have h3 : ‖u z‖ ≤ Cu := (hu_bound z (mem_ball_zero_iff.mpr hzlt)).le
                gcongr
          _ = ‖w‖ ^ q * Cu := by ring
      have hsum : ‖traceZk h k w‖ ≤ (RS.setOf_pow_eq_finite hk w).toFinset.card * (‖w‖ ^ q * Cu) := by
        rw [traceZk_apply_of_ne_zero hk hw0]
        calc ‖∑ z ∈ (RS.setOf_pow_eq_finite hk w).toFinset, h z‖
            ≤ ∑ z ∈ (RS.setOf_pow_eq_finite hk w).toFinset, ‖h z‖ := norm_sum_le _ _
          _ ≤ ∑ _z ∈ (RS.setOf_pow_eq_finite hk w).toFinset, ‖w‖ ^ q * Cu :=
              Finset.sum_le_sum hbound_term
          _ = (RS.setOf_pow_eq_finite hk w).toFinset.card * (‖w‖ ^ q * Cu) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : (RS.setOf_pow_eq_finite hk w).toFinset.card = k := by
        rw [← Set.ncard_eq_toFinset_card _ (RS.setOf_pow_eq_finite hk w), RS.ncard_setOf_pow_eq hk hw0]
      rw [hcard] at hsum
      have hwnorm0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
      show ‖w ^ (-q) * traceZk h k w‖ ≤ (k : ℝ) * Cu
      rw [norm_mul, norm_zpow]
      have hzp : (0 : ℝ) ≤ ‖w‖ ^ (-q) := zpow_nonneg (norm_nonneg w) (-q)
      have hcancel : ‖w‖ ^ (-q) * (‖w‖ ^ q * Cu) = Cu := by
        rw [← mul_assoc, ← zpow_add₀ hwnorm0, neg_add_cancel, zpow_zero, one_mul]
      nlinarith [hsum, hzp, mul_le_mul_of_nonneg_left hsum hzp]
    -- Step 6: Riemann's removable singularity theorem.
    have hd : DifferentiableOn ℂ V (Metric.ball (0 : ℂ) ρ' \ {0}) := fun z hz =>
      (hVan z hz).differentiableAt.differentiableWithinAt
    have hb : BddAbove ((norm ∘ V) '' (Metric.ball (0 : ℂ) ρ' \ {0})) :=
      ⟨(k : ℝ) * Cu, by rintro _ ⟨z, hz, rfl⟩; exact hVbound z hz⟩
    have hrep := Complex.differentiableOn_update_limUnder_of_bddAbove
      (Metric.ball_mem_nhds (0 : ℂ) hρ'0) hd hb
    have hanrep : AnalyticAt ℂ (Function.update V 0 (limUnder (𝓝[≠] (0 : ℂ)) V)) 0 :=
      (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).2 hrep 0
        (Metric.mem_ball_self hρ'0)
    have hupdate_eq :
        Function.update V 0 (limUnder (𝓝[≠] (0 : ℂ)) V) =ᶠ[𝓝[≠] (0 : ℂ)] V := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact Function.update_of_ne hz _ _
    have hVmero : MeromorphicAt V 0 := hanrep.meromorphicAt.congr hupdate_eq
    -- Step 7: assemble.
    have hzpow_mero : MeromorphicAt (fun w : ℂ => w ^ q) 0 := by
      simpa using (MeromorphicAt.id (0 : ℂ)).zpow q
    have hprod : MeromorphicAt (fun w => w ^ q * V w) 0 := hzpow_mero.mul hVmero
    exact hprod.congr hstep3.symm

/-! ### The Laurent-coefficient formula (P6) -/

/-- THE Laurent-coefficient formula for `traceZk` (P6). -/
theorem laurentCoeffAt_traceZk (hh : MeromorphicAt h 0) (hk : k ≠ 0) (m : ℤ) :
    laurentCoeffAt (traceZk h k) 0 m = (k : ℂ) * laurentCoeffAt h 0 (k * m) := by
  -- TODO(blocker): this coefficient identity is the one theorem in this unit not fully proved
  -- within the time budget. BLOCKED for >45 min on the following genuine mathematical gap (not
  -- a lemma-name lookup problem): P5's growth-bound/removable-singularity route establishes
  -- *existence* of the analytic repair `update V 0 c` of `V := (·)^(-q) * traceZk h k` (`q,r`
  -- the Euclidean split of `h`'s order `n₀` by `k`, `n₀ = k*q+r`), but does NOT compute its
  -- Taylor coefficients, which is what this theorem needs (via `laurentCoeffAt_of_eventuallyEq`
  -- applied to the presentation `traceZk h k =ᶠ[𝓝[≠]0] fun w => w^q * (update V 0 c) w`, reducing
  -- the goal to `taylorCoeffAt (update V 0 c) 0 m' = k * taylorCoeffAt u 0 (k*m' - r)` for
  -- `m' := (m - q).toNat`, `u` the unit factor of `h`'s order presentation).
  --   Two viable routes, NEITHER completed here:
  --   (a) design's original route (`docs/design/meromorphic-trace.md` §5 P6): expand `u` as a
  --       genuine convergent power series (`HasFPowerSeriesAt`), substitute termwise into the
  --       branch formula `V w = ∑_{i<k} (ψ_i w)^r u(ψ_i w)` (`ψ_i` the `k` root branches from
  --       P4), and collapse `∑_{i<k} ζ^{i·e}` to `k·[k ∣ e]` via `geom_sum_eq` (spike-verified,
  --       §9) — needs `tsum`/`HasSum` manipulation under the finite branch sum, not yet written.
  --   (b) a `tsum`-free alternative sketched during this session: apply the ALREADY-BUILT
  --       `AnalyticAt.exists_taylor_remainder hu M` (residue-calculus, `TaylorCoeff.lean`) to get
  --       an EXACT (not just eventual) global identity `u z = P(z) + z^M * ρ(z)` (`P` a finite
  --       polynomial, `ρ` analytic) for `M` large enough that `r + M > k*(m'+1)`; substitute into
  --       the branch formula to get an EXPLICIT finite-polynomial-in-`w` main term (via the same
  --       geometric-sum collapse, now on a FINITE index range `d < M`, no `tsum`) plus a genuinely
  --       negligible remainder term, then bound the remainder exactly as in P5's step 5 to show
  --       it does not affect the `m'`-th Taylor coefficient. This route stays inside the
  --       `dslope`/`taylorCoeffAt` finite-order idiom residue-calculus itself uses (no `tsum`
  --       anywhere in that unit either) but needs a second growth-bound argument analogous to
  --       P5's, which is itself ~100+ lines; not completed in the time budget.
  -- `traceZk`'s EXISTENCE as a meromorphic function at `0` (P5, `meromorphicAt_traceZk`) does NOT
  -- depend on this theorem and is fully proved above, admitted-goal-free. `resAt_traceZk` and
  -- `ordAt_traceZk_ge` (design §4.4, immediate corollaries of this formula) are also deferred as
  -- a consequence and are NOT stated below, to avoid building further API on an admitted goal.
  sorry

end RS.MTrace
