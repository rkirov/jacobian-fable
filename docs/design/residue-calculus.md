# Design: residue-calculus (`Jacobian/ResidueCalculus/`)

Blueprint unit **residue-calculus** (Builds on: holomorphic-forms — but see "Dependencies" below:
the Lean code is *purely planar* and imports nothing from `Jacobian/Forms`). Provides: Laurent
coefficients and principal parts of planar meromorphic germs, the residue functional `resAt`,
the residue-of-a-derivative and log-derivative lemmas, the **change-of-variables theorem**
(chart invariance of residues of 1-form integrands), the **circle-integral bridge**
`∮ = 2πi·res`, Mittag-Leffler principal-part data, and the ℂ-linear-functional packaging of
Laurent coefficients on meromorphic germs. References: Forster §17.1–17.2 (book 132–133 = PDF
138–139; read), Forster Thm 10.21 context (consumed later, not here); Miranda Ch. VI §3 "The
Residue Map" (book 186–187 = PDF 198–199; read — pins the pairing shape
`Res_p(fω) = Σ_n c_n·a_{−1−n}`, a finite convolution at index −1).

⚠ **Routing (blueprint warning, repeated here so no builder mis-scopes):** this unit is the
LOCAL, planar input. The residue **theorem** `∑Res = 0` (Stokes) lives in residue-theorem /
planar-stokes-atoms; the residue **functional** `H¹(Ω) → ℂ` of Serre duality lives in
serre-duality-cech/tails. Neither is built here. What IS built here is everything both of them
consume pointwise: `resAt` and its algebra, chart invariance, and the single honest integral
identity on a small circle (the "integration atom" the blueprint budgets for).

Everything below verified against the pinned mathlib `548398201a64f3a5127d90d83945278cfe38cac4`
by reading source; **file:line refer to `.lake/packages/mathlib/`**. Spike report in §8.

---

## 1. Mathlib at the pin: what exists, what is absent

Present (all read in source, names exact):

- `MeromorphicAt f x` (`Analysis/Meromorphic/Basic.lean:36`), closure lemmas
  `MeromorphicAt.add/smul/mul/sum/neg/sub/inv/zpow` (`:74–321`), `AnalyticAt.meromorphicAt`
  (`:40`), `MeromorphicAt.deriv` (`:372`, needs `[CompleteSpace E]` — ℂ fine),
  `meromorphicAt_congr {h : f =ᶠ[𝓝[≠] x] g} : MeromorphicAt f x ↔ MeromorphicAt g x` (`:265`,
  also usable as `MeromorphicAt.meromorphicAt_congr`),
  `meromorphicAt_comp_iff_of_deriv_ne_zero` (`:458`).
- `meromorphicOrderAt` (`Order.lean:47`; junk `0` if not meromorphic), factorization
  `meromorphicOrderAt_eq_int_iff` (`:94`), `meromorphicOrderAt_ne_top_iff` (`:126`),
  `meromorphicOrderAt_eq_top_iff : … ↔ ∀ᶠ z in 𝓝[≠] x, f z = 0` (`:64`),
  `meromorphicOrderAt_congr`, additivity `meromorphicOrderAt_smul/_mul` (`:407/:429`),
  `meromorphicOrderAt_zpow/_inv` (`:481/:510`),
  **`meromorphicOrderAt_zpow_id_sub_const : meromorphicOrderAt ((· - x) ^ n) x = n`** (`:365`),
  `meromorphicOrderAt_id_sub_const = 1` (`:376`),
  `AnalyticAt.meromorphicOrderAt_eq` (analytic↔meromorphic order bridge, `:279`),
  `AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero` (`Analysis/Analytic/Order.lean:305`).
- **`meromorphicTrailingCoeffAt`** (`TrailingCoefficient.lean:36`) — leading Laurent coefficient
  only, defined by `.choose` on the order presentation. Read in full. We REUSE: its
  characterization pattern (`AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE`
  `:90`), its congruence lemma (`meromorphicTrailingCoeffAt_congr_nhdsNE` `:184`), its
  arithmetic (`_smul/_mul/_zpow/_inv/_add_eq_left_of_lt/_add_eq_add`), and — decisively — its
  *definition style* (dite + `Exists.choose`), which our `laurentCoeffAt` extends from the
  leading coefficient to all coefficients.
- **`dslope`** (`Analysis/Calculus/DSlope.lean`): `dslope_same` (= `deriv` at the point, `:39`),
  `dslope_of_ne` (`:45`), `sub_smul_dslope` (`:67`), **`dslope_sub_smul_of_ne
  (f) (h : b ≠ a) : dslope (fun x => (x - a) • f x) a b = f b`** (`:70`),
  `sub_smul_dslope_of_zero` (`:145`), **`pow_sub_smul_iterate_dslope_of_zero (n)
  (hf : ∀ k < n, (Function.swap dslope a)^[k] f a = 0) (b) :
  (b - a) ^ n • (Function.swap dslope a)^[n] f b = f b`** (`:149`) — the exact
  Taylor-remainder-factorization engine, pointwise, hypothesis-free on analyticity.
- `HasFPowerSeriesAt.has_fpower_series_dslope_fslope` / `has_fpower_series_iterate_dslope_fslope`
  (`Analysis/Analytic/IsolatedZeros.lean:78/:91`, namespace `HasFPowerSeriesAt`) — dslope
  iterates of analytic functions are analytic; `FormalMultilinearSeries.fslope`
  (`Analysis/Calculus/FormalMultilinearSeries.lean:343`), `coeff_iterate_fslope`.
  `AnalyticAt.map_nhdsNE` (`IsolatedZeros.lean:335`).
- `Filter.EventuallyEq.nhdsNE_deriv (h : f₁ =ᶠ[𝓝[≠] x] f) : deriv f₁ =ᶠ[𝓝[≠] x] deriv f`
  (`Analysis/Calculus/Deriv/Basic.lean:659`);
  `ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE` (`Topology/Separation/Hausdorff.lean:649`);
  `HasDerivAt.tendsto_nhdsNE (h : HasDerivAt f f' x) (hf' : f' ≠ 0) :
  Tendsto f (𝓝[≠] x) (𝓝[≠] f x)` (`Analysis/Calculus/Deriv/Inverse.lean:107`);
  `hasDerivAt_zpow (m : ℤ) (x) (h : x ≠ 0 ∨ 0 ≤ m)` (`Analysis/Calculus/Deriv/ZPow.lean:61`);
  `AnalyticAt.eventually_analyticAt` (`Analysis/Analytic/ChangeOrigin.lean:377`).
- **Circle integrals** (`MeasureTheory/Integral/CircleIntegral.lean`, namespace
  `circleIntegral` unless noted):
  `integral_sub_zpow_of_ne (hn : n ≠ -1) (c w R) : (∮ z in C(c, R), (z - w) ^ n) = 0` (`:539`);
  `integral_sub_center_inv (c) (hR : R ≠ 0) : (∮ z in C(c, R), (z - c)⁻¹) = 2 * π * I` (`:505`);
  `integral_sub_inv_of_mem_ball (hw : w ∈ ball c R)` (`:671`); `integral_congr (hR : 0 ≤ R)
  (h : EqOn f g (sphere c R))` (`:398`); `integral_add/integral_sub/integral_fun_sum`
  (`:424/:429/:434`); `integral_const_mul` (`:500`); `integral_undef` (`:420`);
  root-level `circleIntegrable_sub_zpow_iff : CircleIntegrable ((· - w) ^ n) c R ↔
  R = 0 ∨ 0 ≤ n ∨ w ∉ sphere c |R|` (`:317`); `CircleIntegrable.add/.sum/.fun_sum` (`:197–217`);
  `ContinuousOn.circleIntegrable (hR : 0 ≤ R)` (`:310`);
  `circleIntegral_congr_codiscreteWithin` (`:403`).
- **Cauchy machinery** (`Analysis/Complex/CauchyIntegral.lean`, namespace `Complex`):
  **`circleIntegral_eq_zero_of_differentiable_on_off_countable {R} (h0 : 0 ≤ R) (hs :
  s.Countable) (hc : ContinuousOn f (closedBall c R)) (hd : ∀ z ∈ ball c R \ s,
  DifferentiableAt ℂ f z) : (∮ z in C(c, R), f z) = 0`** (`:441`), clean variant
  `DiffContOnCl.circleIntegral_eq_zero` (`:460`); **annulus deformation
  `circleIntegral_eq_of_differentiable_on_annulus_off_countable (h0 : 0 < r) (hle : r ≤ R)
  (hs : s.Countable) (hc : ContinuousOn f (closedBall c R \ ball c r)) (hd : ∀ z ∈
  (ball c R \ closedBall c r) \ s, DifferentiableAt ℂ f z) :
  (∮ z in C(c, R), f z) = ∮ z in C(c, r), f z`** (inventory §5a, re-verified).
- `Filter.Germ` with `Module R (Germ l M)` (`Order/Filter/Germ/Basic.lean:654`) and
  `Germ.liftOn` (`:176`). `Finsupp.onFinset`, `Finsupp.supported` (standard).

**Absent (inventory §5c–d, re-verified by grep at the pin):** any analytic Laurent theory,
`principalPart` in any form, residues (all "residue" hits are algebra), argument principle,
winding numbers. `FactorizedRational.lean` (global zero/pole factorization on a set) is NOT
needed here — our objects are single-point germs and `meromorphicOrderAt_eq_int_iff` is the
right atom; do not import it.

---

## 2. Core definitional choices (fixed by this doc)

Junk convention (uniform): **every functional below returns `0`** when `f` is not meromorphic
at the point, and on the `meromorphicOrderAt = ⊤` (locally-≡0) germ. All honest statements are
guarded by `MeromorphicAt`; all definitions are stated for bare `f : ℂ → ℂ`. Everything is
invariant under `=ᶠ[𝓝[≠] z₀]` (congr lemmas provided), matching CC3's codiscrete-germ
philosophy and CC8's germ cochains.

### 2.1 The Taylor-coefficient extractor (dslope iterates — no `iteratedDeriv`, no factorials)

```lean
/-- The `j`-th Taylor coefficient of `g` at `z₀`, extracted by iterated difference quotients.
For `g` analytic at `z₀` with power series `p` this equals `p.coeff j`. Junk for non-smooth
`g` (whatever the iterated `dslope` evaluates to). -/
noncomputable def taylorCoeffAt (g : ℂ → ℂ) (z₀ : ℂ) (j : ℕ) : ℂ :=
  (Function.swap dslope z₀)^[j] g z₀
```

Rationale: `dslope` is mathlib's own device for exactly this (IsolatedZeros is built on it);
the iterates of an analytic germ are analytic (`has_fpower_series_iterate_dslope_fslope`), the
shift identities are *pointwise* (`dslope_sub_smul_of_ne`,
`pow_sub_smul_iterate_dslope_of_zero`), and no factorial/`iteratedDeriv` bookkeeping ever
appears. The power-series bridge (`taylorCoeffAt g z₀ j = p.coeff j`) is provided as a lemma,
not used internally.

### 2.2 Laurent coefficients (THE definition of the unit)

```lean
/-- The `k`-th Laurent coefficient of `f` at `z₀` (coefficient of `(z - z₀)^k`).
Defined through the order presentation `f =ᶠ[𝓝[≠] z₀] (· - z₀)^n • g`, `g` analytic,
`g z₀ ≠ 0`, `n = meromorphicOrderAt f z₀`: the coefficient is the `(k - n)`-th Taylor
coefficient of `g`. Junk `0` if `f` is not meromorphic at `z₀`, on the locally-zero germ
(order `⊤`), and for `k <` order. -/
noncomputable def laurentCoeffAt (f : ℂ → ℂ) (z₀ : ℂ) (k : ℤ) : ℂ := by
  by_cases h₁ : MeromorphicAt f z₀
  · by_cases h₂ : meromorphicOrderAt f z₀ = ⊤
    · exact 0
    · exact if (meromorphicOrderAt f z₀).untop₀ ≤ k then
        taylorCoeffAt (((meromorphicOrderAt_ne_top_iff h₁).1 h₂).choose) z₀
          (k - (meromorphicOrderAt f z₀).untop₀).toNat
      else 0
  · exact 0
```

Same `.choose` on the same existential as mathlib's `meromorphicTrailingCoeffAt` — deliberately,
so `laurentCoeffAt f z₀ n = meromorphicTrailingCoeffAt f z₀` at the order is near-definitional.
Nobody ever unfolds this definition except to prove the single characterization lemma §4.2
(`laurentCoeffAt_of_eventuallyEq`); ALL other lemmas go through that.

### 2.3 Residue and principal part

```lean
/-- The residue of `f` at `z₀`: the `(-1)`-st Laurent coefficient. Purely algebraic;
the circle-integral characterization is `RS.circleIntegral_eq_two_pi_I_mul_resAt`. -/
noncomputable def resAt (f : ℂ → ℂ) (z₀ : ℂ) : ℂ := laurentCoeffAt f z₀ (-1)

/-- The principal part of `f` at `z₀`: the finite sum of the negative-exponent Laurent terms.
An honest function `ℂ → ℂ`, analytic on `ℂ \ {z₀}`, meromorphic at `z₀`. Zero (empty sum)
when `f` is analytic-after-repair at `z₀`, not meromorphic there, or locally `0`. -/
noncomputable def principalPartAt (f : ℂ → ℂ) (z₀ : ℂ) : ℂ → ℂ := fun z =>
  ∑ k ∈ Finset.Icc (meromorphicOrderAt f z₀).untop₀ (-1),
    laurentCoeffAt f z₀ k * (z - z₀) ^ k
```

(`Icc` is empty in every junk case: order `⊤` and non-meromorphic give `untop₀ = 0`;
order `≥ 0` gives `untop₀ ≥ 0`.) "`f − principalPartAt` is analytic" is stated precisely as
the decomposition `f =ᶠ[𝓝[≠] z₀] principalPartAt f z₀ + h`, `h` analytic at `z₀` (§4.4) —
the `=ᶠ[𝓝[≠]]` form, as CC3 does; a `MeromorphicNFAt`-style variant is a corollary
(`0 ≤ meromorphicOrderAt (f - principalPartAt f z₀) z₀`).

### 2.4 What is deliberately NOT defined here

No meromorphic 1-forms (canonical-forms), no surface-level residue (residue-theorem defines
`Res_p(ω) := resAt` of the chart integrand — well-defined BY our change-of-variables theorem),
no tail spaces `T[D]` (laurent-tails, CC8), no winding numbers, no general contour integrals.

---

## 3. File plan

```
Jacobian/ResidueCalculus.lean                  -- unit root: imports all, 5–15 line API docstring
Jacobian/ResidueCalculus/TaylorCoeff.lean      -- taylorCoeffAt: dslope-iterate API (analytic layer)
Jacobian/ResidueCalculus/LaurentCoeff.lean     -- laurentCoeffAt: characterization, congr, algebra
Jacobian/ResidueCalculus/PrincipalPart.lean    -- principalPartAt, decomposition, uniqueness
Jacobian/ResidueCalculus/Residue.lean          -- resAt: algebra, deriv-lemma, log-deriv, products
Jacobian/ResidueCalculus/ChangeOfVariables.lean-- resAt ((f∘φ)·φ') = resAt f  (chart invariance)
Jacobian/ResidueCalculus/IntegralBridge.lean   -- ∮_{C(z₀,ρ)} f = 2πi · resAt f z₀
Jacobian/ResidueCalculus/GermFunctionals.lean  -- meromorphic germ submodule; laurentCoeffAt as →ₗ[ℂ]
Jacobian/ResidueCalculus/MittagLeffler.lean    -- PrincipalPartData, Realizes, basic ops
```

Imports (targeted; spike-verified spine):
`TaylorCoeff`: `Mathlib.Analysis.Analytic.IsolatedZeros`, `Mathlib.Analysis.Calculus.DSlope`.
`LaurentCoeff` adds `Mathlib.Analysis.Meromorphic.TrailingCoefficient` (pulls in
`Meromorphic.Order`). `Residue` adds `Mathlib.Analysis.Calculus.Deriv.ZPow`.
`ChangeOfVariables` adds `Mathlib.Analysis.Calculus.Deriv.Inverse` (for
`HasDerivAt.tendsto_nhdsNE`). `IntegralBridge` adds `Mathlib.Analysis.Complex.CauchyIntegral`
(which brings `MeasureTheory.Integral.CircleIntegral`). `GermFunctionals` adds
`Mathlib.Order.Filter.Germ.Basic`. `MittagLeffler` adds `Mathlib.Data.Finsupp.Basic` (or
`Mathlib.LinearAlgebra.Finsupp.Supported` if the `LaurentTail` submodule spelling is used).
NO manifold imports anywhere; NO import of `Jacobian/Forms` (see §9 note on the blueprint edge).

Standing header for every file:

```lean
open Filter Topology Metric Function
namespace RS
variable {f g h : ℂ → ℂ} {z₀ w₀ : ℂ} {k n : ℤ}
```

---

## 4. Exports (exact signatures) and proof plans

### 4.1 `TaylorCoeff.lean` — the analytic layer

```lean
noncomputable def taylorCoeffAt (g : ℂ → ℂ) (z₀ : ℂ) (j : ℕ) : ℂ    -- §2.1

@[simp] theorem taylorCoeffAt_zero_apply : taylorCoeffAt g z₀ 0 = g z₀   -- rfl

/-- dslope iterates of analytic germs are analytic. -/
theorem AnalyticAt.iterate_dslope (hg : AnalyticAt ℂ g z₀) (j : ℕ) :
    AnalyticAt ℂ ((Function.swap dslope z₀)^[j] g) z₀
  -- obtain ⟨p, hp⟩ := hg; exact ⟨_, hp.has_fpower_series_iterate_dslope_fslope j⟩

/-- Germ invariance: `taylorCoeffAt` only depends on the `𝓝 z₀`-germ. -/
theorem taylorCoeffAt_congr (hfg : f =ᶠ[𝓝 z₀] g) (j : ℕ) :
    taylorCoeffAt f z₀ j = taylorCoeffAt g z₀ j
  -- Induction via: dslope f z₀ =ᶠ[𝓝 z₀] dslope g z₀ when f =ᶠ[𝓝 z₀] g
  -- (off z₀: dslope_of_ne + slope congruence; at z₀: dslope_same + EventuallyEq.deriv_eq).
  -- Prove the helper `Filter.EventuallyEq.dslope (hfg) : dslope f z₀ =ᶠ[𝓝 z₀] dslope g z₀`.

-- ℂ-linearity on differentiable-at germs (dslope is linear pointwise given DifferentiableAt
-- at the base point for the `dslope_same` value; iterate via AnalyticAt.iterate_dslope):
theorem taylorCoeffAt_add (hf : AnalyticAt ℂ f z₀) (hg : AnalyticAt ℂ g z₀) (j : ℕ) :
    taylorCoeffAt (f + g) z₀ j = taylorCoeffAt f z₀ j + taylorCoeffAt g z₀ j
theorem taylorCoeffAt_const_mul (c : ℂ) (j : ℕ) :
    taylorCoeffAt (fun z => c * g z) z₀ j = c * taylorCoeffAt g z₀ j
  -- unconditional: dslope commutes with c • · pointwise (slope_smul; deriv_const_mul needs
  -- DifferentiableAt only for the value at z₀ — if friction, add (hg : AnalyticAt) hypothesis;
  -- consumers always have it
@[simp] theorem taylorCoeffAt_const (c : ℂ) (j : ℕ) :
    taylorCoeffAt (fun _ => c) z₀ j = if j = 0 then c else 0

/-- Shift: prepending a monomial factor shifts Taylor coefficients. THE workhorse identity. -/
theorem taylorCoeffAt_sub_pow_mul (hg : AnalyticAt ℂ g z₀) (d : ℕ) (j : ℕ) :
    taylorCoeffAt (fun z => (z - z₀) ^ d * g z) z₀ j
      = if j < d then 0 else taylorCoeffAt g z₀ (j - d)
  -- Induction on d. Step: dslope (fun z => (z - z₀) * ((z-z₀)^d * g z)) z₀ =ᶠ[𝓝 z₀]
  -- (fun z => (z-z₀)^d * g z): off z₀ this is dslope_sub_smul_of_ne (smul = mul in ℂ);
  -- at z₀ both sides evaluate (dslope_same; deriv of (·-z₀)·F at z₀ = F z₀ by product rule,
  -- F differentiable at z₀). Then taylorCoeffAt_congr. The `j < d` branch: value at z₀ of
  -- (·-z₀)^d·g with d > 0 is 0, and iterates keep a monomial factor.
@[simp] theorem taylorCoeffAt_monomial (d j : ℕ) :
    taylorCoeffAt (fun z => (z - z₀) ^ d) z₀ j = if j = d then 1 else 0

/-- Bridge to power series (for consumers that hold a `HasFPowerSeriesAt`; not used internally). -/
theorem HasFPowerSeriesAt.taylorCoeffAt_eq {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt g p z₀) (j : ℕ) : taylorCoeffAt g z₀ j = p.coeff j
  -- (has_fpower_series_iterate_dslope_fslope j hp).coeff_zero + coeff_iterate_fslope

/-- Taylor remainder factorization, EXACT (pointwise): subtracting the degree-< m Taylor
polynomial leaves an honest `(z - z₀)^m`-divisible function with analytic quotient. -/
theorem AnalyticAt.exists_taylor_remainder (hg : AnalyticAt ℂ g z₀) (m : ℕ) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r z₀ ∧ (∀ j, taylorCoeffAt r z₀ j = taylorCoeffAt g z₀ (j + m)) ∧
      ∀ z, g z = (∑ d ∈ Finset.range m, taylorCoeffAt g z₀ d * (z - z₀) ^ d)
        + (z - z₀) ^ m * r z
  -- G := g - Taylor-poly has taylorCoeffAt G j = 0 for j < m (linearity + monomial), so
  -- pow_sub_smul_iterate_dslope_of_zero m gives (z-z₀)^m • (swap dslope z₀)^[m] G z = G z
  -- POINTWISE; r := (swap dslope z₀)^[m] G, analytic by AnalyticAt.iterate_dslope;
  -- coefficient identity: iterating the same shift lemma backwards (or: taylorCoeffAt r j =
  -- taylorCoeffAt ((·-z₀)^m * r) (j+m) = taylorCoeffAt G (j+m) = taylorCoeffAt g (j+m)).
```

### 4.2 `LaurentCoeff.lean` — characterization and algebra

```lean
noncomputable def laurentCoeffAt (f : ℂ → ℂ) (z₀ : ℂ) (k : ℤ) : ℂ     -- §2.2

-- Junk API:
@[simp] theorem laurentCoeffAt_of_not_meromorphicAt (h : ¬ MeromorphicAt f z₀) (k) :
    laurentCoeffAt f z₀ k = 0
@[simp] theorem laurentCoeffAt_of_order_eq_top (h : meromorphicOrderAt f z₀ = ⊤) (k) :
    laurentCoeffAt f z₀ k = 0
theorem laurentCoeffAt_eq_zero_of_lt_order (h : (k : WithTop ℤ) < meromorphicOrderAt f z₀) :
    laurentCoeffAt f z₀ k = 0

/-- THE characterization (workhorse; the only lemma that unfolds the definition).
Any zpow-presentation computes every Laurent coefficient — `n` need NOT be the order and
`g z₀ = 0` is allowed. -/
theorem laurentCoeffAt_of_eventuallyEq {n : ℤ} (hg : AnalyticAt ℂ g z₀)
    (hfg : f =ᶠ[𝓝[≠] z₀] fun z => (z - z₀) ^ n * g z) (k : ℤ) :
    laurentCoeffAt f z₀ k = if n ≤ k then taylorCoeffAt g z₀ (k - n).toNat else 0

/-- Congruence: Laurent coefficients live on the punctured germ. -/
theorem laurentCoeffAt_congr (hfg : f =ᶠ[𝓝[≠] z₀] g) (k) :
    laurentCoeffAt f z₀ k = laurentCoeffAt g z₀ k

-- Compatibility with the mathlib leading coefficient (CC3-facing):
theorem laurentCoeffAt_order (hf : MeromorphicAt f z₀) (h : meromorphicOrderAt f z₀ ≠ ⊤) :
    laurentCoeffAt f z₀ (meromorphicOrderAt f z₀).untop₀ = meromorphicTrailingCoeffAt f z₀
theorem laurentCoeffAt_order_ne_zero (hf) (h : meromorphicOrderAt f z₀ ≠ ⊤) :
    laurentCoeffAt f z₀ (meromorphicOrderAt f z₀).untop₀ ≠ 0

-- Analytic case (local-multiplicity/CC4-facing: for analytic f these ARE Taylor coefficients):
theorem laurentCoeffAt_of_analyticAt (hf : AnalyticAt ℂ f z₀) (k : ℤ) :
    laurentCoeffAt f z₀ k = if 0 ≤ k then taylorCoeffAt f z₀ k.toNat else 0

-- ℂ-linearity (the laurent-tails currency):
theorem laurentCoeffAt_add (hf : MeromorphicAt f z₀) (hg : MeromorphicAt g z₀) (k) :
    laurentCoeffAt (f + g) z₀ k = laurentCoeffAt f z₀ k + laurentCoeffAt g z₀ k
theorem laurentCoeffAt_fun_add …    -- `fun z => f z + g z` variant, same proof
theorem laurentCoeffAt_const_mul (c : ℂ) (k) :
    laurentCoeffAt (fun z => c * f z) z₀ k = c * laurentCoeffAt f z₀ k
  -- c = 0 separately (order ⊤); c ≠ 0 via characterization (c·g is a presentation)
theorem laurentCoeffAt_neg / laurentCoeffAt_sub / laurentCoeffAt_fun_sum
    (hF : ∀ i ∈ s, MeromorphicAt (F i) z₀) …   -- Finset.sum, by induction from _add

-- Monomials and shift:
@[simp] theorem laurentCoeffAt_zpow_monomial (m k : ℤ) :
    laurentCoeffAt (fun z => (z - z₀) ^ m) z₀ k = if k = m then 1 else 0
theorem laurentCoeffAt_zpow_mul (hg : MeromorphicAt g z₀) (m k : ℤ) :
    laurentCoeffAt (fun z => (z - z₀) ^ m * g z) z₀ k = laurentCoeffAt g z₀ (k - m)

-- Vanishing principal tail ↔ analytic-after-repair (Mittag-Leffler-facing):
theorem forall_neg_laurentCoeffAt_eq_zero_iff (hf : MeromorphicAt f z₀) :
    (∀ k < 0, laurentCoeffAt f z₀ k = 0) ↔ 0 ≤ meromorphicOrderAt f z₀
```

Proof plan for `laurentCoeffAt_of_eventuallyEq`:
1. `MeromorphicAt f z₀` from `hfg` (`meromorphicAt_congr` + `fun_prop` on the presentation).
2. Case `meromorphicOrderAt f z₀ = ⊤`: then the presentation is `=ᶠ[𝓝[≠]] 0`, so
   `g =ᶠ[𝓝[≠] z₀] 0` (cancel the zpow, nonvanishing off `z₀`), extend over the puncture by
   `ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE` (both sides continuous), so
   `taylorCoeffAt g z₀ = 0` for all `j` (`taylorCoeffAt_congr` + `taylorCoeffAt_const 0`);
   LHS is junk `0`. Both branches of the `if` are `0`.
3. Case order `= m ∈ ℤ` with chosen presentation `g₀` (`g₀ z₀ ≠ 0`): first `n ≤ m` — if
   `n > m`, then `g₀ =ᶠ[𝓝[≠]] (·-z₀)^{n-m}·g`, extend by continuity, evaluate at `z₀`:
   `g₀ z₀ = 0`, contradiction. Then `g =ᶠ[𝓝[≠] z₀] (·-z₀)^(m-n)·g₀` (cancel zpow), extend by
   continuity (`(m - n).toNat` cast juggling: `zpow_natCast`), so by `taylorCoeffAt_congr` +
   `taylorCoeffAt_sub_pow_mul`: `taylorCoeffAt g z₀ j = if j < m - n then 0 else
   taylorCoeffAt g₀ z₀ (j - (m-n))`. Unfold the definition once (its `.choose` IS `g₀`) and
   match the integer/`toNat` case splits (`omega`).

Linearity plan (`laurentCoeffAt_add`): if either order is `⊤`, that summand is `=ᶠ[𝓝[≠]] 0`
and drops out via `laurentCoeffAt_congr`; junk lemma covers its coefficient. Otherwise take
order presentations `(n_f, u_f)`, `(n_g, u_g)`, set `n := min n_f n_g`, rewrite both as
`(·-z₀)^n · ((·-z₀)^(n_f-n)·u_f)` etc. (exponents ≥ 0, so the shifted units are analytic);
`f + g =ᶠ (·-z₀)^n · (shifted_f + shifted_g)`. Apply the characterization three times +
`taylorCoeffAt_add`/`taylorCoeffAt_sub_pow_mul`; integer case analysis by `omega`/`split_ifs`.

### 4.3 `PrincipalPart.lean`

```lean
noncomputable def principalPartAt (f : ℂ → ℂ) (z₀ : ℂ) : ℂ → ℂ        -- §2.3

theorem meromorphicAt_principalPartAt : MeromorphicAt (principalPartAt f z₀) z₀   -- fun_prop
theorem analyticOnNhd_principalPartAt : AnalyticOnNhd ℂ (principalPartAt f z₀) {z₀}ᶜ
theorem principalPartAt_eq_zero_of_order_nonneg (h : 0 ≤ meromorphicOrderAt f z₀) :
    principalPartAt f z₀ = 0                       -- Icc empty (incl. ⊤); also ¬mero variant
theorem laurentCoeffAt_principalPartAt (hf : MeromorphicAt f z₀) (k : ℤ) :
    laurentCoeffAt (principalPartAt f z₀) z₀ k
      = if k < 0 then laurentCoeffAt f z₀ k else 0
  -- fun_sum + zpow_monomial + laurentCoeffAt_eq_zero_of_lt_order for k below the Icc

/-- THE decomposition: `f = (principal part) + (analytic)` on a punctured neighborhood. -/
theorem MeromorphicAt.exists_principalPart_add_analyticAt (hf : MeromorphicAt f z₀) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h z₀ ∧
      (∀ j : ℕ, taylorCoeffAt h z₀ j = laurentCoeffAt f z₀ j) ∧
      f =ᶠ[𝓝[≠] z₀] fun z => principalPartAt f z₀ z + h z

/-- Repair form (MeromorphicNFAt-compatible corollary). -/
theorem MeromorphicAt.orderAt_sub_principalPartAt_nonneg (hf : MeromorphicAt f z₀) :
    0 ≤ meromorphicOrderAt (fun z => f z - principalPartAt f z₀ z) z₀

/-- Uniqueness: any Laurent-tail + analytic decomposition IS the canonical one. -/
theorem eq_principalPart_of_eventuallyEq {c : ℤ → ℂ} {s : Finset ℤ} (hs : ∀ k ∈ s, k < 0)
    (hh : AnalyticAt ℂ h z₀)
    (hfg : f =ᶠ[𝓝[≠] z₀] fun z => (∑ k ∈ s, c k * (z - z₀) ^ k) + h z) :
    (∀ k ∈ s, c k = laurentCoeffAt f z₀ k) ∧
      (∀ k < 0, k ∉ s → laurentCoeffAt f z₀ k = 0) ∧
      ∀ j : ℕ, taylorCoeffAt h z₀ j = laurentCoeffAt f z₀ j
```

Decomposition proof: order `⊤` or `≥ 0`: `principalPartAt = 0`; `h` := the analytic repair
(from `meromorphicOrderAt_eq_int_iff` with `n ≥ 0`, `h := (·-z₀)^n·g` analytic — for order `⊤`
take `h = 0`, using `meromorphicOrderAt_eq_top_iff`; the Taylor-coefficient clause via
`laurentCoeffAt_of_analyticAt` + congr). Pole case `n < 0`: presentation `f =ᶠ (·-z₀)^n·g`;
apply `AnalyticAt.exists_taylor_remainder` to `g` with `m := (-n).toNat`: pointwise
`g z = ∑_{d<m} a_d (z-z₀)^d + (z-z₀)^m·r z`. Multiply by `(z-z₀)^n` (on the punctured
neighborhood; `zpow_add₀` with `z ≠ z₀`): `f =ᶠ ∑_{d<m} a_d (·-z₀)^{d+n} + r`, exponents
`d + n ∈ [n, -1]`, and `a_d = taylorCoeffAt g z₀ d = laurentCoeffAt f z₀ (d+n)`
(characterization). Reindex the sum to `Finset.Icc n (-1)` = `principalPartAt` (the
coefficients `laurentCoeffAt` with `untop₀ = n` — same Icc). `h := r`. Uniqueness: linearity +
`laurentCoeffAt_zpow_monomial` + `laurentCoeffAt_of_analyticAt` (negative coefficients of the
RHS are exactly `c k` on `s` / `0` off `s`; nonnegative ones are `taylorCoeffAt h`).

### 4.4 `Residue.lean`

```lean
noncomputable def resAt (f : ℂ → ℂ) (z₀ : ℂ) : ℂ := laurentCoeffAt f z₀ (-1)

-- Inherited algebra (one-line wrappers over §4.2):
theorem resAt_congr (hfg : f =ᶠ[𝓝[≠] z₀] g) : resAt f z₀ = resAt g z₀
theorem resAt_add (hf : MeromorphicAt f z₀) (hg : MeromorphicAt g z₀) :
    resAt (f + g) z₀ = resAt f z₀ + resAt g z₀          -- + fun_add, sub, neg, fun_sum
theorem resAt_const_mul (c : ℂ) : resAt (fun z => c * f z) z₀ = c * resAt f z₀
@[simp] theorem resAt_of_analyticAt (hf : AnalyticAt ℂ f z₀) : resAt f z₀ = 0
theorem resAt_of_order_nonneg (h : 0 ≤ meromorphicOrderAt f z₀) : resAt f z₀ = 0
@[simp] theorem resAt_sub_inv : resAt (fun z => (z - z₀)⁻¹) z₀ = 1     -- zpow_monomial, k = -1
@[simp] theorem resAt_zpow_monomial (m : ℤ) :
    resAt (fun z => (z - z₀) ^ m) z₀ = if m = -1 then 1 else 0

/-- Residue of a derivative vanishes (Serre/Abel bookkeeping; the k ≤ -2 engine of
change-of-variables). -/
theorem MeromorphicAt.resAt_deriv (hf : MeromorphicAt f z₀) : resAt (deriv f) z₀ = 0

/-- Log-derivative residue = order (THE argument-principle atom; meromorphic-trace input).
Junk-robust: no order hypothesis (order ⊤ gives 0 = untop₀ ⊤). -/
theorem MeromorphicAt.resAt_deriv_div (hf : MeromorphicAt f z₀) :
    resAt (fun z => deriv f z / f z) z₀ = ((meromorphicOrderAt f z₀).untop₀ : ℂ)

/-- Serre-pairing atom, tail form (Miranda VI.3 eq. shape `Σ c_n a_{−1−n}`): residue of an
explicit Laurent tail times a meromorphic germ. -/
theorem resAt_tail_mul {c : ℤ → ℂ} {s : Finset ℤ} (hg : MeromorphicAt g z₀) :
    resAt (fun z => (∑ k ∈ s, c k * (z - z₀) ^ k) * g z) z₀
      = ∑ k ∈ s, c k * laurentCoeffAt g z₀ (-1 - k)
  -- expand, fun_sum + const_mul + zpow_mul; each term: laurentCoeffAt g (-1 - k)

/-- Serre-pairing atom, analytic-multiplier form: residue of `h·f` through `h`'s Taylor
coefficients against `f`'s principal Laurent coefficients (finite sum against the tail).
`n` is any integer lower bound for the order that the consumer holds. -/
theorem resAt_analyticAt_mul (hh : AnalyticAt ℂ h z₀) (hf : MeromorphicAt f z₀)
    {n : ℤ} (hn : (n : WithTop ℤ) ≤ meromorphicOrderAt f z₀) :
    resAt (fun z => h z * f z) z₀
      = ∑ k ∈ Finset.Icc n (-1), taylorCoeffAt h z₀ (-1 - k).toNat * laurentCoeffAt f z₀ k

/-- General product formula (both meromorphic; subsumes the two above — provided because
laurent-tails' μ_f operators multiply tails by meromorphic functions). -/
theorem resAt_mul (hf : MeromorphicAt f z₀) (hg : MeromorphicAt g z₀)
    {n m : ℤ} (hn : (n : WithTop ℤ) ≤ meromorphicOrderAt f z₀)
    (hm : (m : WithTop ℤ) ≤ meromorphicOrderAt g z₀) :
    resAt (fun z => f z * g z) z₀
      = ∑ k ∈ Finset.Icc n (-1 - m), laurentCoeffAt f z₀ k * laurentCoeffAt g z₀ (-1 - k)
```

Proof plans.
`resAt_deriv`: decompose `f =ᶠ[𝓝[≠] z₀] P + h` (§4.3). `deriv f =ᶠ[𝓝[≠] z₀] deriv (P + h)`
by `Filter.EventuallyEq.nhdsNE_deriv`. On a punctured neighborhood, `deriv (P + h) =
deriv P + deriv h` pointwise (`deriv_add`; `P` differentiable off `z₀`, `h` differentiable
near `z₀` via `AnalyticAt.eventually_analyticAt`). `resAt (deriv h) = 0` (`AnalyticAt.deriv`
analytic). `deriv P = ∑_{k ∈ Icc n (-1)} c_k·k·(·-z₀)^(k-1)` pointwise off `z₀`
(`hasDerivAt_zpow` with `z ≠ z₀`, `HasDerivAt.deriv`, finite-sum deriv); exponents `k - 1 ≤ -2`
never hit `-1`, so `resAt_fun_sum` + `resAt_zpow_monomial` gives `0`.

`resAt_deriv_div`: order `⊤`: `f =ᶠ[𝓝[≠]] 0` and `deriv f =ᶠ[𝓝[≠]] 0` (`nhdsNE_deriv`);
`0/0 = 0`; both sides `0`. Order `n` finite: presentation `f =ᶠ (·-z₀)^n·u`, `u z₀ ≠ 0`. On a
punctured neighborhood where `u` is analytic and nonvanishing (continuity) and `z ≠ z₀`:
`deriv f = n(·-z₀)^(n-1)·u + (·-z₀)^n·deriv u` (`nhdsNE_deriv` + product/zpow rules), so
`deriv f / f = n·(·-z₀)⁻¹ + deriv u/u` (`field_simp`; denominators nonzero). `deriv u/u`
analytic at `z₀` (`AnalyticAt.div`, `u z₀ ≠ 0`) ⇒ residue `0`; conclude with `resAt_add`,
`resAt_const_mul`, `resAt_sub_inv`.

`resAt_analyticAt_mul` / `resAt_mul`: decompose `f =ᶠ P_f + r_f`; `h·f =ᶠ h·P_f + h·r_f`;
`h·r_f` analytic ⇒ `0`; `h·P_f = ∑_k c_k·(h·(·-z₀)^k)` and `resAt (h·(·-z₀)^k) =
laurentCoeffAt h z₀ (-1-k)` (`laurentCoeffAt_zpow_mul` + commutativity) `= taylorCoeffAt h
(-1-k).toNat` (`laurentCoeffAt_of_analyticAt`; `-1-k ≥ 0` since `k ≤ -1`). Pad the sum from
`Icc n_order (-1)` to `Icc n (-1)` with zero coefficients (`laurentCoeffAt_eq_zero_of_lt_order`,
`Finset.sum_subset`). `resAt_mul`: same, decomposing both and using `resAt_tail_mul` on the
cross terms; `r_f·r_g` analytic ⇒ `0`; index bookkeeping by `omega`.

### 4.5 `ChangeOfVariables.lean` — the hardest theorem; route (a), fully algebraic

```lean
/-- Chart invariance of the residue of a 1-form integrand (Forster 9.9-flavored): for a local
analytic isomorphism `φ` at `w₀` with `φ w₀ = z₀`, the residue of `(f ∘ φ)·φ'` at `w₀` equals
the residue of `f` at `z₀`. Makes `Res_p(ω)` on a surface chart-independent (residue-theorem
unit). -/
theorem resAt_comp_mul_deriv {φ : ℂ → ℂ} (hφ : AnalyticAt ℂ φ w₀) (hφ' : deriv φ w₀ ≠ 0)
    (hφ₀ : φ w₀ = z₀) (hf : MeromorphicAt f z₀) :
    resAt (fun w => f (φ w) * deriv φ w) w₀ = resAt f z₀
```

**Route decision.** (a) algebraic (chosen) vs (b) integral via `circleIntegral` + a planar
change-of-variables for contour integrals (rejected: mathlib has no holomorphic
change-of-variables for `circleIntegral`; one would have to deform `φ(circle)` to a circle —
winding-number machinery that does not exist at the pin. Route (a) needs zero integration.)

Proof plan (each step checked against the §4.1–4.4 toolkit):
1. **Transport of the punctured filter**: `hT : Tendsto φ (𝓝[≠] w₀) (𝓝[≠] z₀)` — this is
   `hφ.differentiableAt.hasDerivAt.tendsto_nhdsNE hφ'` rewritten along `hφ₀`
   (`HasDerivAt.tendsto_nhdsNE`, `Deriv/Inverse.lean:107`, verified). Consequently any
   `=ᶠ[𝓝[≠] z₀]` fact about `f` pulls back to `=ᶠ[𝓝[≠] w₀]` about `f ∘ φ` (`hT.eventually`).
   Also `∀ᶠ w in 𝓝[≠] w₀, φ w ≠ z₀` (`hT.eventually self_mem_nhdsWithin`-style).
2. **Decompose**: `f =ᶠ[𝓝[≠] z₀] (∑_{k ∈ Icc n (-1)} c_k (·-z₀)^k) + h`, `h` analytic,
   `c_k = laurentCoeffAt f z₀ k`, `n := untop₀ order` (§4.3). Pull back and multiply:
   `(f∘φ)·φ' =ᶠ[𝓝[≠] w₀] ∑_k c_k·((φ·-z₀)^k·φ') + (h∘φ)·φ'`. `resAt_congr` + `resAt_fun_sum` +
   `resAt_const_mul` (each summand is meromorphic at `w₀`: `((hφ.sub analyticAt_const)
   .meromorphicAt.zpow k).mul (hφ.deriv.meromorphicAt)` — wait, order of factors:
   `((analytic base).meromorphicAt.zpow).mul (deriv φ analytic).meromorphicAt`; fine by
   `MeromorphicAt.mul`).
3. **Analytic remainder**: `(h ∘ φ)·φ'` is analytic at `w₀` (`AnalyticAt.comp` along `hφ₀` +
   `hφ.deriv` + `mul`) ⇒ `resAt = 0` (`resAt_of_analyticAt`).
4. **Term `k = -1`**: `(φ - z₀)⁻¹·φ' = deriv g / g` for `g := fun w => φ w - z₀` up to
   `mul_comm`/`div_eq_mul_inv` (`deriv g = deriv φ` by `deriv_sub_const`). Order of `g` at
   `w₀`: `g w₀ = 0` and `deriv g w₀ = deriv φ w₀ ≠ 0`, so `analyticOrderAt (φ · - φ w₀) w₀ = 1`
   (`AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero`, rewritten along `hφ₀`), bridge
   `AnalyticAt.meromorphicOrderAt_eq` ⇒ `meromorphicOrderAt g w₀ = 1`, `untop₀ = 1`. Apply
   `MeromorphicAt.resAt_deriv_div` (with `deriv g` congruent to `deriv φ` — pointwise equal
   functions, `deriv_sub_const` is a `simp` lemma): residue `= 1`. Contribution: `c_{-1}`.
5. **Terms `k ≤ -2`**: let `F := fun w => ((k+1 : ℂ))⁻¹ * (φ w - z₀)^(k+1)`. `F` is
   meromorphic at `w₀` (as in step 2). On the punctured neighborhood where `φ w ≠ z₀` and `φ`
   is differentiable: `HasDerivAt F ((φ w - z₀)^k * deriv φ w) w` — chain rule
   `hasDerivAt_zpow (k+1) _ (Or.inl (sub_ne_zero.2 …)) |>.comp` with the `(k+1)⁻¹(k+1) = 1`
   cancellation (`k ≠ -1` ⇒ `(k+1 : ℂ) ≠ 0`, `Int.cast` nonzero). Hence
   `(φ·-z₀)^k·φ' =ᶠ[𝓝[≠] w₀] deriv F` (`HasDerivAt.deriv` pointwise on the eventual set).
   `resAt_congr` + `MeromorphicAt.resAt_deriv` ⇒ `0`.
   (`k ≥ 0` does not occur — `Icc n (-1)` — but would be analytic, residue `0`, same as 3.)
6. **Assemble**: total `= c_{-1} = resAt f z₀`. If `n > -1` the sum is empty AND
   `resAt f z₀ = 0` by `resAt_of_order_nonneg` — both sides `0`. ∎

Corollary shipped with it (residue-theorem convenience; free from the theorem + `resAt_congr`):

```lean
theorem resAt_comp_mul_deriv_of_eventuallyEq {φ : ℂ → ℂ} (hφ : AnalyticAt ℂ φ w₀)
    (hφ' : deriv φ w₀ ≠ 0) (hφ₀ : φ w₀ = z₀) (hf : MeromorphicAt f z₀)
    {F : ℂ → ℂ} (hF : F =ᶠ[𝓝[≠] w₀] fun w => f (φ w) * deriv φ w) :
    resAt F w₀ = resAt f z₀
```

### 4.6 `IntegralBridge.lean` — the one honest integration atom

```lean
open Real Complex in
/-- Fixed-radius residue formula: if `f` is meromorphic at `z₀` and differentiable on the
punctured closed disk, the circle integral computes the residue. All mathlib names verified
at the pin (§1). -/
theorem circleIntegral_eq_two_pi_I_mul_resAt {R : ℝ} (hR : 0 < R) (hf : MeromorphicAt f z₀)
    (hd : ∀ z ∈ closedBall z₀ R \ {z₀}, DifferentiableAt ℂ f z) :
    (∮ z in C(z₀, R), f z) = (2 * π * I) * resAt f z₀

open Real Complex in
/-- Small-radius form for consumers that only know meromorphy (they pick their own ρ). -/
theorem MeromorphicAt.eventually_circleIntegral_eq_two_pi_I_mul_resAt
    (hf : MeromorphicAt f z₀) :
    ∀ᶠ R in 𝓝[>] (0 : ℝ), (∮ z in C(z₀, R), f z) = (2 * π * I) * resAt f z₀
```

Proof plan (fixed-radius; every lemma name verified — §1 "Circle integrals"/"Cauchy machinery"):
1. Decomposition `f =ᶠ[𝓝[≠] z₀] P + h` (§4.3); the eventual-equality set contains
   `ball z₀ r₂ \ {z₀}` for some `r₂ > 0`; `h` is analytic on `ball z₀ r₁`
   (`AnalyticAt.eventually_analyticAt` + `Filter.Eventually.exists_mem`). Pick
   `r := min stuff`, `0 < r ≤ R`, `r < min r₁ r₂`.
2. **Deformation to the small circle**:
   `Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable` (`s := ∅`,
   `h0 : 0 < r`, `hle : r ≤ R`; continuity on `closedBall z₀ R \ ball z₀ r` and
   differentiability on the open annulus from `hd` — the sets avoid `z₀`):
   `∮_{C(z₀,R)} f = ∮_{C(z₀,r)} f`. (Degenerate `r = R` allowed by taking `r < R` strictly; if
   `R` already small skip — uniform: always deform.)
3. **Split on the sphere**: `EqOn f (P + h) (sphere z₀ r)` (sphere ⊆ punctured ball of step 1);
   `circleIntegral.integral_congr hr.le`. Then `circleIntegral.integral_add` with
   integrability: `P` — finite sum of `c_k·(·-z₀)^k`, `CircleIntegrable.fun_sum` +
   `const_smul` + `circleIntegrable_sub_zpow_iff` (RHS disjunct `w ∉ sphere c |R|`: here
   `w = z₀ = c`, `z₀ ∈ sphere z₀ r ↔ r = 0`, false); `h` — `ContinuousOn.circleIntegrable`
   from analyticity on `closedBall z₀ r`.
4. **Analytic part**: `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable`
   (`s := ∅`, `h0 : 0 ≤ r`, continuity + differentiability from `h` analytic on the closed
   ball) ⇒ `∮ h = 0`.
5. **Principal part termwise**: `circleIntegral.integral_fun_sum` + `integral_const_mul`;
   `circleIntegral.integral_sub_zpow_of_ne` kills `k ≠ -1`;
   `circleIntegral.integral_sub_center_inv` (with `zpow_neg_one` to align `(·-z₀)^(-1 : ℤ)`
   with `(·-z₀)⁻¹`) gives `2πI` at `k = -1`. Collapse: `Finset.sum_ite_eq'`-style:
   `= (if -1 ∈ Icc n (-1) then c_{-1} else 0)·2πI`; if `-1 ∉ Icc` then `n > -1` and
   `resAt f z₀ = 0` (`resAt_of_order_nonneg`) — uniform conclusion `2πI·resAt f z₀`. ∎

Small-radius form: `MeromorphicAt` gives `N : ℕ` with `(·-z₀)^N • f` analytic at `z₀`
(definition `Basic.lean:36`), hence analytic on some `ball z₀ ρ₀`; then for `z ≠ z₀` in that
ball `f z = (z-z₀)^(-N:ℤ)·((z-z₀)^N·f z)` is differentiable, so the fixed-radius hypotheses
hold for every `R < ρ₀`; `Ioo 0 ρ₀ ∈ 𝓝[>] 0`.

Note for planar-stokes-atoms: if a countable-exceptional-set variant is ever needed, thread
`s.Countable` through steps 2 and 4 verbatim (the mathlib lemmas already take it); we ship the
`s = ∅` form only.

### 4.7 `GermFunctionals.lean` — linear-map packaging (laurent-tails/serre-duality currency)

```lean
/-- Meromorphy is a property of the punctured germ. -/
def MeromorphicGerm (z₀ : ℂ) (γ : Filter.Germ (𝓝[≠] z₀) ℂ) : Prop :=
  γ.liftOn (MeromorphicAt · z₀) fun _ _ hfg => propext (meromorphicAt_congr hfg)

/-- The ℂ-space of meromorphic germs at `z₀` (a submodule of the full germ module). -/
def meromorphicGermsAt (z₀ : ℂ) : Submodule ℂ (Filter.Germ (𝓝[≠] z₀) ℂ) where
  carrier := {γ | MeromorphicGerm z₀ γ}
  zero_mem' := analyticAt_const.meromorphicAt            -- germ of 0
  add_mem' := …                                          -- Germ.inductionOn₂ + MeromorphicAt.add
  smul_mem' := …                                         -- Germ induction + const-mul closure

/-- Laurent coefficients as ℂ-linear functionals on meromorphic germs. -/
noncomputable def laurentCoeffL (z₀ : ℂ) (k : ℤ) : meromorphicGermsAt z₀ →ₗ[ℂ] ℂ where
  toFun γ := (γ : Filter.Germ _ ℂ).liftOn (laurentCoeffAt · z₀ k)
    fun _ _ hfg => laurentCoeffAt_congr hfg k
  map_add' := …    -- Germ induction; laurentCoeffAt_add (meromorphy from the membership proofs)
  map_smul' := …   -- laurentCoeffAt_const_mul

/-- The residue functional. -/
noncomputable def resL (z₀ : ℂ) : meromorphicGermsAt z₀ →ₗ[ℂ] ℂ := laurentCoeffL z₀ (-1)

@[simp] theorem laurentCoeffL_mk {f : ℂ → ℂ} (hf : MeromorphicAt f z₀) (k) :
    laurentCoeffL z₀ k ⟨(↑f : Filter.Germ (𝓝[≠] z₀) ℂ), hf⟩ = laurentCoeffAt f z₀ k := rfl
```

Design notes: the `Filter.Germ (𝓝[≠] z₀) ℂ` module instance is
`Order/Filter/Germ/Basic.lean:654`; `smul` by constants is `Germ.const_smul`-flavored
(the `Module ℂ (Germ l ℂ)` instance smul is coefficient-wise on representatives, which is what
`laurentCoeffAt_const_mul` matches). Membership/lift plumbing is `Quotient.inductionOn`-level,
~60 lines. laurent-tails (CC8) may take `meromorphicGermsAt` as the local model for its germ
spaces or re-derive; the frozen part of this interface is: *`laurentCoeffL z₀ k` exists as a
`→ₗ[ℂ]` and computes `laurentCoeffAt` on representatives.*

### 4.8 `MittagLeffler.lean` — principal-part distributions (Forster §17.1–17.2, planar data)

```lean
/-- A Mittag-Leffler datum of principal parts on `U ⊆ ℂ`: at finitely many points, a finite
tail of negative-exponent Laurent coefficients. -/
structure PrincipalPartData (U : Set ℂ) where
  coeff : ℂ → (ℤ →₀ ℂ)                                -- coefficient tail at each point
  coeff_neg : ∀ p, ∀ k ∈ (coeff p).support, k < 0     -- pure principal parts, no constant term
  mem_of_ne_zero : ∀ p, coeff p ≠ 0 → p ∈ U           -- supported in U
  finite_support : {p | coeff p ≠ 0}.Finite           -- finitely many poles

namespace PrincipalPartData
variable {U : Set ℂ}

instance : Zero (PrincipalPartData U) / Add / Neg / SMul ℂ …  -- pointwise on `coeff`;
instance : AddCommGroup (PrincipalPartData U) / Module ℂ …    -- support of sum ⊆ union of
                                                              -- finite supports; ext lemma on coeff

/-- `f` realizes the datum on `U`: meromorphic with exactly these principal parts. -/
def Realizes (f : ℂ → ℂ) (D : PrincipalPartData U) : Prop :=
  MeromorphicOn f U ∧ ∀ p ∈ U, ∀ k < 0, laurentCoeffAt f p k = D.coeff p k

/-- The associated function: sum of the finite tails (junk-free honest function). -/
noncomputable def toFun (D : PrincipalPartData U) : ℂ → ℂ := fun z =>
  ∑ᶠ p, ∑ k ∈ (D.coeff p).support, D.coeff p k * (z - p) ^ k

/-- Total residue of the datum. -/
noncomputable def totalRes (D : PrincipalPartData U) : ℂ := ∑ᶠ p, D.coeff p (-1)

/-- Extraction from a meromorphic function with finitely many poles. -/
noncomputable def ofMeromorphicOn {f : ℂ → ℂ} (hf : MeromorphicOn f U)
    (hfin : {p ∈ U | meromorphicOrderAt f p < 0}.Finite) : PrincipalPartData U
  -- coeff p := Finsupp.onFinset (Finset.Icc (order).untop₀ (-1))
  --   (fun k => if k < 0 ∧ p ∈ U then laurentCoeffAt f p k else 0) …

theorem realizes_ofMeromorphicOn … : Realizes f (ofMeromorphicOn hf hfin)
theorem Realizes.add : Realizes f D → Realizes g E → Realizes (f + g) (D + E)
theorem Realizes.smul (c : ℂ) : Realizes f D → Realizes (c • f) (c • D)
/-- Two realizations differ by a pole-free function (the ML gluing atom: differences of
solutions are holomorphic-after-repair). -/
theorem Realizes.sub_orderAt_nonneg (hf : Realizes f D) (hg : Realizes g D) :
    ∀ p ∈ U, 0 ≤ meromorphicOrderAt (f - g) p
  -- laurentCoeffAt_sub + forall_neg_laurentCoeffAt_eq_zero_iff
/-- Realizing the zero datum = no poles on U. -/
theorem realizes_zero_iff (hf : MeromorphicOn f U) :
    Realizes f (0 : PrincipalPartData U) ↔ ∀ p ∈ U, 0 ≤ meromorphicOrderAt f p
end PrincipalPartData
```

**Scope check against downstream** (blueprint): canonical-forms (§17.4) needs the *vocabulary*
of principal parts on charts and `resAt` bookkeeping — covered by §4.3/§4.4; the sheaves `Ω_D`
themselves are its own business. serre-duality-cech needs Forster 17.2's residue of an ML
distribution of 1-forms — that object lives on `X` with form-cochains; what it consumes from
here is `resAt`, `resAt_analyticAt_mul`, chart invariance, and *this* planar data type for the
chart-local computations. Global solvability (Forster §18/§26) is later units. So the DATA
structure + `Realizes` + linear ops + `totalRes` is the minimal right thing; anything more
(orderings, restriction maps) is YAGNI until the cech/laurent-tails designs land — marked
**semi-frozen**: laurent-tails' designer may extend, not change, this interface.

---

## 5. Junk-value and compatibility ledger (CC3/CC4 alignment)

- `laurentCoeffAt`/`resAt`/`principalPartAt` are `0`/empty on: non-meromorphic germs, the
  locally-zero germ (order `⊤`), and coefficients below the order. No statement becomes
  vacuously true through junk: every honest lemma carries `MeromorphicAt`/`AnalyticAt` guards,
  mirroring mathlib's own `meromorphicTrailingCoeffAt` conventions.
- CC3 (`ordAtX f x := meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)`): surface
  units will apply this unit's functionals to `f ∘ (chartAt ℂ x).symm` at `chartAt ℂ x x`;
  chart-independence of the *residue of the 1-form integrand* is §4.5, and of the *order* is
  mathlib's `meromorphicOrderAt_comp_of_deriv_ne_zero` (CC3's own bridge). Note the residue of
  a raw *function* (not integrand) is NOT chart-invariant — consumers must pair with the
  `deriv` factor exactly as §4.5 states; the doc-comment on `resAt_comp_mul_deriv` says this
  loudly.
- CC4/local-multiplicity: `laurentCoeffAt_of_analyticAt` + `AnalyticAt.meromorphicOrderAt_eq`
  keep `analyticOrderAt`-facing statements one rewrite away.
- `meromorphicTrailingCoeffAt` compatibility: `laurentCoeffAt_order` (§4.2) — downstream may
  freely mix mathlib's leading-coefficient lemmas with ours.

## 6. Dependencies note (blueprint edge "Builds on: holomorphic-forms")

The blueprint's edge is about *scheduling/conceptual* order (residues feed 1-form residue
bookkeeping). The Lean unit is deliberately planar and imports NOTHING from `Jacobian/Forms`
(as `Forms/Montel.lean` is manifold-free for finiteness-and-chi, this whole unit is
manifold-free for residue-theorem/meromorphic-trace/laurent-tails). No `docs/requests/` needed:
zero upstream lemmas required from other units.

## 7. Risks & fallbacks

1. **`.choose`-alignment in `laurentCoeffAt_of_eventuallyEq`** (medium): the definition's
   `.choose` must be beaten into the general-presentation statement. Mitigation: the proof
   compares the chosen presentation with the given one purely through
   `taylorCoeffAt_congr`/`taylorCoeffAt_sub_pow_mul` — the same pattern
   `TrailingCoefficient.lean` uses successfully; if `untop₀`/`toNat` case splits get ugly,
   `omega` closes them. Fallback: none needed — this is the one place allowed to be ugly.
2. **`dslope` iterate lemmas at `z₀` need `DifferentiableAt` for the `dslope_same` branch**
   (low): all our uses are on analytic germs; the eventual-equality versions
   (`…=ᶠ[𝓝 z₀]…`) sidestep pointwise values everywhere except the final evaluation, which is
   guarded. If `taylorCoeffAt_const_mul` unconditional form fights, add an `AnalyticAt`
   hypothesis (harmless; all consumers have it).
3. **Annulus-deformation hypothesis shape** (low): `circleIntegral_eq_of_…_annulus_…` wants
   `ContinuousOn (closedBall R \ ball r)` + `DifferentiableAt` on `(ball R \ closedBall r)`;
   our `hd` on `closedBall \ {z₀}` supplies both since the annulus avoids `z₀` — pure set
   arithmetic (`mem_diff`, `mem_ball`, `omega`-free but fiddly `dist` juggling). Fallback:
   restate the bridge with `AnalyticOnNhd ℂ f (closedBall z₀ R \ {z₀})` if `DifferentiableAt`
   plumbing annoys; consumers (planar-stokes) hold analyticity anyway.
4. **`zpow` vs `⁻¹` vs `^(n : ℤ)` normal forms** (low, pervasive): fix on `zpow` internally;
   provide `⁻¹`-spelled corollaries (`resAt_sub_inv`) at the API surface; `zpow_neg_one`,
   `zpow_natCast` at friction points.
5. **Germ plumbing** (low): `Filter.Germ.liftOn` + `Submodule` membership by induction is
   boilerplate; if `Germ` module-instance defeq fights the `Submodule` structure, fallback is
   a bare `structure MeromorphicGermAt` with its own `Module` instance (~+80 lines), same API.
6. **Compile weight** (low): heaviest import is `Analysis/Complex/CauchyIntegral` — confined
   to `IntegralBridge.lean`; the algebraic files stay on the light
   `Meromorphic`/`DSlope`/`IsolatedZeros` spine (spike: 6.8 s warm for the full import stack
   including CauchyIntegral — cheap).

## 8. Spike report (`scratch_residue.lean`, project root, 74 lines)

Gated per compile discipline (`pgrep -cx lean` < 3), run `lake env lean scratch_residue.lean`:
**compiles clean, exit 0, 6.8 s wall** (warm cache; the CauchyIntegral import stack is cheap
here). One fix between the two runs: `ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE`
states **`f =ᶠ[𝓝[≠] x] g ↔ f =ᶠ[𝓝 x] g`** (punctured filter on the LEFT) — builders take
`.mp` to extend punctured equalities over the puncture (§4.2 step 2/3, §4.3). Verified by
re-typing exact statements:
- the `laurentCoeffAt` definition (§2.2) **elaborates as written** (dite + `.choose` +
  `untop₀`/`toNat` + dslope-iterate extractor), and `taylorCoeffAt`, `resAt` on top of it;
- `dslope_sub_smul_of_ne`, `pow_sub_smul_iterate_dslope_of_zero` (exact hypothesis shape),
  `HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope`;
- `Filter.EventuallyEq.nhdsNE_deriv`, `ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE`
  (T2 target; direction as above), `HasDerivAt.tendsto_nhdsNE`;
- `meromorphicOrderAt_zpow_id_sub_const`,
  `AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero`, `AnalyticAt.meromorphicOrderAt_eq`,
  `meromorphicAt_congr`;
- `circleIntegral.integral_sub_zpow_of_ne`, `circleIntegral.integral_sub_center_inv`,
  `Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable`,
  `Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable`;
- `Filter.Germ` `Module ℂ` instance + `Germ.liftOn` through `meromorphicAt_congr` (the
  §4.7 `MeromorphicGerm` predicate, verbatim).
Imports needed: exactly the §3 spine (`IsolatedZeros`, `DSlope`,
`Meromorphic.TrailingCoefficient`, `CauchyIntegral`, `Calculus.Deriv.Inverse`,
`Order.Filter.Germ.Basic`).

## 9. Downstream map (who consumes what)

- **residue-theorem**: `resAt`, `resAt_comp_mul_deriv(_of_eventuallyEq)` (well-definedness of
  `Res_p(h·dg₀)` across charts), `circleIntegral_eq_two_pi_I_mul_resAt` (the boundary-term
  evaluation in the PoU/Stokes argument), decomposition (§4.3) for isolating poles.
- **planar-stokes-atoms**: `circleIntegral_eq_two_pi_I_mul_resAt` + the small-radius form
  ("annulus residue integrals" seed); `principalPartAt` for splitting integrands.
- **meromorphic-trace**: `MeromorphicAt.resAt_deriv_div` (argument-principle atom
  res(f'/f) = ord), `resAt_deriv` (= 0), linearity, `resAt_congr`.
- **serre-duality-cech / serre-duality-tails**: `resAt_analyticAt_mul`, `resAt_tail_mul`,
  `resAt_mul` (Miranda VI.3 `Res_ω` pairing atoms), `resL`/`laurentCoeffL` functionals,
  `resAt_deriv` (exactness bookkeeping).
- **laurent-tails (CC8)**: `laurentCoeffAt` + linearity + `laurentCoeffAt_zpow_mul` (shift; the
  `μ_f` operators) + `laurentCoeffAt_congr` + `meromorphicGermsAt`/`laurentCoeffL` (germ-valued
  tail spaces); `forall_neg_laurentCoeffAt_eq_zero_iff` (`L(D) = ker α_D`).
- **canonical-forms**: `principalPartAt`, decomposition, `resAt` vocabulary on chart
  representatives; `PrincipalPartData` for §17-flavored bookkeeping.
- **abel-weak-solutions / abel-theorem**: `resAt_deriv_div` through meromorphic-trace; nothing
  direct.
- **meromorphic-and-divisors (CC3)**: nothing imported from here (CC3 is
  mathlib-direct), but the compatibility ledger §5 is the contract both sides state against.
