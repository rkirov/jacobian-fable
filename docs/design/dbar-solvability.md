# Design: dbar-solvability (`Jacobian/Dbar/`)

Blueprint unit **dbar-solvability** — the only PDE of the project (routing decision #3: the ONLY
PDE input to the whole edifice is ∂̄ on a disk, Forster 13.2). Delivers:

1. the **planar ∂̄ layer**: the Cauchy-transform solution of `∂̄u = g` for compactly supported
   smooth `g` (Forster 13.1) and the **Dolbeault lemma on an open disk** (Forster 13.2,
   exhaustion + telescoping);
2. the **Wirtinger / almost-complex API** (`wirtingerDbar`, Cauchy–Riemann bridge, (0,1) chain
   rule) — the hand-built J-smoothness API the blueprint says mathlib lacks;
3. the **surface layer**: smooth `(0,1)`-forms `Form01 X` as chart-coefficient families with the
   `conj (deriv τ)` transition rule, the intrinsic `∂̄ : C^∞(X) → Form01 X`, chart-disk local
   solvability on `X`, and holomorphic representatives of ∂̄-closed functions;
4. **disk acyclicity for the Čech complex**: `Subsingleton (H1Cover D 𝒱)` for every finite cover
   `𝒱` of a chart disk (the interface the cech design assigned to this unit, its §7/§11).

Consumers (blueprint entries re-read): **dolbeault-comparison** (chart-disk solvability, `Form01`,
`dbar`, holomorphic-of-∂̄-closed, disk acyclicity → Leray 12.8, PoU availability),
**finiteness-and-chi** (indirectly, through dolbeault's Leray theorem + cech's `H1`),
**planar-stokes-atoms** (builds ON us per DAG; reuses `Wirtinger.lean`, must NOT be imported here).

References: Forster §13 (book 104–109 = PDF 110–115; Lemma 13.1 = PDF 110–111, **Thm 13.2 =
PDF 111–113**, Thm 13.4 = PDF 113), §15 (Dolbeault Thm 15.14 = PDF 131 — context only, owned by
dolbeault-comparison); Forster Appendix A (partitions of unity, PDF 243–244).
Substrates: `docs/design/cech-cohomology.md` (§4.1–4.2 `FinCover`/`C0/C1/C2/d0/d1/Z1/B1/H1Cover`,
`IsChartDisk`, `subsingleton_h1Cover_iff`), `docs/design/meromorphic-and-divisors.md`
(`MeroGermOn`, `mk/mk_eq_mk`, `restrict` AlgHom, `ord_*`, `evalAt_*`, `holoRepr` suite,
`LinSysOn`), completed units `Jacobian/Surface/` (CC7 `RealSmooth.lean`, `Bridges.lean`) and
`Jacobian/Forms/Analyticity.lean` (`analyticAt_trans`, `deriv_trans_comp`).

All mathlib names below verified by reading source at the pin
(`.lake/packages/mathlib/Mathlib/...`); the four riskiest shapes compiled in the spike (§10).

---

## 0. The two routing decisions of this design (read first)

**A. The ∂̄-computation is convolution + polar-coordinates FTC — no 2-D Stokes at all.**
Forster proves 13.1 by differentiating under the integral and then Stokes on an annulus.
Mathlib has no smooth-function annulus Stokes, and the DAG forbids using planar-stokes-atoms
(it builds on us). Instead:

* `u := cauchyKernel ⋆[mul ℝ ℂ] g` with `cauchyKernel w := (π * w)⁻¹`; mathlib's convolution
  API (`HasCompactSupport.contDiff_convolution_right`, `.hasFDerivAt_convolution_right`,
  `convolution_precompR_apply`) gives smoothness AND `fderiv u = k ⋆ fderiv g` — the entire
  "differentiate under the integral" step is a verified mathlib package;
* the pointwise identity `(k ⋆ ∂̄g)(z) = g(z)` (Cauchy–Pompeiu for compactly supported C¹ g) is
  proved by `Complex.integral_comp_polarCoord_symm` + Fubini + **1-D FTC in the radial and
  angular directions**. In polar coordinates the kernel singularity cancels exactly
  (`r • (π r e^{iθ})⁻¹ = π⁻¹ e^{-iθ}`), and the integrand splits as
  `e^{-iθ}·(∂̄g)(z − re^{iθ}) = ½ [(ir)⁻¹ ∂_θ G − ∂_r G]` with `G (r,θ) := g (z − r e^{iθ})`;
  the θ-integral of `∂_θ G` vanishes by periodicity, the r-integral of `∂_r G` telescopes to
  `−g z` by compact support. Full computation in §5. Every atom exists at the pin.

**B. `(0,1)`-forms are chart-coefficient families; no bundles, no tangent-space projections.**
The blueprint warns the `restrictScalars ℂ→ℝ` diamond on tangent spaces breaks definitional
equality, and mathlib has no anti-linear Hom-bundle (checked: no `MeasurableInv`-style instances
for antilinear bundles, no `ContMDiffVectorBundle` for `→ₗ[ℝ]`-Hom over a `𝓘(ℝ,ℂ)` tangent
bundle without hitting the diamond; `docs/mathlib-inventory.md` §16 confirms no ℝ↔ℂ manifold
bridge). A bundled `ContMDiffSection` model is therefore REJECTED. `Form01 X` is a structure:
a `chartAt`-indexed family of coefficient functions (the coefficient of `dz̄`), zero off chart
targets (junk-normalized, so `ext` is honest), smooth on targets, with the anti-holomorphic
transition rule `coeff_y = conj (deriv τ) · (coeff_x ∘ τ)`. This mirrors, with `conj`, the
frozen CC1 `coeffIn` philosophy (`Jacobian/Forms/Coeffs.lean:234` `coeffIn_trans`), so all
transition machinery (`analyticAt_trans`, `deriv_trans_comp`) is reused, not re-proved. The
intrinsic `∂̄` is chart-local `wirtingerDbar` of the chart representative — by the (0,1) chain
rule this IS `proj^{0,1} ∘ d`; the identification is a paper remark, never formalized.

---

## 1. Verified mathlib facts (file:line at the pin)

### 1.1 Convolution (`Analysis/Convolution.lean`, `Analysis/Calculus/ContDiff/Convolution.lean`)

- `convolution f g L μ` (`Convolution.lean:401`), notation `f ⋆[L, μ] g` (`:406`), `f ⋆[L] g`
  with `MeasureSpace.volume` (`:410`); `convolution_def : (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ`
  (`:419`).
- `HasCompactSupport.convolutionExists_right (L) (hcg : HasCompactSupport g)
  (hf : LocallyIntegrable f μ) (hg : Continuous g) : ConvolutionExists f g L μ` (`:385–389`).
- `HasCompactSupport.hasFDerivAt_convolution_right (hcg) (hf : LocallyIntegrable f μ)
  (hg : ContDiff 𝕜 1 g) (x₀) : HasFDerivAt (f ⋆[L, μ] g) ((f ⋆[L.precompR G, μ] fderiv 𝕜 g) x₀) x₀`
  (`ContDiff/Convolution.lean:63`) — works over `RCLike 𝕜`; we instantiate `𝕜 := ℝ`, `G = E =
  E' = F = ℂ`, `L := ContinuousLinearMap.mul ℝ ℂ`, `μ := volume`. Instance needs:
  `[NormedSpace ℝ ℂ] [MeasurableSpace ℂ] [BorelSpace ℂ] [NormedSpace ℝ ℂ] [SFinite volume]
  [IsAddLeftInvariant volume]` — all present for `ℂ` (volume is add-Haar). **Spiked** (§10).
- `HasCompactSupport.contDiff_convolution_right {n : ℕ∞} (hcg) (hf : LocallyIntegrable f μ)
  (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n (f ⋆[L, μ] g)` (`ContDiff/Convolution.lean:423`).
- `convolution_precompR_apply (hf : LocallyIntegrable f μ) (hcg : HasCompactSupport g)
  (hg : Continuous g) (x₀ x) : (f ⋆[L.precompR E'', μ] g) x₀ x = (f ⋆[L, μ] fun a => g a x) x₀`
  (`Convolution.lean:925`) — extracts directional components of the derivative convolution.
- `HasCompactSupport.fderiv (hf : HasCompactSupport f) : HasCompactSupport (fderiv 𝕜 f)`
  (`Analysis/Calculus/FDeriv/Const.lean:388`).

### 1.2 Polar coordinates (`Analysis/SpecialFunctions/PolarCoord.lean`)

- `Complex.polarCoord : OpenPartialHomeomorph ℂ (ℝ × ℝ)` (`:181`);
  `Complex.polarCoord_target : target = Set.Ioi 0 ×ˢ Set.Ioo (-π) π` (`:191`);
  `Complex.polarCoord_symm_apply (p) : symm p = p.1 * (Real.cos p.2 + Real.sin p.2 * I)` (`:195`)
  — equal to `circleMap 0 p.1 p.2` via `Complex.exp_mul_I`.
- `Complex.integral_comp_polarCoord_symm (f : ℂ → E) :
  (∫ p in polarCoord.target, p.1 • f (Complex.polarCoord.symm p)) = ∫ p, f p` (`:205`).
- `Complex.lintegral_comp_polarCoord_symm (f : ℂ → ℝ≥0∞) :
  (∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p)) = ∫⁻ p, f p`
  (`:212`) — THE tool for local integrability of `1/‖z‖` (no layer-cake needed). **Spiked.**

### 1.3 Integration plumbing

- `LocallyIntegrable` (`MeasureTheory/Function/LocallyIntegrable.lean:239`);
  `locallyIntegrable_iff [LocallyCompactSpace X] : LocallyIntegrable f μ ↔ ∀ k, IsCompact k →
  IntegrableOn f k μ` (`:332`); `LocallyIntegrable.integrableOn_isCompact` (`:312`).
- `MeasureTheory.setIntegral_prod (f) (hf : IntegrableOn f (s ×ˢ t) (μ.prod ν)) :
  ∫ z in s ×ˢ t, f z = ∫ x in s, ∫ y in t, f (x, y)` (`MeasureTheory/Integral/Prod.lean:549`);
  `integral_integral_swap (hf : Integrable (uncurry f) (μ.prod ν))` (`:532`). No
  `setIntegral_prod_symm` at the pin — the θ-outer iteration goes through
  indicator-extension + `integral_integral_swap` (§5 step 6; spiked the swap shape).
- `intervalIntegral.integral_eq_sub_of_hasDerivAt` (FTC-2,
  `MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`, per inventory §6);
  `intervalIntegral.integral_of_le`, `MeasureTheory.integral_Ioc_eq_integral_Ioo` (bridges).
- `hasDerivAt_circleMap (c R θ) : HasDerivAt (circleMap c R) (circleMap 0 R θ * I) θ`
  (`MeasureTheory/Integral/CircleIntegral.lean:98`); `circleMap c R θ = c + R * exp (θ * I)`.
- `Complex.exp_pi_mul_I : exp (π * I) = -1`
  (`Analysis/SpecialFunctions/Trigonometric/Basic.lean:1209`); `Complex.exp_mul_I`.
- Measurability of the kernel: no `MeasurableInv ℂ` instance found; route is
  `ContinuousOn.aestronglyMeasurable` on `{0}ᶜ` (open, conull) — resolved in spike (§10).

### 1.4 Complex analysis atoms

- `DifferentiableOn.hasFPowerSeriesOnBall {R : ℝ≥0} (hd : DifferentiableOn ℂ f (ball c R))
  (hR : 0 < R) : HasFPowerSeriesOnBall f (cauchyPowerSeries f c R) c R`
  (`Analysis/Complex/CauchyIntegral.lean:619`).
- `DifferentiableOn.analyticAt` (`:626`), `DifferentiableOn.analyticOnNhd` (`:632`),
  `analyticOnNhd_iff_differentiableOn (o : IsOpen s)` (`:668`).
- `HasFPowerSeriesOnBall.tendstoUniformlyOn {r' : ℝ≥0} (hf) (h : r' < r) :
  TendstoUniformlyOn (fun n y => p.partialSum n y) (fun y => f (x + y)) atTop (ball 0 r')`
  (`Analysis/Analytic/Basic.lean:916`; primed variant on `ball x r'` at `:964`).
- `FormalMultilinearSeries.partialSum`; 1-D evaluation `apply_eq_pow_smul_coeff` (used at
  `Analytic/Basic.lean:1123`) — partial sums are polynomial functions, entire.
- `tendstoUniformlyOn_tsum (hu : Summable u) (hfu : ∀ n x, x ∈ s → ‖f n x‖ ≤ u n)`
  (`Analysis/NormedSpace/FunctionSeries.lean:33`) — Weierstrass M-test.
- `TendstoLocallyUniformlyOn.differentiableOn` (`Analysis/Complex/LocallyUniformLimit.lean`,
  module doc `:20`) — uniform limits of holomorphic are holomorphic.
- Cauchy–Riemann bridge core: `hasFDerivAt_of_restrictScalars (h : HasFDerivAt f g' x)
  (H : f'.restrictScalars 𝕜 = g') : HasFDerivAt f f' x`
  (`Analysis/Calculus/FDeriv/RestrictScalars.lean:89`); `HasFDerivAt.restrictScalars` (`:56`).
  There is NO `Analysis/Complex/CauchyRiemann.lean` at the pin — the Wirtinger form is ours.
- `ContDiffOn.fderiv_of_isOpen (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hmn : m + 1 ≤ n)`
  (`Analysis/Calculus/ContDiff/Defs.lean:898`), `.continuousOn_fderiv_of_isOpen` (`:907`).
- `meromorphicOrderAt_zpow_id_sub_const {n : ℤ}` (`Analysis/Meromorphic/Order.lean:365`,
  `@[simp]`), `meromorphicOrderAt_mul` (`:429`), `meromorphicOrderAt_zpow` (`:481`) — the
  divisor-twist order bookkeeping is fully stocked.

### 1.5 Bump functions, PoU, shrinking

- `ContDiffBump (c : E)` (`Analysis/Calculus/BumpFunction/Basic.lean:70`): fields `rIn rOut`,
  `one_of_mem_closedBall` (`:137`), `support_eq : support f = ball c rOut` (`:151`),
  `tsupport_eq : tsupport f = closedBall c rOut` (`:157`); `ContDiffBump.contDiff` in
  `BumpFunction/Normed.lean`; `hasCompactSupport` available.
- `IsOpen.exists_smooth_support_eq` = alias of `IsOpen.exists_contDiff_support_eq`
  (`Analysis/Calculus/BumpFunction/FiniteDimension.lean:199`): for open `s ⊆ E` (finite-dim)
  there is `f : E → ℝ`, `ContDiff ℝ ∞ f`, `support f = s`, `range f ⊆ Icc 0 1` — the seed of
  the finite planar PoU (§7.1).
- `exists_subset_iUnion_closure_subset (hs : IsClosed s) (uo) (uf : point-finite) (us) :
  ∃ v, s ⊆ ⋃ v ∧ (∀ i, IsOpen (v i)) ∧ ∀ i, closure (v i) ⊆ u i` — `[NormalSpace X]`
  (`Topology/ShrinkingLemma.lean:216`); applied in the SUBTYPE `V` (metrizable ⇒ normal).
- Surface PoU (deliverable 4, availability check): `RS.exists_smoothPartitionOfUnity`
  (`Jacobian/Surface/RealSmooth.lean:119–122`, compiled): on `[T2Space X] [CompactSpace X]`
  surfaces, `∃ p : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) X univ, p.IsSubordinate U` for every open
  cover — via CC7's `isManifoldRealOfComplex` (`RealSmooth.lean:38`) and mathlib
  `SmoothPartitionOfUnity.exists_isSubordinate` (`Geometry/Manifold/PartitionOfUnity.lean:810`,
  footprint `[FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]`).
  **dolbeault-comparison consumes this directly; nothing more is needed from us.**

### 1.6 Project substrates consumed

- `Jacobian/Surface/RealSmooth.lean`: `isManifoldRealOfComplex`, `extChartAt_real_eq (rfl)`,
  `contMDiffAt_real_iff_contDiffAt` (`:69`) — ℝ-smoothness on `X` ⇔ `ContDiffAt ℝ` of the
  chart representative (in the SHARED `𝓘(ℂ)` charts), `contMDiffOn_real_of_holomorphicOn`.
- `Jacobian/Surface/Bridges.lean`: `contMDiffAt_iff_analyticAt` (`:81`),
  `contMDiffOn_iff_analyticOnNhd_of_subset_source` (`:149`).
- `Jacobian/Forms/Analyticity.lean`: `analyticAt_trans (he he' hzt hzs) :
  AnalyticAt ℂ (e ∘ e'.symm) z` (`:43`), `deriv_trans_comp` (chain rule for transition
  derivatives, `:65`) — reused verbatim for the `conj`-transition cocycle laws.
- `Jacobian/Meromorphic/` (built: `GermSpace`, `OrderEval`, `Predicates`): `MeroGermOn X U`,
  `mk`, `mk_eq_mk`, `restrict : →ₐ[ℂ]` with `restrict_mk/restrict_restrict/restrict_id`,
  `ord_mk/ord_restrict/ord_mul/ord_add/ord_neg`, `evalAt_add/mul/smul/restrict`,
  `holoRepr := fun x => evalAt φ x` with `holoRepr_contMDiffOn` (`OrderEval.lean:289`),
  `mk_holoRepr` (`:305`), `holoRepr_restrict` (`:313`), `MeromorphicAtX.inv/zpow`
  (`Predicates.lean:117/:123`). `LinSysOn D U : Submodule ℂ (MeroGermOn X U)` with carrier
  `{φ | ∀ x ∈ U, (-(D x) : WithTop ℤ) ≤ φ.ord x}` (mero design §5) — in flight.
- `docs/design/cech-cohomology.md` §4.1–4.2: `FinCover Ω`, `IsChartDisk`, `C0/C1/C2 D 𝒰`,
  `d0/d1`, `Z1/B1`, `H1Cover`, `subsingleton_h1Cover_iff : Subsingleton (H1Cover D 𝒰) ↔
  Z1 D 𝒰 ≤ B1 D 𝒰`, `LinSysOn.restrictL` — in flight; our `DiskAcyclic.lean` compiles only
  after `Jacobian/Cech/{Covers,Cochains}.lean` land (§3 build-order note).

---

## 2. Design decisions

### D1 — Regularity: everything is stated at `C^∞` (`ContDiff ℝ ∞` / `ContMDiff … ∞`)

Forster works in `ℰ = C^∞`; every consumer (dolbeault, finiteness) is `C^∞`. We do NOT track
finite regularity `n` through 13.1/13.2 (the internal derivative steps use `ContDiff ℝ 1`
hypotheses where that is what mathlib's lemma wants, but exported statements are `∞`). This
kills all `n+1 ≤ n'` arithmetic. Non-goal: `C^k` variants (trivial to add later if ever needed).

### D2 — The kernel and solution are DEFINITIONS, not just existence statements

`cauchyKernel w := (π * w)⁻¹` and `cauchyTransform g := cauchyKernel ⋆[mul ℝ ℂ] g` are named
`def`s with a lemma suite; 13.1/13.2 export `∃ u, …` forms as well (what consumers match on).
Rationale: the 13.2 recursion applies 13.1 to a SEQUENCE of cutoffs; a stable function-level
handle avoids `choose`-noise inside the induction. Sign audit (done twice, §5): with
`dz ∧ dz̄ = −2i dx∧dy`, Forster's `f(ζ) = (1/2πi)∬ g(z)/(z−ζ) dz∧dz̄` equals
`(cauchyKernel ⋆ g)(ζ) = ∫ g(ζ−w)/(πw) dA(w)`. The polar-FTC computation (§5) independently
confirms `∂̄(k ⋆ g) = g` with THESE signs.

### D3 — 13.2 for finite open balls only

`exists_dbar_solution_ball` is stated for `Metric.ball c R`, `0 < R < ∞`. The cech design's
`IsChartDisk` produces exactly finite balls (`chartAt ℂ x '' V = Metric.ball (chartAt ℂ x x) r`),
and no consumer needs the `ℂ = R = ∞` case (ℙ¹'s `H¹(ℂ,𝒪)=0` is not on our critical path; the
project computes `H¹` via the colimit + Leray on good covers). The exhaustion proof would extend
verbatim with radii `n`; documented non-goal.

### D4 — Wirtinger operators as plain functions `(ℂ → ℂ) → ℂ → ℂ`, junk-tolerant

`wirtingerDbar f z := (fderiv ℝ f z 1 + I * fderiv ℝ f z I) / 2` (and `wirtingerD` with `−`).
If `f` is not ℝ-differentiable at `z`, `fderiv = 0` and the value is junk `0` — harmless
because every exported statement carries the smoothness hypothesis anyway, and this makes
`wirtingerDbar` total (usable under integrals without piecewise definitions). Orientation
audit: `wirtingerDbar conj z = 1`, `wirtingerDbar id z = 0`, `wirtingerD id z = 1`. The
workhorse is the **decomposition lemma** `fderiv ℝ f z v = wirtingerD f z * v +
wirtingerDbar f z * conj v` (proved on the ℝ-basis `{1, I}` of ℂ), from which the chain rule,
the CR bridge, and the polar-integrand splitting all fall out by algebra.

### D5 — `Form01 X`: point-indexed (`chartAt`) coefficient families, junk-normalized to 0

```lean
structure Form01 (X) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] where
  coeffAt : X → ℂ → ℂ
  coeffAt_zero_off : ∀ x, ∀ z ∉ (chartAt ℂ x).target, coeffAt x z = 0
  contDiffOn_coeffAt : ∀ x, ContDiffOn ℝ ∞ (coeffAt x) (chartAt ℂ x).target
  compat : ∀ x y : X, ∀ z ∈ chartAt ℂ y '' ((chartAt ℂ x).source ∩ (chartAt ℂ y).source),
    coeffAt y z = (starRingEnd ℂ) (deriv (chartAt ℂ x ∘ (chartAt ℂ y).symm) z) *
      coeffAt x (chartAt ℂ x ((chartAt ℂ y).symm z))
```
- Point-indexed rather than atlas-indexed: every consumer works through `chartAt` (cech's
  `IsChartDisk` charts ARE `chartAt`s; mero is `chartAt`-based), and a plain `X`-indexed Pi
  avoids `∀ e ∈ atlas` dependent-family friction in `ext`/module instances. Transition data
  against arbitrary maximal-atlas charts is recovered on demand from `compat` +
  `deriv_trans_comp` (Forms's helper), which is exactly how `Form1.coeffIn_trans` is organized.
- Junk-normalization `coeffAt_zero_off` makes structure-`ext` mathematically honest (two forms
  with equal coefficients ON TARGETS are equal), which the quotient `H^{0,1}` in
  dolbeault-comparison needs.
- Instances `Zero/Add/Neg/SMul ℂ/AddCommGroup/Module ℂ`: pointwise; each structure field is
  closed under the operations (compat is ℂ-linear in the coefficients, `zero_off` trivially
  preserved). No mathlib instance can collide (our type).
- **Smooth only.** No analytic variant, no `(1,0)`+`(0,1)` direct sum, no 2-forms: the minimum
  dolbeault-comparison needs.

### D6 — The intrinsic `∂̄` is chart-local Wirtinger; domain is a hand-rolled `SmoothC X`

`SmoothC X := {f : X → ℂ // ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ f}` with OUR `AddCommGroup`/`Module ℂ`
instances (pointwise; closure by `ContMDiff` composition with the ℝ-smooth planar maps
`(+)`, `(c * ·)` through `contMDiff_iff_contDiff` (`Geometry/Manifold/ContMDiff/
NormedSpace.lean:66`) and `ContMDiff.comp`). Rationale: mathlib's
`Geometry/Manifold/Algebra/SmoothFunctions.lean:251` gives `Module 𝕜 C^n⟮I, N; 𝓘(𝕜,V), V⟯`
only when the target model is literally `𝓘(𝕜, V)` — for our target model `𝓘(ℝ, ℂ)` that
yields `Module ℝ`, NOT `Module ℂ`; adding a competing ℂ-instance on mathlib's type is the
restrictScalars-diamond trap the blueprint warns about. A private subtype dodges it entirely.
`dbar : SmoothC X →ₗ[ℂ] Form01 X`, `(dbar f).coeffAt x = wirtingerDbar (f ∘ (chartAt ℂ x).symm)`
on targets (0 off). ℂ-linearity of `wirtingerDbar` in `f` makes `dbar` ℂ-linear. `H^{0,1}` is
NOT defined here (dolbeault-comparison owns the quotient).

### D7 — Local ∂̄-equations are a pointwise chart-free predicate; no relative `Form01On`

```lean
def IsDbarAt (u : X → ℂ) (ω : Form01 X) (x : X) : Prop :=
  wirtingerDbar (u ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) = ω.coeffAt x (chartAt ℂ x x)
def IsDbarOn (u ω) (s : Set X) : Prop := ∀ x ∈ s, IsDbarAt u ω x
```
evaluated at the chart CENTER only — as `x` ranges over `s` every point is a center, and the
(0,1) chain rule shows the predicate is chart-independent and equivalent (for `u` smooth on an
open `s` inside one chart) to the full coefficient identity in that chart
(`isDbarOn_iff_eqOn_coeff`). This kills the need for an `Opens`-relative `(0,1)`-form theory:
local solvability, gluing of local solutions, and "difference of solutions is holomorphic" are
all statements about `IsDbarOn`. Dolbeault's globalization then uses `Form01.ofCoeffs` (D8)
to assemble a global form from local data — no relative forms anywhere.

### D8 — Constructor from covering coefficient data (`Form01CoeffData`), mirroring Forms

`Form01CoeffData X ι`: charts `ι → OpenPartialHomeomorph X ℂ` in `maximalAtlas 𝓘(ℂ) ω X`
covering `X`, coefficients `ι → ℂ → ℂ` smooth on targets, pairwise `conj`-compatible (same
shape as `Form1CoeffData`, `Jacobian/Forms/OfCoeffs.lean:35`, with `AnalyticOnNhd` ↦
`ContDiffOn ℝ ∞` and `deriv τ` ↦ `conj (deriv τ)`). `Form01.ofCoeffs` defines
`coeffAt x z := conj (deriv (e_{i(p)} ∘ (chartAt x).symm) z) * coeff_{i(p)} (e_{i(p)} p)` for
`z ∈ target`, `p := (chartAt x).symm z`, `i(p)` a chosen covering chart at `p` — pointwise in
`z`, so the data chart may vary across the target; local constancy of the formula (data-compat
+ `deriv_trans_comp`) gives smoothness and `compat`. This is the exact scheme Forms used for
`toSection`/`coeffInFun_toSection`; we transcribe with `conj` inserted. Dolbeault consumes this
to glue `∂̄(local solutions)`s and PoU-patched cocycle data into a global `Form01`.

### D9 — Disk acyclicity: planar Cousin atom + germ transport + divisor twist

The Čech-facing theorem (owed per cech §7/§11) is
`Subsingleton (H1Cover D 𝒱)` for `𝒱 : FinCover V`, `IsChartDisk V`. Route:
1. **Planar Cousin atom** (`exists_holo_splitting_ball`, §7.2): holomorphic cocycles on finite
   open covers of a planar ball split holomorphically — proved by finite smooth PoU splitting
   (§7.1) + `∂̄`-correction via 13.2. Pure ℂ, zero project imports: interface-independent even
   if cech's shapes move (risk containment).
2. **Germ transport** (`D = 0` case): cochain components are `LinSysOn 0`-germs on opens of the
   chart disk; `holoRepr` (mero) gives canonical analytic representatives, the Surface bridge
   moves them to planar holomorphic functions on the image opens; pointwise cocycle identities
   transfer through `evalAt_add/neg/restrict` rigidity; the planar splitting pulls back through
   `mk`/`mk_holoRepr`. Only sheaf-free pointwise reasoning — no `exists_glue` needed.
3. **Divisor twist** (`D` general, `[CompactSpace X] [T2Space X]`): `D` has finite support
   (CC2 `finiteSupport`), so `q w := ∏_{a ∈ S} (w − a) ^ (D (e.symm a))` is meromorphic with
   `divisor q = D|_V` in the chart; multiplication by the germ `t := mk (q ∘ e)` is a
   componentwise linear iso `C^•(D) ≅ C^•(0)` commuting with `d0/d1` (mero `restrict` is an
   `AlgHom`; orders via `meromorphicOrderAt_zpow_id_sub_const` + `_mul`), giving
   `Z1 D ≤ B1 D ⟺ Z1 0 ≤ B1 0` and the transfer via `subsingleton_h1Cover_iff`.
   We only build the one-directional maps and the commutation squares — no packaged complex
   equivalence.

### D10 — Instance hygiene, namespaces, imports

Planar files (`Wirtinger`, `CauchyKernel`, `SolveDisk`, `PlanarPoU`, `PlanarCousin`): NO
variables, NO project imports — mathlib only (so planar-stokes-atoms and residue-calculus can
import them without dragging in the manifold stack). Surface files:
`variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]`;
`[T2Space X]`/`[CompactSpace X]` ONLY in `DiskAcyclic.lean` (twist needs finite divisor
support), and `[ConnectedSpace X]` nowhere. Everything in `namespace RS`. Targeted imports per
CONVENTIONS: `Mathlib.Analysis.Calculus.ContDiff.Convolution`,
`Mathlib.Analysis.SpecialFunctions.PolarCoord`, `Mathlib.Analysis.Complex.CauchyIntegral`,
`Mathlib.Analysis.Calculus.BumpFunction.{Normed,FiniteDimension}`,
`Mathlib.Analysis.NormedSpace.FunctionSeries`, `Mathlib.Analysis.Complex.LocallyUniformLimit`,
`Mathlib.Topology.ShrinkingLemma`, plus project `Jacobian.Surface`, `Jacobian.Forms.Analyticity`
(surface files), `Jacobian.Cech.Cochains` + `Jacobian.Meromorphic` (DiskAcyclic only).

---

## 3. File plan (dependency order; estimated sizes)

```
Jacobian/Dbar.lean                  -- unit root: imports + 5–15 line API docstring       (~30)
Jacobian/Dbar/Wirtinger.lean        -- planar Wirtinger API, CR bridge, chain rule        (~330)
Jacobian/Dbar/CauchyKernel.lean     -- kernel, LocallyIntegrable, Cauchy–Pompeiu, 13.1    (~650)
Jacobian/Dbar/SolveDisk.lean        -- 13.2: cutoff extension, recursion, telescoping     (~450)
Jacobian/Dbar/PlanarPoU.lean        -- finite smooth PoU on open planar sets, ext-by-0    (~260)
Jacobian/Dbar/PlanarCousin.lean     -- smooth + holomorphic cocycle splitting on a ball   (~320)
Jacobian/Dbar/Form01.lean           -- Form01, module instances, ofCoeffs constructor     (~420)
Jacobian/Dbar/Operator.lean         -- SmoothC, dbar, IsDbarAt/On, chart-disk solvability,
                                    --   holomorphic-of-∂̄-closed                          (~380)
Jacobian/Dbar/DiskAcyclic.lean      -- germ transport, divisor twist, Subsingleton H1Cover(~550)
```
Import spine: `Wirtinger ← CauchyKernel ← SolveDisk ← PlanarCousin` (also `← PlanarPoU`);
`Form01` imports Surface + Forms.Analyticity; `Operator` imports `Wirtinger`, `SolveDisk`,
`Form01`; `DiskAcyclic` imports `PlanarCousin`, `Operator`, `Jacobian.Cech.Cochains`,
`Jacobian.Meromorphic`. **Build order note**: files 1–6 (planar + Form01/Operator) compile
against mathlib + ALREADY-BUILT units only; `DiskAcyclic.lean` is written last and gated on the
cech unit landing `Covers.lean`+`Cochains.lean` (coordinate; if cech slips, the unit root
temporarily exports everything except `DiskAcyclic` — but the unit is DONE only with it).

---

## 4. Exports — exact signatures

Throughout `f g u : ℂ → ℂ`, `z w c : ℂ`, `r R : ℝ`, `s V W : Set ℂ`; conjugation is
`starRingEnd ℂ` (written `conj` here for brevity).

### 4.1 `Wirtinger.lean` (namespace `RS`; mathlib-only)

```lean
noncomputable def wirtingerD (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I) / 2
noncomputable def wirtingerDbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) / 2

/-- ℝ-linear maps ℂ → ℂ decompose as `v ↦ a v + b v̄` (values on the basis 1, I). -/
theorem clm_apply_eq_add_conj_smul (L : ℂ →L[ℝ] ℂ) (v : ℂ) :
    L v = (L 1 - Complex.I * L Complex.I) / 2 * v
        + (L 1 + Complex.I * L Complex.I) / 2 * conj v
/-- THE workhorse: the Wirtinger decomposition of the real differential. -/
theorem fderiv_apply_eq_wirtinger (hf : DifferentiableAt ℝ f z) (v : ℂ) :
    fderiv ℝ f z v = wirtingerD f z * v + wirtingerDbar f z * conj v

theorem wirtingerDbar_add (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtingerDbar (f + g) z = wirtingerDbar f z + wirtingerDbar g z
theorem wirtingerDbar_sub / wirtingerDbar_neg / wirtingerDbar_const_mul (c : ℂ) …
    -- const_mul: wirtingerDbar (fun w => c * f w) z = c * wirtingerDbar f z
theorem wirtingerDbar_congr_nhds (h : f =ᶠ[𝓝 z] g) : wirtingerDbar f z = wirtingerDbar g z
theorem wirtingerDbar_zero : wirtingerDbar 0 z = 0    (+ `_const`)

-- holomorphy ↔ CR
theorem wirtingerDbar_eq_zero_of_differentiableAt (hf : DifferentiableAt ℂ f z) :
    wirtingerDbar f z = 0
theorem wirtingerD_eq_deriv (hf : DifferentiableAt ℂ f z) : wirtingerD f z = deriv f z
/-- Cauchy–Riemann bridge (hand-built; no mathlib counterpart at the pin). -/
theorem differentiableAt_of_wirtingerDbar_eq_zero (hf : DifferentiableAt ℝ f z)
    (h : wirtingerDbar f z = 0) : DifferentiableAt ℂ f z
theorem differentiableAt_iff_wirtingerDbar_eq_zero :
    DifferentiableAt ℂ f z ↔ DifferentiableAt ℝ f z ∧ wirtingerDbar f z = 0
theorem differentiableOn_of_wirtingerDbar_eq_zero (hs : IsOpen s)
    (hf : ∀ z ∈ s, DifferentiableAt ℝ f z) (h : ∀ z ∈ s, wirtingerDbar f z = 0) :
    DifferentiableOn ℂ f s
theorem analyticOnNhd_of_wirtingerDbar_eq_zero (hs : IsOpen s) (hf h as above) :
    AnalyticOnNhd ℂ f s          -- via DifferentiableOn.analyticOnNhd

/-- (0,1) chain rule along a holomorphic map — the transition law of `(0,1)`-coefficients. -/
theorem wirtingerDbar_comp_differentiableAt {τ : ℂ → ℂ} (hF : DifferentiableAt ℝ f (τ z))
    (hτ : DifferentiableAt ℂ τ z) :
    wirtingerDbar (f ∘ τ) z = conj (deriv τ z) * wirtingerDbar f (τ z)
theorem wirtingerD_comp_differentiableAt … = deriv τ z * wirtingerD f (τ z)   -- companion

-- regularity of the operator
theorem contDiffOn_wirtingerDbar (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) :
    ContDiffOn ℝ ∞ (wirtingerDbar f) s
theorem continuous_wirtingerDbar (hf : ContDiff ℝ ∞ f) : Continuous (wirtingerDbar f)
theorem hasCompactSupport_wirtingerDbar (hf : HasCompactSupport f) :
    HasCompactSupport (wirtingerDbar f)      -- support ⊆ tsupport f, via fderiv support
```

### 4.2 `CauchyKernel.lean` (namespace `RS`; mathlib-only)

```lean
noncomputable def cauchyKernel : ℂ → ℂ := fun w => (Real.pi * w)⁻¹

theorem aestronglyMeasurable_cauchyKernel : AEStronglyMeasurable cauchyKernel volume
theorem locallyIntegrable_cauchyKernel : MeasureTheory.LocallyIntegrable cauchyKernel volume

/-- Cauchy–Pompeiu identity for compactly supported C¹ functions (polar-FTC proof, §5). -/
theorem cauchyPompeiu (hg : ContDiff ℝ 1 g) (hcs : HasCompactSupport g) (z : ℂ) :
    ∫ w : ℂ, cauchyKernel w * wirtingerDbar g (z - w) = g z

noncomputable def cauchyTransform (g : ℂ → ℂ) : ℂ → ℂ :=
  cauchyKernel ⋆[ContinuousLinearMap.mul ℝ ℂ] g
theorem contDiff_cauchyTransform (hg : ContDiff ℝ ∞ g) (hcs : HasCompactSupport g) :
    ContDiff ℝ ∞ (cauchyTransform g)
/-- ∂̄ commutes with the transform: `∂̄(k ⋆ g) = k ⋆ ∂̄g` (differentiation under the ∫). -/
theorem wirtingerDbar_cauchyTransform (hg : ContDiff ℝ ∞ g) (hcs : HasCompactSupport g) (z) :
    wirtingerDbar (cauchyTransform g) z = ∫ w : ℂ, cauchyKernel w * wirtingerDbar g (z - w)
/-- Forster 13.1. -/
theorem wirtingerDbar_cauchyTransform_eq (hg : ContDiff ℝ ∞ g) (hcs : HasCompactSupport g) :
    ∀ z, wirtingerDbar (cauchyTransform g) z = g z
theorem exists_dbar_solution_of_hasCompactSupport (hg : ContDiff ℝ ∞ g)
    (hcs : HasCompactSupport g) : ∃ u, ContDiff ℝ ∞ u ∧ ∀ z, wirtingerDbar u z = g z
```

### 4.3 `SolveDisk.lean` (namespace `RS`; mathlib-only)

```lean
/-- Extension by zero of a bump-cutoff of a function smooth on an open set. -/
theorem contDiff_indicator_bump_smul {c : ℂ} (φ : ContDiffBump c) (hs : IsOpen s)
    (hg : ContDiffOn ℝ ∞ g s) (hsub : Metric.closedBall c φ.rOut ⊆ s) :
    ContDiff ℝ ∞ (s.indicator fun z => φ z • g z)
    -- + HasCompactSupport, + eqOn: = g on closedBall c φ.rIn where φ = 1

/-- Forster 13.2: Dolbeault's lemma on a finite open disk. -/
theorem exists_dbar_solution_ball (hR : 0 < R) (hg : ContDiffOn ℝ ∞ g (Metric.ball c R)) :
    ∃ u : ℂ → ℂ, ContDiffOn ℝ ∞ u (Metric.ball c R) ∧
      ∀ z ∈ Metric.ball c R, wirtingerDbar u z = g z
```
(the exhaustion radii, the recursive sequence, and the telescoping sum are `private`; §6.)

### 4.4 `PlanarPoU.lean` (namespace `RS`; mathlib-only)

```lean
/-- Finite smooth partition of unity on an open planar set, subordinate with V-relative
closed supports (the `∀ᶠ`-clause is the consumable form of `closure_V (supp ψ i) ⊆ W i`). -/
theorem exists_smooth_partition_of_finite_cover {V : Set ℂ} (hV : IsOpen V) {n : ℕ}
    {W : Fin n → Set ℂ} (hWo : ∀ i, IsOpen (W i)) (hWV : ∀ i, W i ⊆ V)
    (hcov : V ⊆ ⋃ i, W i) :
    ∃ ψ : Fin n → ℂ → ℝ,
      (∀ i, ContDiffOn ℝ ∞ (ψ i) V) ∧ (∀ i z, 0 ≤ ψ i z) ∧
      (∀ z ∈ V, ∑ i, ψ i z = 1) ∧
      (∀ i, Function.support (ψ i) ⊆ W i) ∧
      (∀ i, ∀ z ∈ V, z ∉ W i → ∀ᶠ w in 𝓝 z, ψ i w = 0)

/-- Extension-by-zero across the support boundary (the gluing helper for splittings). -/
theorem contDiffOn_indicator_smul_of_eventually_zero {U W V : Set ℂ} (hU : IsOpen U)
    (hW : IsOpen W) {ψ : ℂ → ℝ} {f : ℂ → ℂ} (hUV : U ⊆ V)
    (hψ : ContDiffOn ℝ ∞ ψ V) (hf : ContDiffOn ℝ ∞ f (U ∩ W))
    (hvan : ∀ z ∈ U, z ∉ W → ∀ᶠ w in 𝓝 z, ψ w = 0) :
    ContDiffOn ℝ ∞ (W.indicator fun z => ψ z • f z) U
```

### 4.5 `PlanarCousin.lean` (namespace `RS`; mathlib-only)

Cocycle convention matched to cech's `d0` (`(d0 h)_{ij} = h_j − h_i`) and `Z1.rel_res`
(`f_{jk} − f_{ik} + f_{ij} = 0`, i.e. `f i k = f i j + f j k`).

```lean
variable {n : ℕ} {W : Fin n → Set ℂ} {f : Fin n → Fin n → ℂ → ℂ}

/-- Smooth splitting: `H¹(finite cover of open V, ℰ) = 0` (Forster 12.6 planar). -/
theorem exists_smooth_splitting {V : Set ℂ} (hV : IsOpen V) (hWo : ∀ i, IsOpen (W i))
    (hWV : ∀ i, W i ⊆ V) (hcov : V ⊆ ⋃ i, W i)
    (hf : ∀ i j, ContDiffOn ℝ ∞ (f i j) (W i ∩ W j))
    (hcoc : ∀ i j k, ∀ z ∈ W i ∩ W j ∩ W k, f i k z = f i j z + f j k z) :
    ∃ h : Fin n → ℂ → ℂ, (∀ i, ContDiffOn ℝ ∞ (h i) (W i)) ∧
      ∀ i j, ∀ z ∈ W i ∩ W j, f i j z = h j z - h i z

/-- Holomorphic splitting on a ball (Forster 13.4, planar core; = disk Cousin I). -/
theorem exists_holo_splitting_ball {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hWo : ∀ i, IsOpen (W i)) (hWb : ∀ i, W i ⊆ Metric.ball c R)
    (hcov : Metric.ball c R ⊆ ⋃ i, W i)
    (hf : ∀ i j, DifferentiableOn ℂ (f i j) (W i ∩ W j))
    (hcoc : as above) :
    ∃ u : Fin n → ℂ → ℂ, (∀ i, DifferentiableOn ℂ (u i) (W i)) ∧
      ∀ i j, ∀ z ∈ W i ∩ W j, f i j z = u j z - u i z
```
(Internal: `f i i = 0` and `f j i = −f i j` on overlaps, derived from `hcoc`.)

### 4.6 `Form01.lean` (namespace `RS`; `variable {X} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]`)

```lean
structure Form01 (X) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] where
  coeffAt : X → ℂ → ℂ
  coeffAt_zero_off : ∀ x, ∀ z ∉ (chartAt ℂ x).target, coeffAt x z = 0
  contDiffOn_coeffAt : ∀ x, ContDiffOn ℝ ∞ (coeffAt x) (chartAt ℂ x).target
  compat : ∀ x y : X, ∀ z ∈ ⇑(chartAt ℂ y) '' ((chartAt ℂ x).source ∩ (chartAt ℂ y).source),
    coeffAt y z = (starRingEnd ℂ) (deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) z) *
      coeffAt x (chartAt ℂ x ((chartAt ℂ y).symm z))

@[ext] theorem Form01.ext {ω η : Form01 X}
    (h : ∀ x, ∀ z ∈ (chartAt ℂ x).target, ω.coeffAt x z = η.coeffAt x z) : ω = η
instance : Zero (Form01 X) / Add / Neg / SMul ℂ / AddCommGroup / Module ℂ
@[simp] theorem coeffAt_add / coeffAt_smul / coeffAt_zero …

/-- Covering compatible coefficient data (mirror of `Form1CoeffData` with conj-rule). -/
structure Form01CoeffData (X) [instances as above] (ι : Type*) where
  chart : ι → OpenPartialHomeomorph X ℂ
  mem_maximalAtlas : ∀ i, chart i ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X
  exists_mem : ∀ x : X, ∃ i, x ∈ (chart i).source
  coeff : ι → ℂ → ℂ
  contDiffOn : ∀ i, ContDiffOn ℝ ∞ (coeff i) (chart i).target
  compat : ∀ i j, ∀ x ∈ (chart i).source ∩ (chart j).source,
    coeff j (chart j x) =
      (starRingEnd ℂ) (deriv (⇑(chart i) ∘ ⇑(chart j).symm) (chart j x)) * coeff i (chart i x)

noncomputable def Form01.ofCoeffs {ι} (D : Form01CoeffData X ι) : Form01 X
theorem Form01.coeffAt_ofCoeffs {ι} (D : Form01CoeffData X ι) {x : X} {i : ι}
    (hx : x ∈ (D.chart i).source) {z : ℂ}
    (hz : z ∈ ⇑(chartAt ℂ x) '' ((D.chart i).source ∩ (chartAt ℂ x).source)) :
    (Form01.ofCoeffs D).coeffAt x z =
      (starRingEnd ℂ) (deriv (⇑(D.chart i) ∘ ⇑(chartAt ℂ x).symm) z) *
        D.coeff i (D.chart i ((chartAt ℂ x).symm z))
```

### 4.7 `Operator.lean` (namespace `RS`; same variables)

```lean
def SmoothC (X) [instances] : Type _ := {f : X → ℂ // ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f}
instance : FunLike (SmoothC X) X ℂ ; instance : AddCommGroup (SmoothC X)
instance : Module ℂ (SmoothC X)

/-- The intrinsic ∂̄, chart-locally the planar Wirtinger operator. -/
noncomputable def dbar : SmoothC X →ₗ[ℂ] Form01 X
@[simp] theorem coeffAt_dbar (f : SmoothC X) (x : X) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) :
    (dbar f).coeffAt x z = wirtingerDbar (⇑f ∘ ⇑(chartAt ℂ x).symm) z

def IsDbarAt (u : X → ℂ) (ω : Form01 X) (x : X) : Prop :=
  wirtingerDbar (u ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) = ω.coeffAt x (chartAt ℂ x x)
def IsDbarOn (u : X → ℂ) (ω : Form01 X) (s : Set X) : Prop := ∀ x ∈ s, IsDbarAt u ω x

theorem isDbarAt_congr_chart …          -- chart-independence via wirtingerDbar_comp (internal)
theorem isDbarOn_iff_eqOn_coeff {x₀ : X} {s : Set X} (hs : IsOpen s)
    (hsub : s ⊆ (chartAt ℂ x₀).source) {u ω} (hu : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ u s) :
    IsDbarOn u ω s ↔
      Set.EqOn (wirtingerDbar (u ∘ ⇑(chartAt ℂ x₀).symm)) (ω.coeffAt x₀) (⇑(chartAt ℂ x₀) '' s)
theorem isDbarOn_dbar (f : SmoothC X) : IsDbarOn ⇑f (dbar f) Set.univ
theorem dbar_eq_iff {f : SmoothC X} {ω} : dbar f = ω ↔ IsDbarOn ⇑f ω Set.univ

/-- Deliverable (iv): a smooth ∂̄-closed function is holomorphic. -/
theorem contMDiffOn_omega_of_isDbarOn_zero {u : X → ℂ} {s : Set X} (hs : IsOpen s)
    (hu : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ u s) (h : IsDbarOn u 0 s) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω u s
/-- Difference of two local ∂̄-solutions is holomorphic (dolbeault's cocycle source). -/
theorem contMDiffOn_omega_sub_of_isDbarOn {u v : X → ℂ} {ω} {s} (hs : IsOpen s)
    (hu hv : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ _ s)
    (h₁ : IsDbarOn u ω s) (h₂ : IsDbarOn v ω s) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (u - v) s

/-- Chart-disk local solvability on X (13.2 transported; `IsChartDisk`-unpacked so this file
does not depend on cech). -/
theorem exists_dbar_solution_chart_ball {x₀ : X} {r : ℝ} (hr : 0 < r) {V : Set X}
    (hVs : V ⊆ (chartAt ℂ x₀).source)
    (hVim : ⇑(chartAt ℂ x₀) '' V = Metric.ball (chartAt ℂ x₀ x₀) r) (ω : Form01 X) :
    ∃ u : X → ℂ, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ u V ∧ IsDbarOn u ω V
```

### 4.8 `DiskAcyclic.lean` (namespace `RS`; adds `[T2Space X]`, `[CompactSpace X]` where noted; imports cech + mero)

```lean
-- germ/function bridge helpers (Compat-flavored; candidates for upstreaming to mero)
theorem meromorphicOnX_of_contMDiffOn_omega {U : Set X} (hU : IsOpen U) {u : X → ℂ}
    (hu : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω u U) : MeromorphicOnX u U
theorem mk_mem_linSysOn_zero {U} (hU : IsOpen U) {u} (hu : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω u U) :
    MeroGermOn.mk u (…) ∈ LinSysOn 0 U

/-- Acyclicity for 𝒪 (no compactness needed). -/
theorem subsingleton_h1Cover_zero_of_isChartDisk {V : Opens X} (hV : IsChartDisk V)
    (𝒱 : FinCover V) : Subsingleton (H1Cover (0 : Divisor X) 𝒱)

-- the divisor twist (private machinery): for e := chartAt ℂ x₀ the IsChartDisk chart,
--   S := (D.support ∩ V) as a Finset (finiteSupport, [CompactSpace X] [T2Space X]),
--   q : ℂ → ℂ := fun w => ∏ a ∈ S.image e, (w - a) ^ (D (e.symm a)),
--   twistGerm D hV : MeroGermOn X ↑V := mk (q ∘ e) …  with  ord_twistGerm : ord = D x on V
-- one-directional twisted maps C1 D 𝒱 → C1 0 𝒱 (and C0), commuting with d0/d1/restrictL.

/-- MAIN deliverable (owed to cech §7 / consumed by dolbeault's Leray 12.8):
disk acyclicity of the Čech complex of `𝒪_D` on chart disks. -/
theorem subsingleton_h1Cover_of_isChartDisk [T2Space X] [CompactSpace X] {V : Opens X}
    (hV : IsChartDisk V) (D : Divisor X) (𝒱 : FinCover V) :
    Subsingleton (H1Cover D 𝒱)
```

---

## 5. Proof plan: `cauchyPompeiu` + 13.1 (CauchyKernel.lean) — the analytic crux

Fix `g` C¹ with compact support, `z : ℂ`; write `h := wirtingerDbar g` (continuous by
`ContDiffOn.continuousOn_fderiv_of_isOpen` on `univ`, compactly supported by
`hasCompactSupport_wirtingerDbar`), `k := cauchyKernel`. Choose `R'` with
`tsupport g ⊆ ball 0 R₀` and set `R' := ‖z‖ + R₀ + 1`, so `w ↦ h (z − w)` vanishes for
`‖w‖ ≥ R'`.

**Step 0 (kernel measurability).** `k` is continuous on `{0}ᶜ` (open); `{0}` is `volume`-null.
`aestronglyMeasurable_cauchyKernel` via `ContinuousOn.aestronglyMeasurable` on the measurable
conull set (restrict/mono plumbing; the spike resolved the exact incantation, §10).

**Step 1 (local integrability).** `locallyIntegrable_iff` (ℂ is locally compact): enough that
`IntegrableOn k K` for compact `K ⊆ ball 0 ρ`. `IntegrableOn k (ball 0 ρ)`: AESM from step 0;
finiteness of `∫⁻ ‖k‖ₑ` by `Complex.lintegral_comp_polarCoord_symm` applied to
`F := (ball 0 ρ).indicator (fun w => ‖k w‖ₑ)`:
`∫⁻ F = ∫⁻ p in Ioi 0 ×ˢ Ioo (−π) π, ENNReal.ofReal p.1 • F (polar.symm p)`; on the target
`‖k (polar.symm p)‖ = (π p.1)⁻¹` (`norm_polarCoord_symm`), so the integrand is
`ofReal (p.1) * (indicator (p.1 < ρ)) * ofReal (π p.1)⁻¹ ≤ π⁻¹ · indicator {p.1 < ρ}`;
`∫⁻ ≤ π⁻¹ · volume (Ioo 0 ρ ×ˢ Ioo (−π) π) = π⁻¹ · ρ · 2π < ∞` (product-measure of a
rectangle; `Measure.volume_eq_prod`, `Real.volume_Ioo`). No layer-cake, no polarization tricks.

**Step 2 (the transform and its derivative).** `u := k ⋆[mul ℝ ℂ] g`. By
`HasCompactSupport.contDiff_convolution_right`, `ContDiff ℝ ∞ u`. By
`HasCompactSupport.hasFDerivAt_convolution_right` (𝕜 = ℝ),
`fderiv ℝ u z = (k ⋆[(mul ℝ ℂ).precompR ℂ] fderiv ℝ g) z`, and by
`convolution_precompR_apply` (kernel locally integrable ✓, `fderiv ℝ g` continuous with
compact support ✓ `HasCompactSupport.fderiv`): for every `v`,
`fderiv ℝ u z v = ∫ w, k w * (fderiv ℝ g (z − w) v)`. Take `v = 1` and `v = I`, combine with
`½(· + I·)`: since both component integrands are integrable
(`HasCompactSupport.convolutionExists_right` at the functions `w ↦ fderiv g w 1`, `w ↦ fderiv
g w I`), `integral_add`/`integral_const_mul` give
`wirtingerDbar u z = ∫ w, k w * wirtingerDbar g (z − w)` — `wirtingerDbar_cauchyTransform`.
(Formal note: `(mul ℝ ℂ) (k w) (·)` is literally `k w * ·`, so `convolution_def` unfolds to
the display above; spiked.)

**Step 3 (polar rewrite).** Apply `Complex.integral_comp_polarCoord_symm` to
`F w := k w * h (z − w)`:
`∫ w, F w = ∫ p in polarCoord.target, p.1 • F (Complex.polarCoord.symm p)` — the set is the
REAL `polarCoord.target`, and `polarCoord.target = Ioi 0 ×ˢ Ioo (−π) π` is `rfl` (spiked).
On the target `p = (r, θ)` with `r > 0`: `polar.symm p = r·(cos θ + sin θ·I) =
circleMap 0 r θ = r * exp (θ I)` (`Complex.polarCoord_symm_apply`, `Complex.exp_mul_I`), and
`r • k (r e^{iθ}) = r / (π r e^{iθ}) = π⁻¹ * exp (−θ I)` (helper `cauchyKernel_smul_polar`;
`exp ≠ 0`, `r ≠ 0`). By `setIntegral_congr_fun` on the open target:
`∫ w, F w = π⁻¹ • ∫ p in T, exp (−p.2 I) * h (z − circleMap 0 p.1 p.2)`, `T := Ioi 0 ×ˢ Ioo (−π) π`.

**Step 4 (Wirtinger split of the integrand).** Set `G : ℝ × ℝ → ℂ`,
`G p := g (z − circleMap 0 p.1 p.2)`. Two 1-D derivative computations (`HasDerivAt.comp` with
the affine inner map in `r`; `hasDerivAt_circleMap` in `θ`), then `fderiv_apply_eq_wirtinger`:
- `Gr p := −(fderiv ℝ g (z − re^{iθ})) (e^{iθ})`   satisfies `HasDerivAt (G (·, θ)) (Gr p) r`;
- `Gθ p := −(fderiv ℝ g (z − re^{iθ})) (i r e^{iθ})` satisfies `HasDerivAt (G (r, ·)) (Gθ p) θ`.
Wirtinger decomposition of `L := fderiv ℝ g (z − re^{iθ})` on the vectors `e^{iθ}`, `ire^{iθ}`:
`Gr = −(wD·e^{iθ} + w̄·e^{−iθ})`, `(i r)⁻¹ Gθ = −wD·e^{iθ} + w̄·e^{−iθ}` (with
`w̄ := wirtingerDbar g (z−re^{iθ})`, `conj (i r e^{iθ}) = −i r e^{−iθ}`). Hence pointwise on `T`
`exp (−θI) * h (z − re^{iθ}) = ½ ((i r)⁻¹ * Gθ p − Gr p)`  (*)
— pure algebra in ℂ, `r ≠ 0`.

**Step 5 (integrability on T).** Both `Gr` and `(i r)⁻¹ Gθ` are continuous on `T` (the `r`
factor in `Gθ` cancels the `(ir)⁻¹`), bounded by `M := sup ‖fderiv ℝ g‖` (compact support ⇒
finite), and vanish for `p.1 ≥ R'`. So each is `IntegrableOn` on `T`: bounded AESM functions
supported in the finite-measure box `Ioc 0 R' ×ˢ Ioo (−π) π` (`Measure.integrableOn_of_bounded`
+ indicator congruence). This justifies splitting `∫_T (*)` into two integrals.

**Step 6 (the θ-leg vanishes).** `A := ∫ p in T, (i p.1)⁻¹ * Gθ p`. `T = Ioi 0 ×ˢ Ioo (−π) π`
with `volume = volume.prod volume` on `ℝ × ℝ` (definitional, `rfl`; spiked);
`setIntegral_prod` (r outer):
`A = ∫ r in Ioi 0, (i r)⁻¹ * ∫ θ in Ioo (−π) π, Gθ (r, θ)`. Inner: `integral_Ioc_eq_integral_Ioo`
backwards + `intervalIntegral.integral_of_le` + FTC-2 `integral_eq_sub_of_hasDerivAt`
(the θ-derivative from step 4, continuous integrand ⇒ `IntervalIntegrable` by
`ContinuousOn.intervalIntegrable`): `= G (r, π) − G (r, −π) = g (z + r) − g (z + r) = 0`
(`circleMap 0 r (±π) = r·exp(±πI) = −r`, `Complex.exp_pi_mul_I` and its inverse). So `A = 0`.

**Step 7 (the r-leg telescopes).** `B := ∫ p in T, Gr p`. Here the iteration must be θ-OUTER;
mathlib has no `setIntegral_prod_symm` at the pin, so: extend to the full plane by indicators,
`B = ∫ r, ∫ θ, ind p * Gr p` (via `setIntegral_prod` + `integral_indicator`), then
`integral_integral_swap` (uncurried integrand integrable, step 5) to get
`B = ∫ θ in Ioo (−π) π, ∫ r in Ioi 0, Gr (r, θ)`. Inner (fixed θ): `Gr (·, θ)` is continuous,
vanishes for `r ≥ R'`; FTC-2 on `[0, R']`: `∫ r in (0)..(R'), Gr = G (R', θ) − G (0, θ) =
0 − g z = −g z`; interval→`Ioc`→`Ioi` by support (`setIntegral_eq_of_eqOn_zero` off `Ioc 0 R'`).
So `B = ∫ θ in Ioo (−π) π, (−g z) = −(2π) g z` (`integral_const`, `Real.volume_Ioo`).

**Step 8 (assembly).** `∫ w, F w = π⁻¹ • (½ (A − B)) = π⁻¹ · ½ · 2π · g z = g z`. ∎

**13.1**: `wirtingerDbar_cauchyTransform_eq := (step 2) ▸ cauchyPompeiu (hg.of_le one) hcs`;
`exists_dbar_solution_of_hasCompactSupport := ⟨cauchyTransform g, contDiff_cauchyTransform, …⟩`.

Fallback ladder for this section (§9 R1): if the convolution API fights at `𝕜 = ℝ, G = ℂ`
(spike says it does not), replace step 2 by a manual
`hasFDerivAt_integral_of_dominated_of_fderiv_le` argument (`Analysis/Calculus/
ParametricIntegral.lean`, same file mathlib's own proof uses) — the dominating function is
`‖k‖·M·(indicator of a compact)`, identical to step 5's bound.

---

## 6. Proof plan: `exists_dbar_solution_ball` (SolveDisk.lean) — Forster 13.2

Fix `c`, `R > 0`, `g` smooth on `B := ball c R`. Radii `ρ n := R − R / (n + 2)`
(`0 < ρ 0 = R/2`, strictly monotone, `→ R`, `ρ n < R`); write `Bₙ := ball c (ρ n)`,
`B̄ₙ := closedBall c (ρ n)`. Note `B̄ₙ ⊆ B_{n+1}` and `⋃ₙ Bₙ = B` (any `‖w−c‖ < R` is `< ρ n`
for large `n`).

**Step 1 (cutoffs).** `φ n : ContDiffBump c` with `rIn := ρ (n+1)`, `rOut := (ρ (n+1) + ρ (n+2))/2 < ρ (n+2) < R`.
`gₙ := B.indicator (fun w => φ n w • g w)`: by `contDiff_indicator_bump_smul` (§4.3; proof:
`ℂ = B ∪ (closedBall c (φ n).rOut)ᶜ`, on the open `B` the function is locally `φ • g` — smooth;
on the open complement of the closed ball it is locally `0` since `tsupport (φ n) = closedBall`
(`ContDiffBump.tsupport_eq`); `ContDiffAt` is local), `ContDiff ℝ ∞ gₙ`,
`HasCompactSupport gₙ` (support ⊆ `closedBall c (φ n).rOut`), and `gₙ = g` on `B̄_{n+1}`
(`ContDiffBump.one_of_mem_closedBall`, membership `B̄_{n+1} ⊆ B`).

**Step 2 (raw solutions).** `fₙ := cauchyTransform gₙ`: `ContDiff ℝ ∞ fₙ` and
`wirtingerDbar fₙ = gₙ` everywhere (13.1); in particular `= g` on `B̄_{n+1} ⊇ B̄ₙ`.

**Step 3 (the corrected sequence — recursion).** Build `F : ℕ → (ℂ → ℂ)` with invariants
  (i) `ContDiff ℝ ∞ (F n)`;
  (ii) `∀ z ∈ Bₙ₊₁… ` precisely: `wirtingerDbar (F n) = g` on `B̄_{n+1}`;
  (iii) `∀ z ∈ B̄ₙ, ‖F (n+1) z − F n z‖ ≤ (1/2)^(n+1)`.
Lean shape: a `private def solStep` + `Nat.rec` into the Σ-type
`Σ' F : ℂ → ℂ, ContDiff ℝ ∞ F ∧ EqOn (wirtingerDbar F) g (B̄_{n+1})` and a separate lemma for
(iii), OR (chosen, simpler): define the whole sequence with its invariants as a single
recursively-chosen function via `Nat.rec` carrying the full `PProd` of properties; the doc
fixes the recursion step:
- `F 0 := f 0`. Given `F n` with (i),(ii):
- `d := f (n+1) − F n` satisfies `wirtingerDbar d = 0` on the OPEN `B_{n+1}` ⊇ `B̄ₙ`
  (both solve `∂̄ = g` there, `wirtingerDbar_sub`), hence `DifferentiableOn ℂ d B_{n+1}` (CR
  bridge `differentiableOn_of_wirtingerDbar_eq_zero`).
- `DifferentiableOn.hasFPowerSeriesOnBall` (radius `⟨ρ (n+1), _⟩ : ℝ≥0`): power series `p` for
  `d` on `B_{n+1}`; `HasFPowerSeriesOnBall.tendstoUniformlyOn` with `r' := ρ n < ρ (n+1)`:
  partial sums `Pₘ (w) := p.partialSum m (w − c)` converge to `d` uniformly on `B̄ₙ`… note the
  mathlib statement converges on `ball 0 r'` in the shifted variable and against `y ↦ d (c+y)`;
  `r' := (ρ n + ρ (n+1))/2` makes `B̄ₙ ⊆ c +ᵥ ball 0 r'` and uniform convergence restricts.
  Pick `m` with `‖d w − Pₘ w‖ ≤ (1/2)^(n+1)` on `B̄ₙ` (uniform convergence, `Metric.tendstoUniformlyOn_iff`).
- `Pₘ` is an entire polynomial function: `p.partialSum m (· − c)` is a finite sum of
  `w ↦ (w−c)^k • p.coeff k` (`apply_eq_pow_smul_coeff`), so `ContDiff ℝ ∞` and
  `Differentiable ℂ`, hence `wirtingerDbar Pₘ = 0` EVERYWHERE.
- `F (n+1) := f (n+1) − Pₘ`. Then (i) ✓; (ii): on `B̄_{n+2}`,
  `wirtingerDbar (F (n+1)) = g − 0` ✓; (iii): `F (n+1) − F n = d − Pₘ` ✓ on `B̄ₙ`.

**Step 4 (the limit).** For `z ∈ B`, pick `N` with `z ∈ B_N`; for `n ≥ N` the increments obey
(iii) (as `B̄ₙ ⊇ B̄_N ∋ z` — monotone), so `(F n z)` is Cauchy; define
`u z := limUnder atTop (fun n => F n z)` (junk-free: the limit exists for `z ∈ B`, and we only
ever evaluate/claim things on `B`). Fix `N`; on `B_N` write the tail
`T_N := fun z => ∑' k, (F (N + k + 1) z − F (N + k) z)`:
- each summand is holomorphic on `B_N`: `wirtingerDbar (F (n+1) − F n) = g − g = 0` on the open
  `B_N` (both `n, n+1 ≥ N`… (ii) gives it on `B̄_{n+1} ⊇ B_N`), CR bridge ⇒
  `DifferentiableOn ℂ _ B_N`;
- `‖F (N+k+1) − F (N+k)‖ ≤ (1/2)^(N+k+1)` on `B_N ⊆ B̄_{N+k}`; `tendstoUniformlyOn_tsum` with
  `u k := (1/2)^(N+k+1)` (geometric, summable) ⇒ partial sums of `T_N` converge uniformly on
  `B_N`;
- `TendstoUniformlyOn.tendstoLocallyUniformlyOn` + `TendstoLocallyUniformlyOn.differentiableOn`
  ⇒ `DifferentiableOn ℂ T_N B_N`;
- telescoping: on `B_N`, `u = F N + T_N` pointwise (partial sums of the tail are
  `F (N+m) − F N`; the limit of `F (N+m) z` is `u z` by definition of `limUnder` +
  uniqueness of limits).

**Step 5 (conclusion on each `B_N`, then on `B`).** On the open `B_N`:
`ContDiffOn ℝ ∞ u B_N` — `F N` is smooth, `T_N` is `DifferentiableOn ℂ` on an open set hence
`AnalyticOnNhd` (`DifferentiableOn.analyticOnNhd`) hence `ContDiffOn ℝ ∞` (restrict scalars:
`AnalyticAt.restrictScalars` + `AnalyticAt.contDiffAt`, the CC7 pattern); and for `z ∈ B_N`,
`wirtingerDbar u z = wirtingerDbar (F N) z + wirtingerDbar T_N z = g z + 0`
(`wirtingerDbar_congr_nhds` with `u =ᶠ F N + T_N` near `z` — `B_N` open; (ii) with
`B_N ⊆ B̄_{N+1}`; holomorphy of `T_N`). Since `ContDiffOn`/the ∂̄-equation are local and
`B = ⋃ B_N` with `B_N` open increasing, `ContDiffOn ℝ ∞ u B` and `∀ z ∈ B, wirtingerDbar u z
= g z`. ∎

Watchpoints (from a dry-run of the Lean shapes): (a) `ℝ≥0` coercion of radii in
`hasFPowerSeriesOnBall` — take `⟨ρ (n+1), le_of_lt …⟩ : ℝ≥0` and use `ENNReal.coe_lt_coe` for
`r' < r`; (b) the `tendstoUniformlyOn` statement is in the shifted variable `y ∈ ball 0 r'` —
transport by `fun w => w − c` (image/preimage of balls under subtraction, `sub_mem_ball_iff`…);
(c) the recursion must RETURN the chosen partial-sum degree inside the step (use
`Exists.choose` on the uniform-convergence eventuality); (d) `limUnder` needs `⊥`-junk care:
guard every use with `z ∈ B_N` and the Cauchy convergence (`cauchySeq_tendsto_of_complete`).

---

## 7. Proof plans: the remaining items

### 7.1 Finite smooth PoU on an open planar set (PlanarPoU.lean)

1. **Shrinking.** Work in the subtype `V` (`TopologicalSpace.Opens`-free: plain `Set.Elem V`):
   metrizable ⇒ `NormalSpace V` (instances: `Subtype.metricSpace` +
   `TopologicalSpace.MetrizableSpace.toNormalSpace`-chain). Apply
   `exists_subset_iUnion_closure_subset` with `s := univ` (closed), `u i := Subtype.val ⁻¹' W i`
   (open, point-finite: finitely many). Get subtype-opens `v i`, `closure (v i) ⊆ u i`,
   covering. Push forward: `W' i := Subtype.val '' v i` — open in ℂ (`IsOpen.isOpenMap_
   subtype_val` for open `V`), `W' i ⊆ W i`, `V ⊆ ⋃ W' i`, and the KEY relative-closure fact
   `V ∩ closure (W' i) ⊆ W i` (subtype closure = preimage of closure:
   `IsEmbedding.subtypeVal.closure_eq_preimage_closure_image`).
2. **Bumps.** `IsOpen.exists_smooth_support_eq` on each `W' i`: `ρ i : ℂ → ℝ` smooth,
   `support (ρ i) = W' i`, `0 ≤ ρ i ≤ 1`. `S := ∑ i, ρ i` is smooth; `S > 0` on `V` (cover).
3. **Normalize.** `ψ i := fun z => ρ i z / S z`… defined globally (junk where `S = 0`);
   `ContDiffOn ℝ ∞ (ψ i) V` (`ContDiffOn.div` with `S ≠ 0` on V — actually `ContDiffAt.div`
   pointwise on the open V), `∑ i, ψ i = 1` on `V` (`Finset.sum_div`), `support (ψ i) ⊆
   support (ρ i) = W' i ⊆ W i` ✓, and the eventual-vanishing clause: `z ∈ V ∖ W i` ⇒
   `z ∉ closure (W' i)` (else `z ∈ V ∩ closure W' i ⊆ W i`) ⇒ `ψ i = 0` on the neighborhood
   `(closure (W' i))ᶜ` ✓.
4. **Extension helper** `contDiffOn_indicator_smul_of_eventually_zero`: at `z ∈ U ∩ W` the
   indicator agrees with `ψ • f` on the open `U ∩ W` (`ContDiffAt.congr_of_eventuallyEq`);
   at `z ∈ U ∖ W` the function is eventually `0` (on the `hvan`-neighborhood, `ψ • f` and the
   off-`W` value are both 0); `U ⊆ (U ∩ W) ∪ (U ∖ W)` and `ContDiffWithinAt` is local. ∎

### 7.2 Cocycle splittings (PlanarCousin.lean)

Preliminaries from `hcoc`: `f i i = 0` on `W i` (take `j = k = i`), `f j i = −f i j` on
`W i ∩ W j` (take `k = i`).
**Smooth splitting**: PoU `ψ` from §7.1 for the cover; define
`h i := ∑ k, (W k).indicator (fun z => ψ k z • f k i z)`. Each summand is
`ContDiffOn ℝ ∞ _ (W i)` by the extension helper (`U := W i`, `W := W k`,
`f := f k i` smooth on `W k ∩ W i`, ℝ-smul of a ℂ-valued function; the ℂ-valued product
`ψ k z • f k i z` with `ψ k` ℝ-valued — `ContDiffOn.smul`). On `z ∈ W i ∩ W j`:
`h j z − h i z = ∑ k, indicator-terms (ψ k z • (f k j z − f k i z))`; for `z ∈ W k` the cocycle
(all three memberships available) gives `f k j − f k i = f i j` — wait, orientation:
`f k j = f k i + f i j` (hcoc at `(k, i, j)`), so the difference is `ψ k z • f i j z`; for
`z ∉ W k` both indicator terms vanish AND `ψ k z = 0` (support ⊆ W k), so the term equals
`ψ k z • f i j z` in every case. Summing: `(∑ k, ψ k z) • f i j z = f i j z` ✓ (`z ∈ V`).
**Holomorphic splitting on the ball**: `V := ball c R`. With `h` as above, the local forms
`wirtingerDbar (h i)` agree on overlaps: `h j − h i = f i j` is holomorphic there, so
`wirtingerDbar (h j) = wirtingerDbar (h i)` on `W i ∩ W j` (`wirtingerDbar_sub` +
`wirtingerDbar_eq_zero_of_differentiableAt`). Glue: `H z := if h : ∃ i, z ∈ W i then
wirtingerDbar (h h.choose) z else 0`; on `W i ∩ (choice = j)` equality holds by the overlap
relation, so `H` is locally `wirtingerDbar (h i)`, hence `ContDiffOn ℝ ∞ H (ball c R)`
(`contDiffOn_wirtingerDbar`, ∞ − 1 = ∞). Solve `∂̄u₀ = H` on the ball (13.2). Set
`u i := h i − u₀`: `wirtingerDbar (u i) = 0` on `W i`, CR bridge ⇒ `DifferentiableOn ℂ`;
differences `u j − u i = h j − h i = f i j` unchanged. ∎

### 7.3 `Form01.ofCoeffs` and `dbar` compatibility (Form01.lean, Operator.lean)

- `ofCoeffs` well-definedness/smoothness: at `z₀ ∈ (chartAt x).target` with `p₀ := symm z₀`
  and data chart `i₀ := idx p₀`: claim the defining formula with `idx p` equals, for `z` near
  `z₀`, the formula with the FIXED `i₀`. Both points lie in `(D.chart i₀).source ∩
  (D.chart (idx p)).source`; data-`compat` + `deriv_trans_comp` (three charts:
  `D.chart (idx p)`, `D.chart i₀`, `chartAt x`; all in maximal atlas — `chartAt` members via
  `chart_mem_maximalAtlas`) rewrite one into the other. This is a `conj`-decorated transcription
  of Forms's `coeffInFun_toSection` (`OfCoeffs.lean:72–99`); the `conj` distributes over the
  product in `deriv_trans_comp` since `starRingEnd` is multiplicative. Smoothness on the target:
  locally the fixed-`i₀` formula is (smooth ∘ holomorphic-transition) × (conj ∘ analytic deriv):
  `analyticAt_trans` gives `AnalyticAt` of `τ` and (via `AnalyticAt.deriv`… available as
  `AnalyticAt ℂ (deriv τ)` from `analyticAt_trans.deriv` — mathlib `AnalyticAt.deriv` exists;
  else `(analyticOnNhd_trans …).deriv` on the open overlap) ℝ-smoothness through
  `AnalyticAt.restrictScalars` + `contDiffAt`; `Complex.conjCLE` is ℝ-smooth. `compat` of the
  assembled structure: same computation with `chartAt y` in place of the data chart.
- `dbar` well-definedness (the `compat` field for `coeffAt x := indicator target
  (wirtingerDbar (f ∘ (chartAt x).symm))`): for `z ∈ chartAt y '' (source_x ∩ source_y)`,
  `f ∘ (chartAt y).symm = (f ∘ (chartAt x).symm) ∘ τ` near `z` with
  `τ := chartAt x ∘ (chartAt y).symm` (holomorphic at `z` by `analyticAt_trans`), so
  `wirtingerDbar_comp_differentiableAt` gives EXACTLY the `compat` equation. Smoothness of the
  chart representative: `contMDiffAt_real_iff_contDiffAt` (CC7).
- `isDbarAt` chart-invariance / `isDbarOn_iff_eqOn_coeff`: same chain rule, evaluated at
  centers; for the `⇐` direction at `x ∈ s` relate `chartAt x` to `chartAt x₀` via `compat`
  and cancel the nonzero factor `conj (deriv τ) ≠ 0` (transition derivative nonvanishing:
  `τ` is a local biholomorphism — from `deriv_trans_comp` with the inverse transition giving
  `deriv τ · deriv τ⁻¹ = 1`; Forms proved the analogous nonvanishing for `coeffIn_trans` —
  reuse pattern).
- `exists_dbar_solution_chart_ball`: `e := chartAt ℂ x₀`, `B := ball (e x₀) r = e '' V`.
  Planar datum `g := ω.coeffAt x₀` is smooth on `e.target ⊇ B`. 13.2 on `B` gives planar `u₀`.
  `u := u₀ ∘ e` (junk off source). `ContMDiffOn 𝓘(ℝ,ℂ) ∞ u V`: chart criterion
  (`contMDiffAt_real_iff_contDiffAt`, representative `u₀ ∘ e ∘ (chartAt z).symm` — reduce to
  the `x₀` chart by transition smoothness). `IsDbarOn u ω V`: at `x ∈ V`, apply the chain rule
  to `u ∘ (chartAt x).symm = u₀ ∘ τ` and `ω.compat` — both sides transform by the same
  `conj (deriv τ)` factor, and the planar equation `wirtingerDbar u₀ = g` on `B` closes it.

### 7.4 Disk acyclicity (DiskAcyclic.lean)

Notation: `hV : IsChartDisk V` unpacked to `x₀, r, e := chartAt ℂ x₀, B := ball (e x₀) r`,
`e '' V = B`, `V ⊆ e.source`; `𝒱 : FinCover V`, opens `Uᵢ := 𝒱.U i ≤ V`.

**(a) `D = 0`.** By cech's `subsingleton_h1Cover_iff` reduce to `Z1 0 𝒱 ≤ B1 0 𝒱`. Take
`f ∈ Z1 0 𝒱`; components `f (i,j) ∈ LinSysOn 0 ↑(Uᵢ ⊓ Uⱼ)` (germs, `ord ≥ 0`).
1. Representatives: `Fᵢⱼ := holoRepr (f (i,j)) : X → ℂ`, `ContMDiffOn 𝓘(ℂ) ω` on the open
   `↑(Uᵢ ⊓ Uⱼ)` (`holoRepr_contMDiffOn`, ord ≥ 0).
2. Planar transport: `Wᵢ := e '' ↑Uᵢ` (open: image of an open subset of `e.source`), cover `B`
   (from `𝒱.covers` + `e '' V = B`), `W i ∩ W j = e '' ↑(Uᵢ ⊓ Uⱼ)` (injectivity on source).
   `φᵢⱼ := Fᵢⱼ ∘ e.symm : ℂ → ℂ` is `DifferentiableOn ℂ` on `Wᵢ ∩ Wⱼ`
   (`contMDiffOn_iff_analyticOnNhd_of_subset_source` forward, `.differentiableOn`).
3. Pointwise cocycle: `d1 f = 0` gives, per cech's componentwise `d1_apply`, the germ identity
   `res f (j,k) − res f (i,k) + res f (i,j) = 0` on each triple meet; apply `evalAt` rigidity
   (`evalAt_restrict`, `evalAt_add`, `ord`-nonneg side conditions all `⊤`-safe) to get the
   POINTWISE identity `Fⱼₖ − Fᵢₖ + Fᵢⱼ = 0` on `↑(Uᵢ ⊓ Uⱼ ⊓ Uₖ)`, i.e. planar `hcoc` after
   `∘ e.symm` (orientation matches §4.5).
4. `exists_holo_splitting_ball` ⇒ planar `uᵢ` with `φᵢⱼ = uⱼ − uᵢ` on `Wᵢ ∩ Wⱼ`.
5. Pull back: `vᵢ := uᵢ ∘ e`, `ContMDiffOn 𝓘(ℂ) ω vᵢ ↑Uᵢ` (Bridges iff, backward),
   `hᵢ := MeroGermOn.mk vᵢ (meromorphicOnX_of_contMDiffOn_omega …) ∈ LinSysOn 0 ↑Uᵢ`
   (`mk_mem_linSysOn_zero`: `ord_mk` + `AnalyticAt ⇒ 0 ≤ meromorphicOrderAt` — if the planar
   atom is missing in mero's exports, local Compat via `meromorphicOrderAt_nonneg_iff`…
   one-liner from `AnalyticAt.meromorphicOrderAt_nonneg`-shaped lemmas in
   `Analysis/Meromorphic/Order.lean`; checked family exists).
6. `d0 h = f`: componentwise germ equality in `MeroGermOn X ↑(Uᵢ ⊓ Uⱼ)`:
   `restrict hⱼ − restrict hᵢ = mk (vⱼ − vᵢ) = mk (holoRepr (f (i,j))) = f (i,j)` — first
   equality `restrict_mk` + `mk_sub`; second `mk_eq_mk` from POINTWISE equality on the whole
   open set (membership `↑(Uᵢ ⊓ Uⱼ) ∈ codiscreteWithin ↑(Uᵢ ⊓ Uⱼ)`, trivial); third
   `mk_holoRepr`. Hence `f ∈ B1 0 𝒱`. ∎ (No `exists_glue`, no compactness.)

**(b) The twist (`D` arbitrary, `[T2Space X] [CompactSpace X]`).**
`S := (D.toFun.support ∩ ↑V)` is finite (CC2 `finiteSupport` on compact `X`; intersect).
`q : ℂ → ℂ := fun w => ∏ a ∈ Finset.image e S', (w − a) ^ (D (e.symm a))` (`S'` the Finset;
`zpow`; `e` injective on `V` keeps exponents unambiguous — index the product by `p ∈ S'`
directly and use `(w − e p) ^ (D p)` to dodge `e.symm` entirely:
`q w := ∏ p ∈ S', (w − e p) ^ (D p)`).
- `t := MeroGermOn.mk (q ∘ e) hq : MeroGermOn X ↑V` — `MeromorphicOnX (q∘e) V` from planar
  meromorphy of `q` (finite product of `zpow`s of `analyticAt id − const`) through the chart
  (mero's chart-transport lemma for `MeromorphicAtX`, present per `Predicates.lean` toolkit).
- `ord_twistGerm : ∀ x ∈ V, t.ord x = (D x : WithTop ℤ)`: `ord_mk` reduces to planar
  `meromorphicOrderAt q (e x)`; finite-product induction with `meromorphicOrderAt_mul`, atoms
  `meromorphicOrderAt_zpow_id_sub_const` (`= D p` at `e p`, `= 0` at other points since
  `(· − e p') ^ n` is analytic nonvanishing there — `meromorphicOrderAt_eq_zero_iff`-shaped);
  injectivity of `e` on `V` separates the atoms.
- Inverse germ: `t' := mk ((q ∘ e)⁻¹) (…MeromorphicAtX.inv)`, `t * t' = 1` via `mk_mul` +
  `mk_eq_mk` (equality off the finite zero/pole set — codiscrete).
- Twisted maps: for `Wopen ≤ V` define `μ_W : LinSysOn D ↑W →ₗ[ℂ] LinSysOn 0 ↑W`,
  `φ ↦ ⟨restrict (le) t * ↑φ, ord bound⟩` (`ord_mul` + `ord_restrict`: `ord ≥ D + (−D) = 0`;
  `WithTop ℤ` arithmetic — `D x` finite makes `add_le_add` safe). ℂ-linear (`mul_add`,
  `Algebra.mul_smul_comm`). Componentwise `μC0 : C0 D 𝒱 →ₗ C0 0 𝒱`, `μC1`, `μC2`.
- Commutation `μC1 ∘ d0 = d0 ∘ μC0` and `μC2 ∘ d1 = d1 ∘ μC1`: componentwise; `restrictL`
  commutes with multiplication by restrictions of the FIXED `t` (`restrict` is an `AlgHom`:
  `map_mul` + `restrict_restrict` coherence). So `μC1` maps `Z1 D → Z1 0` and reflects `B1`:
  if `μC1 f = d0 g₀` then `f = d0 (μ'C0 g₀)` where `μ'` is the `t'`-twist `LinSysOn 0 → LinSysOn D`
  (same construction; `μ' ∘ μ = id` via `t' * t = 1`, `one_mul`, and `Subtype.ext`).
- Assembly: `f ∈ Z1 D 𝒱` ⇒ `μC1 f ∈ Z1 0 𝒱` ⇒ (part (a)) `∈ B1 0 𝒱` ⇒ `f ∈ B1 D 𝒱`;
  `subsingleton_h1Cover_iff` closes `subsingleton_h1Cover_of_isChartDisk`. ∎

---

## 8. Requests to other units (filed in `docs/requests/`)

1. **meromorphic-and-divisors** (`docs/requests/meromorphic-and-divisors.md`):
   (a) `MeromorphicOnX` from `ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω` on an open set (analytic ⇒ meromorphic,
   chart-transported) and (b) `0 ≤ ord (mk u) x` for such `u` — both provable in our `Compat`
   section from their exported `ord_mk`/chart lemmas + mathlib `Analysis/Meromorphic/Order.lean`
   if not absorbed. (c) nice-to-have: `mem_linSysOn_iff` unfolding lemma (if the submodule is
   defined via carrier, `Iff.rfl`).
2. **cech-cohomology**: none beyond the published design (§4.1–4.2 names used as frozen). We
   OWE them `subsingleton_h1Cover_of_isChartDisk`; recorded in their Colimit.lean docstring.
3. **surfaces-and-charts / holomorphic-forms**: none (RealSmooth, Bridges, Analyticity suffice
   as built).

## 9. Risks & fallbacks (ranked)

1. **R1 (HIGH): the ∂̄-computation chain (§5).** Spike de-risked the four sharpest corners
   (convolution stack at `𝕜 = ℝ, G = ℂ`; kernel local integrability via `lintegral` polar;
   CR bridge; polar `integral_comp` + `setIntegral_prod` + swap shapes) — all compiled (§10).
   Residual risk is bookkeeping volume (indicator/interval bridges in steps 6–7). Fallbacks:
   (i) replace the convolution derivative package by manual
   `hasFDerivAt_integral_of_dominated_of_fderiv_le`; (ii) if the swap in step 7 fights, prove
   the `Ioc`-boxed version `T' := Ioc 0 R' ×ˢ Ioo (−π) π` throughout (finite measure box, both
   `setIntegral_prod` orders available by `integral_integral_swap` on honest `Integrable`
   functions without indicators, since the box has finite measure and integrands are bounded).
2. **R2 (MED-HIGH): 13.2 recursion + telescoping (§6).** No cheap mathematical fallback exists
   (consumers need the FULL open disk: disk acyclicity is quantified over exactly the chart
   disk, and Leray needs the members themselves acyclic) — budget the largest time share here.
   Mitigations: every atom is verified present (power series on ball, uniform partial sums,
   M-test, uniform-limit holomorphy); the recursion is packaged as a Σ-typed `Nat.rec` with the
   three invariants; watchpoints (a)–(d) of §6 pre-resolved. If the `ℝ≥0`/shifted-ball friction
   in the Taylor step explodes, fall back to Cauchy-estimate-based truncation: bound the tail of
   the Taylor series directly via `norm_cauchyPowerSeries_le`-style estimates (same file) —
   coarser but sufficient for (iii).
3. **R3 (MED): DiskAcyclic integration risk** — depends on two IN-FLIGHT units (mero's
   `LinSysOn` file, cech's `Covers/Cochains`). Mitigations: the planar Cousin atom (§7.2) is
   project-independent and lands early; the germ transport uses only mero names already BUILT
   (`holoRepr` suite verified compiled at `OrderEval.lean:225–321`); the twist uses only
   `restrict`-AlgHom + `ord_mul` (built). Fallbacks: (i) ship `subsingleton_h1Cover_zero…`
   (`D = 0`) first — dolbeault's Leray for `𝒪` unblocks the comparison while the twist lands;
   (ii) if cech's shapes shift, only `DiskAcyclic.lean` is touched (isolation by design).
4. **R4 (LOW-MED): Form01/Operator conj-transition bookkeeping.** Forms blazed the identical
   trail for `(1,0)` (`coeffInFun_toSection`, `coeffIn_trans`); ours is a `conj`-decorated
   transcription; `starRingEnd` is a ring hom so all product manipulations survive. Watch the
   junk-normalization interplay with `smul` (indicator outside targets).
5. **R5 (LOW): planar PoU subtype-topology friction** (§7.1 closure transport). Fallback:
   hand-rolled shrinking for FINITE covers by induction on `n` (shrink one member at a time
   using normality of ℂ on the closed set `V ∖ ⋃_{k≠i} W k ⊆ W i`… relative-closed sets), all
   inside ℂ — ~60 extra lines, no subtypes.

## 10. Spike record (RESULTS — run and honest)

`scratch_dbar.lean` (project root, 80 lines incl. comments), run gated
(`while [ "$(pgrep -cx lean)" -ge 3 ]; do sleep 30; done; lake env lean scratch_dbar.lean`):
**SUCCESS, exit 0, 7.1 s wall, zero sorries**, after one round of mechanical fixes.
Verified by compilation (keep `scratch_dbar.lean` as the builder's reference):
1. **Convolution stack at `ℂ`/`ℝ`**: `k ⋆[ContinuousLinearMap.mul ℝ ℂ] g` elaborates with
   default `volume`; `HasCompactSupport.contDiff_convolution_right` (𝕜 := ℝ),
   `HasCompactSupport.hasFDerivAt_convolution_right`, and `convolution_precompR_apply`
   (+ `simp [convolution_def]` to the display integral) all fired FIRST TRY — no
   `SFinite`/`IsAddLeftInvariant` instance surprises.
   ⚠ Typing detail: the lemma's `n : ℕ∞`, while the `ContDiff` scope's `∞` is `ℕ∞ω`-typed;
   write hypotheses/conclusions as `ContDiff ℝ (⊤ : ℕ∞)` at the application site (coercion to
   `ℕ∞ω` is automatic and equals `∞`); a bare `(∞ : ℕ∞)` is ambiguous if `ENNReal` scope is
   open — do NOT `open scoped ENNReal` in these files.
2. **Kernel measurability + local integrability skeleton**: `Measurable cauchyKernel` closes
   by `(measurable_id.const_mul _).inv` — the `MeasurableInv ℂ` instance resolves via the
   `ContinuousInv₀` blanket instance (`MeasureTheory/Constructions/BorelSpace/Basic.lean:588`);
   no `ContinuousOn`/null-set detour needed. `Complex.lintegral_comp_polarCoord_symm` applied
   to `(ball 0 ρ).indicator fun w => ‖k w‖ₑ` type-checks as stated in §5 step 1.
3. **CR bridge compiled end-to-end, sorry-free**: from `HasFDerivAt f L' z` with
   `L' I = I * L' 1`, conclusion `DifferentiableAt ℂ f z` via candidate
   `L' 1 • ContinuousLinearMap.id ℂ ℂ`, extensionality on `v = v.re • 1 + v.im • I`
   (`Complex.real_smul` + `Complex.re_add_im`), simp set
   `[ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smul_apply,
   ContinuousLinearMap.id_apply, hCR, smul_eq_mul, Complex.real_smul]` + `ring`, and
   `hasFDerivAt_of_restrictScalars`. ⚠ That lemma's section makes `𝕜` an EXPLICIT leading
   argument — apply with named args `(h := …) (H := …)` (positional application misparses).
   (`ContinuousLinearMap.restrictScalars_apply` does NOT exist; `coe_restrictScalars'` does.)
4. **Polar + product shapes**: `Complex.integral_comp_polarCoord_symm` applies; NOTE its
   integration set is the REAL `polarCoord.target` (not `Complex.polarCoord.target`), and
   `polarCoord.target = Ioi 0 ×ˢ Ioo (-π) π` is `rfl`. `volume` on `ℝ × ℝ` is
   DEFINITIONALLY `(volume : Measure ℝ).prod volume` (`rfl`; `MeasureTheory.volume_eq_prod`
   also available), after which `setIntegral_prod` fires on the box; `integral_integral_swap`
   signature confirmed for the step-7 swap.
First-round failures (for the record, all fixed as above): `∞` overload ambiguity with
`ENNReal` scope; nonexistent `restrictScalars_apply`; positional `hasFDerivAt_of_restrictScalars`;
`Complex.polarCoord_target` vs real `polarCoord.target` mismatch; `volume_eq_prod` needs
qualification or the `rfl` route. (If any late deviation is found during the build, the
discovering builder updates this section.)

## 11. Per-consumer consumption map

- **dolbeault-comparison** (direct dependent): `Form01` + module instances + `ext` +
  `Form01.ofCoeffs`/`coeffAt_ofCoeffs` (assemble `H^{0,1}`-representatives from local data);
  `SmoothC`, `dbar`, `dbar_eq_iff` (define `H^{0,1} := Form01 X ⧸ LinearMap.range dbar`);
  `IsDbarOn` + `exists_dbar_solution_chart_ball` (local realization of classes);
  `contMDiffOn_omega_sub_of_isDbarOn` (solution differences → Čech cocycles, via mero `mk`);
  `contMDiffOn_omega_of_isDbarOn_zero` (holomorphic representatives);
  `subsingleton_h1Cover_of_isChartDisk` (input to Leray/Forster 12.8, whose statement cech
  recorded as `toH1_surjective_of_isGood`); smooth PoU on `X`: consume
  `RS.exists_smoothPartitionOfUnity` (Surface CC7) directly — availability verified here §1.5.
- **cech-cohomology**: receives the owed `subsingleton_h1Cover_of_isChartDisk` (their §7);
  no other coupling.
- **finiteness-and-chi**: nothing direct; everything flows through dolbeault-comparison
  (Leray) and cech (`H1`, six-term fragment). Montel input comes from `Jacobian/Forms/Montel`.
- **planar-stokes-atoms** (builds on us): reuse `Wirtinger.lean`
  (`fderiv_apply_eq_wirtinger`, CR bridge, chain rule) and possibly
  `PlanarPoU.lean`; they must NOT re-prove these. We import NOTHING from them (DAG).
- **residue-calculus / abel-weak-solutions / monodromy**: may reuse `Wirtinger.lean` and
  `Path/Planar.lean`-style atoms; no promises made beyond the planar files being
  manifold-import-free (D10).

## 12. Conventions / CC conformance

- CC7 consumed as designed: the ℝ-charts ARE the ℂ-charts (`extChartAt_real_eq` is `rfl`);
  all chart representatives are taken through `chartAt ℂ x` so the CC7 `rfl`-facts apply;
  no new `IsManifold` instances are declared (the blueprint's diamond warning is honored by
  D5/D6: no bundles, no competing module instances on mathlib types).
- Frozen choices untouched: genus/L(D)/multiplicity not referenced; divisors via CC2's
  `Divisor X` and `finiteSupport` only.
- `sorry`-free bar per CONVENTIONS; unit root `Jacobian/Dbar.lean` registers in
  `Jacobian.lean`; ≤1 lake job; `scripts/check.sh Jacobian/Dbar` gates DONE.
- Naming: `RS` namespace; planar lemmas about mathlib-typed objects follow mathlib naming
  (`wirtingerDbar_comp_differentiableAt`, `locallyIntegrable_cauchyKernel`); no `Jacobian`
  root-level names (those belong to the final assembly).
- Deviation to flag for orchestrator: the blueprint sentence "define ∂̄ intrinsically as
  `proj^{0,1} ∘ d`" is implemented CHART-LOCALLY (D5/D6) rather than through a tangent-bundle
  projection — the two agree by the (0,1) chain rule, and the bundle route is exactly the
  restrictScalars trap the same blueprint entry warns about. Statement shapes consumed
  downstream are unaffected.
