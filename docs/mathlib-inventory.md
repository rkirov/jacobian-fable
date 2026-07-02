# Mathlib inventory for the Jacobian project

Pinned mathlib commit: `548398201a64f3a5127d90d83945278cfe38cac4` (2026-05-15), source at
`.lake/packages/mathlib/Mathlib/`. All file paths below are relative to `Mathlib/`.
All Lean names and signatures were verified against this commit's source (not memory).
Signatures may elide long typeclass argument lists with `...`; the mathematical content is exact.

Notation reminders used throughout: `open scoped Manifold ContDiff` gives
`𝓘(𝕜, E) = modelWithCornersSelf 𝕜 E`, `𝓘(𝕜) = modelWithCornersSelf 𝕜 𝕜`,
`ℕ∞ω = WithTop ℕ∞`, `ω = (⊤ : WithTop ℕ∞)` (analytic), `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)` (C^∞).

---

## 1. Complex manifolds

### Layout of `Geometry/Manifold/`

Top-level files: `Bordism`, `BumpFunction`, `ChartedSpace`, `Complex`, `ConformalGroupoid`,
`ContMDiffMFDeriv`, `ContMDiffMap`, `DerivationBundle`, `Diffeomorph`, `GroupLieAlgebra`,
`HasGroupoid`, `Immersion`, `LocalDiffeomorph`, `LocalInvariantProperties`,
`LocalSourceTargetProperty`, `Metrizable`, `Notation`, `PartitionOfUnity`, `PoincareConjecture`,
`SmoothApprox`, `SmoothEmbedding`, `StructureGroupoid`, `WhitneyEmbedding`.
Subdirectories: `Algebra/` (LieGroup, Monoid, SMul, Structures, SmoothFunctions,
LeftInvariantDerivation), `ContMDiff/` (Defs, Basic, Atlas, Constructions, NormedSpace),
`Instances/` (Icc, Quotient, Real, Sphere, UnitsOfNormedAlgebra), `IntegralCurve/`,
`IsManifold/` (Basic, ExtChartAt, InteriorBoundary), `MFDeriv/` (Defs, Basic, Atlas, FDeriv,
NormedSpace, SpecificFunctions, Tangent, UniqueDifferential), `Riemannian/` (Riemannian *metric*
geometry — unrelated to Riemann surfaces), `Sheaf/`, `VectorBundle/`, `VectorField/`.

### Core typeclasses

`Geometry/Manifold/IsManifold/Basic.lean:785`:

```lean
class IsManifold {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] : Prop
    extends HasGroupoid M (contDiffGroupoid n I)
```

Smoothness index `n : ℕ∞ω = WithTop ℕ∞` (notation in
`Analysis/Calculus/ContDiff/FTaylorSeries.lean:115-119`): `n = ∞` smooth, `n = ω` analytic.
**`IsManifold 𝓘(ℂ) ω M` is exactly "complex manifold with holomorphic atlas"** — this is the
correct definition of a Riemann surface for us (with charts in `ℂ`). Very mature, central API.

Key helpers (same file): `IsManifold.of_le {m n : ℕ∞ω} (hmn : m ≤ n) [IsManifold I n M] :
IsManifold I m M` (`:827`) plus instances automatically deriving lower smoothness from `ω`
(`:852-871`); `prod` instance (`:936`);
`Topology.IsOpenEmbedding.isManifold_singleton {f : M → H} (h : IsOpenEmbedding f) :
@IsManifold 𝕜 _ E _ _ H _ I n M _ h.singletonChartedSpace` (`:1004`) and
`OpenPartialHomeomorph.isManifold_singleton` (`:996`) — **the** tool for putting a
complex-manifold structure on anything covered by an open embedding into `ℂ`.

`Geometry/Manifold/ChartedSpace.lean:139`:

```lean
class ChartedSpace (H : Type*) [TopologicalSpace H] (M : Type*) [TopologicalSpace M] where
  protected atlas : Set (OpenPartialHomeomorph M H)
  protected chartAt : M → OpenPartialHomeomorph M H
  protected mem_chart_source : ∀ x, x ∈ (chartAt x).source
  protected chart_mem_atlas : ∀ x, chartAt x ∈ atlas
```

with abbreviations `atlas H M`, `chartAt H x`. Note charts are `OpenPartialHomeomorph`.

### ContMDiff / MDifferentiable / mfderiv

- `Geometry/Manifold/ContMDiff/Defs.lean`: `ContMDiffWithinAt` (`:169`), `ContMDiffAt` (`:178`),
  `ContMDiffOn`, `ContMDiff`, all indexed by `n : ℕ∞ω`, so `ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f` means
  "holomorphic map of complex manifolds". `contMDiffAt_iff` (`:181`), `contMDiff_iff` (`:539`).
- `Geometry/Manifold/MFDeriv/Defs.lean`: `MDifferentiableWithinAt` (`:219`), `MDifferentiableAt`
  (`:248`), `MDifferentiable` (`:278`), `mfderivWithin` (`:322`),
  `mfderiv (f) (x) : TangentSpace I x →L[𝕜] TangentSpace I' (f x)` (`:334`). Large API in
  `MFDeriv/Basic.lean`.

### Analytic manifolds, Riemann surfaces — status

- There is **no** `AnalyticManifold.lean` / `ComplexManifold.lean`; analytic manifolds are just
  `IsManifold I ω M` via `contDiffGroupoid ω I`.
- **Nothing** on Riemann surfaces or 1-dimensional complex manifolds anywhere in mathlib
  (case-insensitive searches for `RiemannSurface`, "Riemann surface", `riemann_surface`; all
  "Riemann" hits are `RiemannZeta`, `Riemannian` metrics, `RiemannLebesgue`, Riemann/box
  integrals).
- The only worked example of an `IsManifold 𝓘(ℂ) ω` instance in mathlib is the upper half-plane:
  `Analysis/Complex/UpperHalfPlane/Manifold.lean` — `ChartedSpace ℂ ℍ :=
  isOpenEmbedding_coe.singletonChartedSpace` (`:38`), `IsManifold 𝓘(ℂ) ω ℍ` (`:41`), plus
  `contMDiffAt_iff` / `mdifferentiableAt_iff` reducing `MDifferentiableAt` on `ℍ` to
  `DifferentiableAt ℂ` on `ℂ`. This file is the template for building our surface instances.

Maturity: the abstract manifold machinery is excellent and actively maintained; the complex/
1-dimensional specialization is essentially absent.

## 2. Riemann sphere / projective line

Bottom line: **mathlib has no complex-manifold model of `ℙ¹`.**

- `RiemannSphere`: no hits anywhere.
- `OnePoint ℂ`: `Topology/Compactification/OnePoint/` (`Basic`, `Sphere`, `ProjectiveLine`)
  provides the one-point compactification as a topological space only. **No** `ChartedSpace`,
  `IsManifold`, or `ContMDiff` instance for any `OnePoint X` (greps for
  `ChartedSpace ℂ (OnePoint ℂ)`, manifold instances on `OnePoint`: nothing).
- `Topology/Compactification/OnePoint/Sphere.lean` — topological homeomorphisms only:
  - `onePointHyperplaneHomeoUnitSphere (hv : ‖v‖ = 1) : OnePoint (ℝ ∙ v)ᗮ ≃ₜ sphere (0 : E) 1`
    (`:25`)
  - `onePointEquivSphereOfFinrankEq (h : finrank ℝ V + 1 = Fintype.card ι) :
    OnePoint V ≃ₜ sphere (0 : EuclideanSpace ℝ ι) 1` (`:34`)

  These give `OnePoint ℂ ≃ₜ S²` cheaply (over ℝ), useful for the headline statement
  `genus X = 0 ↔ X ≃ₜ S²`.
- `Topology/Compactification/OnePoint/ProjectiveLine.lean`: only a set-theoretic
  `OnePoint.equivProjectivization : OnePoint K ≃ ℙ K (Fin 2 → K)` for a division ring `K`; the
  file's own TODO (`:20`) says even the `K = ℝ` homeomorphism is not done.
- `Projectivization` (`LinearAlgebra/Projectivization/`) is purely algebraic — **no topology, no
  manifold structure** at all.

### Sphere instances (real)

`Geometry/Manifold/Instances/Sphere.lean` is mature (models on real Euclidean space):

- `stereographic (hv : ‖v‖ = 1) : OpenPartialHomeomorph (sphere (0:E) 1) (ℝ ∙ v)ᗮ` (`:248`)
- `stereographic' (n : ℕ) [Fact (finrank ℝ E = n + 1)] (v : sphere (0:E) 1) :
  OpenPartialHomeomorph (sphere (0:E) 1) (EuclideanSpace ℝ (Fin n))` (`:336`), source `{v}ᶜ`,
  target `univ`
- `EuclideanSpace.instChartedSpaceSphere : ChartedSpace (EuclideanSpace ℝ (Fin n))
  (sphere (0:E) 1)` (`:352`)
- `EuclideanSpace.instIsManifoldSphere [Fact (finrank ℝ E = n + 1)] :
  IsManifold (𝓡 n) ω (sphere (0:E) 1)` (`:386`) — real-analytic
- `contMDiff_coe_sphere : ContMDiff (𝓡 n) 𝓘(ℝ, E) m ((↑) : sphere (0:E) 1 → E)` (`:420`),
  `ContMDiff.codRestrict_sphere` (`:440`), `range_mfderiv_coe_sphere` (`:484`),
  `mfderiv_coe_sphere_injective` (`:520`)
- `Circle` (unit circle in `ℂ`): `ChartedSpace (EuclideanSpace ℝ (Fin 1)) Circle` (`:552`),
  `IsManifold (𝓡 1) ω Circle` (`:555`), `LieGroup (𝓡 1) ω Circle` (`:559`) — the **real**
  structure only.

Nothing special for `EuclideanSpace ℝ (Fin 3)`; the sphere never gets a complex/`ℂP¹` structure.

Consequence for us: we must build `ℙ¹` (or `OnePoint ℂ`) as a complex manifold ourselves — two
charts via `Topology.IsOpenEmbedding.isManifold_singleton`-style tooling won't suffice directly
(that gives a single-chart structure); expect a hand-rolled two-chart `ChartedSpace ℂ (OnePoint ℂ)`
plus a `HasGroupoid` check that `z ↦ 1/z` is analytic.

---

## 3. Meromorphic function theory

### `Analysis/Meromorphic/` — full contents (8 files)

| File | Contents |
|---|---|
| `Basic.lean` | `MeromorphicAt`, `MeromorphicOn`, `Meromorphic`; closure under `+ - • * prod finprod sum deriv`; zpow-smul normal form (Loeffler, Kebekus). Core, mature. |
| `Order.lean` | `meromorphicOrderAt : (𝕜 → E) → 𝕜 → WithTop ℤ` and its characterizations; codiscreteness of {order = 0 or ⊤}. Mature. |
| `IsolatedZeros.lean` | Identity principles for meromorphic functions via codiscrete filters. Mature. |
| `Divisor.lean` | `MeromorphicOn.divisor` and its algebra. Mature. |
| `NormalForm.lean` | `MeromorphicNFAt`/`MeromorphicNFOn` normal-form predicates; `toMeromorphicNFOn` best representative. Mature (2025). |
| `TrailingCoefficient.lean` | `meromorphicTrailingCoeffAt : E` — leading Laurent coefficient. Newer, usable. |
| `FactorizedRational.lean` | `∏ᶠ u, (· - u) ^ d u` factorized rationals; `MeromorphicOn.extract_zeros_poles`. Newer, usable. |
| `Complex.lean` | Gamma is meromorphic (`Meromorphic.Gamma`). |

### Core definitions

`Analysis/Meromorphic/Basic.lean`:

```lean
@[fun_prop] def MeromorphicAt (f : 𝕜 → E) (x : 𝕜) :=
  ∃ (n : ℕ), AnalyticAt 𝕜 (fun z ↦ (z - x) ^ n • f z) x                        -- :36
def MeromorphicOn (f : 𝕜 → E) (U : Set 𝕜) : Prop := ∀ x ∈ U, MeromorphicAt f x -- :473
def Meromorphic (f : 𝕜 → E) := ∀ x, MeromorphicAt f x                          -- :655
lemma MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt : MeromorphicAt f x ↔
    ∃ (n : ℤ) (g : 𝕜 → E), AnalyticAt 𝕜 g x ∧ ∀ᶠ z in 𝓝[≠] x, f z = (z - x) ^ n • g z -- :359
```

### Order — the name is `meromorphicOrderAt` (NOT `MeromorphicAt.order`)

`Analysis/Meromorphic/Order.lean:47`:

```lean
noncomputable def meromorphicOrderAt (f : 𝕜 → E) (x : 𝕜) : WithTop ℤ
```

(junk value `0` when `¬ MeromorphicAt f x`). Key lemmas, naming convention `meromorphicOrderAt_*`:

- `meromorphicOrderAt_eq_top_iff : meromorphicOrderAt f x = ⊤ ↔ ∀ᶠ z in 𝓝[≠] x, f z = 0` (`:64`)
- `meromorphicOrderAt_eq_int_iff {n : ℤ} (hf : MeromorphicAt f x) :
  meromorphicOrderAt f x = n ↔ ∃ g, AnalyticAt 𝕜 g x ∧ g x ≠ 0 ∧
  ∀ᶠ z in 𝓝[≠] x, f z = (z - x) ^ n • g z` (`:94`) — **the local `z^n · unit` factorization.**
- `meromorphicOrderAt_ne_top_iff` (`:126`), `meromorphicOrderAt_ne_top_iff_eventually_ne_zero` (`:137`)
- pole/zero behavior: `tendsto_cobounded_iff_meromorphicOrderAt_neg`,
  `tendsto_ne_zero_of_meromorphicOrderAt_eq_zero`, `tendsto_zero_of_meromorphicOrderAt_pos` (`:149ff`)
- `MeromorphicOn.analyticAt_mem_codiscreteWithin (hf) :
  {x | AnalyticAt 𝕜 f x} ∈ codiscreteWithin U` (`:755`);
  `MeromorphicOn.codiscrete_setOf_meromorphicOrderAt_eq_zero_or_top` (`:766`).

### Analytic order — `analyticOrderAt` (NOT `AnalyticAt.order`)

`Analysis/Analytic/Order.lean`:

```lean
noncomputable def analyticOrderAt (f : 𝕜 → E) (z₀ : 𝕜) : ℕ∞          -- :48
noncomputable def analyticOrderNatAt (f) (z₀) : ℕ                     -- :62 (.toNat)
lemma AnalyticAt.analyticOrderAt_eq_natCast (hf : AnalyticAt 𝕜 f z₀) :
    analyticOrderAt f z₀ = n ↔ ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z                          -- :87
```

plus `analyticOrderAt_eq_top` (`:76`), `AnalyticAt.analyticOrderAt_ne_top` (`:114`),
`analyticOrderAt_eq_zero` (`:121`). This IS the `f(z) = z^k · unit` atom the blueprint's
`local-multiplicity` unit needs on the planar side.

### Isolated zeros / normal-form helpers

`Analysis/Analytic/IsolatedZeros.lean`:

- `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero (hf : AnalyticAt 𝕜 f z₀) :
  (∀ᶠ z in 𝓝 z₀, f z = 0) ∨ ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0` (`:125`)
- `AnalyticAt.frequently_zero_iff_eventually_zero` (`:136`), `frequently_eq_iff_eventually_eq` (`:141`)
- `AnalyticAt.unique_eventuallyEq_zpow_smul_nonzero` (`:149`) /
  `unique_eventuallyEq_pow_smul_nonzero` (`:173`) — uniqueness of the exponent
- `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff` (`:185`) — existence
  (the literal name `eventually_eq_pow_smul` does NOT exist)
- Identity theorems: `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero` (`:214`),
  `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` (`:238`),
  `AnalyticOnNhd.eq_of_frequently_eq` (`:261`)
- Codiscrete bridges: `AnalyticOnNhd.preimage_mem_codiscreteWithin` (`:346`),
  `AnalyticOnNhd.map_codiscreteWithin` (`:366`)

`AnalyticOnNhd` def at `Analysis/Analytic/Basic.lean:118`, `AnalyticOn` at `:123`.

### Normal-form predicates

`Analysis/Meromorphic/NormalForm.lean`:

```lean
def MeromorphicNFAt (f : 𝕜 → E) (x : 𝕜) :=                                    -- :47
  f =ᶠ[𝓝 x] 0 ∨ ∃ (n : ℤ) (g : 𝕜 → E), AnalyticAt 𝕜 g x ∧ g x ≠ 0 ∧
    f =ᶠ[𝓝 x] (· - x) ^ n • g
def MeromorphicNFOn (f : 𝕜 → E) (U : Set 𝕜) := ∀ ⦃z⦄, z ∈ U → MeromorphicNFAt f z -- :491
```

with `meromorphicNFAt_iff_analyticAt_or` (`:53`),
`MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt` (`:114`),
`MeromorphicNFOn.zero_set_eq_divisor_support` (`:536`), and the junk-value repair
`toMeromorphicNFOn` / `meromorphicNFOn_toMeromorphicNFOn`. This is exactly the "normal-form
repair" tool for the blueprint's meromorphic-and-divisors unit.

### Principal parts — ABSENT

No `principalPart` / "principal part" API anywhere in Analysis/. Closest:
`meromorphicTrailingCoeffAt` (`Analysis/Meromorphic/TrailingCoefficient.lean:36`, with
`MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt` `:116`) gives only the leading Laurent
coefficient. Mittag-Leffler principal-part distributions must be built by us.

### Value distribution (`Analysis/Complex/ValueDistribution/`, Kebekus et al. 2025-26)

Files: `LogCounting/Basic.lean` (`ValueDistribution.logCounting`, both as
`locallyFinsupp E ℤ →+ (ℝ → ℝ)` at `:96` and for meromorphic `f` at a value `a` at `:272`),
`LogCounting/Asymptotic.lean`, `Proximity/Basic.lean` (`proximity` via
`circleAverage (log⁺ ‖f ·‖) 0`), `CharacteristicFunction.lean`
(`characteristic := proximity f a + logCounting f a`, `:53`), `FirstMainTheorem.lean`
(`characteristic_sub_characteristic_inv` `:47`, `isBigO_characteristic_sub_characteristic_shift`
`:160` — FMT as O(1) statements), `Cartan.lean` (stub). Supporting:
`Analysis/Complex/JensenFormula.lean`, `MeasureTheory/Integral/CircleAverage.lean`.
Not directly needed for Riemann-Roch, but `logCounting`'s divisor-summation idioms and
`JensenFormula` are useful precedents.

## 4. Divisors

### `Function.locallyFinsuppWithin` — `Topology/LocallyFinsupp.lean` (Kebekus, 2025)

```lean
structure Function.locallyFinsuppWithin (U : Set X) (Y) [Zero Y] where   -- :48
  toFun : X → Y
  supportWithinDomain' : toFun.support ⊆ U
  supportLocallyFiniteWithinDomain' : ∀ z ∈ U, ∃ t ∈ 𝓝 z, Set.Finite (t ∩ toFun.support)
abbrev Function.locallyFinsupp (X) (Y) := locallyFinsuppWithin (Set.univ : Set X) Y  -- :61
```

`FunLike` instance (`:125`, so `D z` works). API:

- Full lattice-ordered abelian group: `AddCommGroup` (`:379`), `LE`/`LT` (`:383`/`:394`),
  `Lattice` (`:462`), `IsOrderedAddMonoid` (`:490`), pos/neg parts `D⁺`/`D⁻`
  (`posPart_apply`/`negPart_apply` `:479`/`:480`).
- `single x y` (`:153`) with `single_apply`.
- `restrict (D) (h : V ⊆ U) : locallyFinsuppWithin V Y` (`:566`);
  `restrictMonoidHom (h : V ⊆ U) : locallyFinsuppWithin U Y →+ locallyFinsuppWithin V Y` (`:607`).
- **Compactness**: `Function.locallyFinsuppWithin.finiteSupport [T2Space X] (D)
  (hU : IsCompact U) : Set.Finite D.support` (`:243`) — **support of a divisor on a compact
  space is finite**. Also `LocallyFiniteSupport.finite_inter_support_of_isCompact` (`:106`),
  `discreteSupport` (`:210`), `closedSupport` (`:229`), `eq_zero_codiscreteWithin` (`:197`).
- `sum_apply_smul_single_eq_self` (`:626`).
- ABSENT: no `map` (post-composition), no `toFinsupp`, and **no `degree`** — the degree
  functional `deg D = ∑ D z` does not exist and must be defined by us (via `finiteSupport` +
  `Finset.sum`).

### `MeromorphicOn.divisor` — `Analysis/Meromorphic/Divisor.lean:39`

```lean
noncomputable def MeromorphicOn.divisor (f : 𝕜 → E) (U : Set 𝕜) :
    Function.locallyFinsuppWithin U ℤ
-- z ↦ if MeromorphicOn f U ∧ z ∈ U then (meromorphicOrderAt f z).untop₀ else 0
```

Lemmas: `divisor_apply (hf : MeromorphicOn f U) (hz : z ∈ U) :
divisor f U z = (meromorphicOrderAt f z).untop₀` (`:68`), `AnalyticOnNhd.divisor_apply` (`:71`),
`AnalyticOnNhd.divisor_nonneg` (`:143`), exact multiplicativity `divisor_smul` (`:246`),
`divisor_mul` (`:276`), `divisor_prod` (`:295`), `divisor_inv` (`:326`), `divisor_pow`/
`divisor_zpow` (`:340-372`), `divisor_restrict` (`:379`), codiscrete congruence
`divisor_congr_codiscreteWithin` (`:118`), additivity bounds `min_divisor_le_divisor_add`
(`:194`) etc.

**Caveat: this is only for functions on `𝕜` (planar), not on manifolds.** Divisors on a surface
`X` have to be `Function.locallyFinsuppWithin (univ : Set X) ℤ` built from chart-local orders —
the container type is ready, the meromorphic-on-a-manifold layer is not.

### Zero/pole factorization on the plane

`Analysis/Meromorphic/FactorizedRational.lean`: `MeromorphicOn.extract_zeros_poles` (`:291`) —
given `(divisor f U).support.Finite`, writes `f =ᶠ[codiscreteWithin U]
(∏ᶠ u, (· - u) ^ (divisor f U u)) • g` with `g` analytic and zero-free;
`Function.FactorizedRational.divisor` (`:176`). Directly useful for planar residue calculus and
for `deg(div f) = 0` bookkeeping on charts.

## 5. Complex analysis atoms

Notable files in `Analysis/Complex/`: `AbsMax`, `Basic`, `BorelCaratheodory`, `CauchyIntegral`,
`Circle`, `Conformal`, `CoveringMap`, `Hadamard`, `Harmonic/`, `HasPrimitives`, `JensenFormula`,
`Liouville`, `LocallyUniformLimit`, `MeanValue`, `OpenMapping`, `PhragmenLindelof`, `Poisson`,
`Polynomial/` (FTA, GaussLucas), `RemovableSingularity`, `Schwarz`, `TaylorSeries`, `UnitDisc/`,
`UpperHalfPlane/`, `ValueDistribution/`.

### (a) Cauchy integral formula — `Analysis/Complex/CauchyIntegral.lean` (namespace `Complex`)

```lean
theorem Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    {R : ℝ} {c w : ℂ} {f : ℂ → E} {s : Set ℂ} (hs : s.Countable) (hw : w ∈ ball c R)
    (hc : ContinuousOn f (closedBall c R)) (hd : ∀ x ∈ ball c R \ s, DifferentiableAt ℂ f x) :
    (∮ z in C(c, R), (z - w)⁻¹ • f z) = (2 * π * I : ℂ) • f w

theorem Complex.circleIntegral_div_sub_of_differentiable_on_off_countable ... :
    (∮ z in C(c, R), f z / (z - w)) = 2 * π * I * f w
```

Also: Cauchy-Goursat on rectangles
`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`; clean-hypothesis
variants `DiffContOnCl.circleIntegral_sub_inv_smul`,
`DifferentiableOn.circleIntegral_sub_inv_smul`; holomorphic-implies-analytic
`Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable`,
`DifferentiableOn.hasFPowerSeriesOnBall (hd : DifferentiableOn ℂ f (closedBall c R)) (hR : 0 < R) :
HasFPowerSeriesOnBall f (cauchyPowerSeries f c R) c R`, then `DifferentiableOn.analyticAt`,
`.analyticOnNhd`. **Contour deformation on annuli** (our Laurent/residue seed):

```lean
theorem Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    {c : ℂ} {r R : ℝ} (h0 : 0 < r) (hle : r ≤ R) {f : ℂ → E} {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn f (closedBall c R \ ball c r))
    (hd : ∀ z ∈ (ball c R \ closedBall c r) \ s, DifferentiableAt ℂ f z) :
    (∮ z in C(c, R), f z) = ∮ z in C(c, r), f z
```

and `circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable`.
Mature, complete.

### (b) `circleIntegral` — `MeasureTheory/Integral/CircleIntegral.lean`

```lean
def circleIntegral (f : ℂ → E) (c : ℂ) (R : ℝ) : E :=
  ∫ θ : ℝ in 0..2 * π, deriv (circleMap c R) θ • f (circleMap c R θ)   -- notation ∮ z in C(c,R), f z
def CircleIntegrable (f : ℂ → E) (c : ℂ) (R : ℝ) : Prop
def circleMap (c : ℂ) (R : ℝ) (θ : ℝ) : ℂ := c + R * exp (θ * I)
```

Key: `circleIntegral.integral_sub_inv_of_mem_ball (hw : w ∈ ball c R) :
(∮ z in C(c, R), (z - w)⁻¹) = 2 * π * I`,
`circleIntegral.integral_sub_zpow_of_ne (hn : n ≠ -1) : (∮ z in C(c, R), (z - w) ^ n) = 0`,
`circleIntegral_congr_codiscreteWithin`,
`TendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn`. Mature.

### (c) Residues — ABSENT

No `Complex.residue`, no contour-integral residue anywhere (all "residue" hits are local-ring
residue fields, residue classes mod m, or zeta-function docstrings). We define `resAt` ourselves;
the ingredients (`circleIntegral`, annulus deformation, `meromorphicOrderAt` factorization) are
all present.

### (d) Laurent series (analytic) — ABSENT

Only algebraic objects: `RingTheory/LaurentSeries.lean` (`LaurentSeries R := HahnSeries ℤ R`),
`Algebra/Polynomial/Laurent.lean` (`LaurentPolynomial`), `FieldTheory/Laurent.lean` (algebraic
Laurent expansion of `RatFunc`). No `HasLaurentSeriesOn`, no analytic expansion on an annulus,
no principal parts.

### (e) Removable singularity — `Analysis/Complex/RemovableSingularity.lean` (namespace `Complex`)

```lean
theorem Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    (hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z) (hc : ContinuousAt f c) : AnalyticAt ℂ f c
theorem Complex.differentiableOn_update_limUnder_of_isLittleO (hc : s ∈ 𝓝 c)
    (hd : DifferentiableOn ℂ f (s \ {c}))
    (ho : (fun z => f z - f c) =o[𝓝[≠] c] fun z => (z - c)⁻¹) :
    DifferentiableOn ℂ (update f c (limUnder (𝓝[≠] c) f)) s
theorem Complex.differentiableOn_update_limUnder_of_bddAbove (hc : s ∈ 𝓝 c)
    (hd : DifferentiableOn ℂ f (s \ {c})) (hb : BddAbove (norm ∘ f '' (s \ {c}))) : ...
```

Mature; exactly the Riemann removable-singularity tool for canonical forms.

### (f) Identity theorem — `Analysis/Analytic/Uniqueness.lean` + `IsolatedZeros.lean`

```lean
theorem AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hf : AnalyticOnNhd 𝕜 f U)
    (hg : AnalyticOnNhd 𝕜 g U) (hU : IsPreconnected U) (h₀ : z₀ ∈ U) (hfg : f =ᶠ[𝓝 z₀] g) :
    EqOn f g U
theorem AnalyticOnNhd.eq_of_eventuallyEq [PreconnectedSpace E] ... : f = g
```

plus the `frequently` versions listed in section 3. Mature.

### (g) Open mapping theorem — `Analysis/Complex/OpenMapping.lean` (root namespace)

```lean
theorem AnalyticAt.eventually_constant_or_nhds_le_map_nhds (hg : AnalyticAt ℂ g z₀) :
    (∀ᶠ z in 𝓝 z₀, g z = g z₀) ∨ 𝓝 (g z₀) ≤ map g (𝓝 z₀)
theorem AnalyticOnNhd.is_constant_or_isOpen (hg : AnalyticOnNhd ℂ g U) (hU : IsPreconnected U) :
    (∃ w, ∀ z ∈ U, g z = w) ∨ ∀ s ⊆ U, IsOpen s → IsOpen (g '' s)
theorem AnalyticOnNhd.is_constant_or_isOpenMap (hg : AnalyticOnNhd ℂ g .univ) : ...
```

Planar only (no manifold version), mature.

### (h) Maximum principle — `Analysis/Complex/AbsMax.lean` (namespace `Complex`)

`Complex.norm_eqOn_closedBall_of_isMaxOn (hd : DiffContOnCl ℂ f (ball z r))
(hz : IsMaxOn (norm ∘ f) (ball z r) z) : EqOn (norm ∘ f) (const E ‖f z‖) (closedBall z r)`;
`Complex.eventually_eq_of_isLocalMax_norm`; `Complex.exists_mem_frontier_isMaxOn_norm
[FiniteDimensional ℂ E]`; `Complex.norm_le_of_forall_mem_frontier_norm_le`;
`Complex.eqOn_of_eqOn_frontier`. Mature and extensive.

### (i) Montel, Arzela-Ascoli, Hurwitz

- **Montel / normal families: ABSENT** (only "Montel space" in `Analysis/Distribution/`,
  unrelated). Closest building block: `Analysis/Complex/LocallyUniformLimit.lean` —
  `TendstoLocallyUniformlyOn.differentiableOn [φ.NeBot] (hf : TendstoLocallyUniformlyOn F f φ U)
  (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U) (hU : IsOpen U) : DifferentiableOn ℂ f U`, and
  `TendstoLocallyUniformlyOn.deriv` (Weierstrass convergence theorem). **We must prove Montel**
  (from Cauchy estimates + Arzela-Ascoli); this is a prerequisite for the Schwartz finiteness
  argument.
- **Arzela-Ascoli: EXISTS.** `Topology/UniformSpace/Ascoli.lean`:
  `ArzelaAscoli.isCompact_of_equicontinuous (S : Set C(X, α)) (hS1 : IsCompact
  (ContinuousMap.toFun '' S)) (hS2 : Equicontinuous ((↑) : S → X → α)) : IsCompact S`, plus
  `isCompact_closure_of_isClosedEmbedding`, `compactSpace_of_isClosedEmbedding`. Metric version:
  `Topology/ContinuousMap/Bounded/ArzelaAscoli.lean` (`arzela_ascoli`, `arzela_ascoli₁`,
  `arzela_ascoli₂`).
- **Hurwitz (zeros of limits of holomorphic functions): ABSENT** (all `Hurwitz` hits are the
  Hurwitz zeta function).

### (j) Schwarz, Liouville, argument principle, Rouché, winding numbers

- `Analysis/Complex/Schwarz.lean`: `Complex.dist_le_dist_of_mapsTo_ball`,
  `Complex.norm_le_norm_of_mapsTo_ball`, `Complex.norm_deriv_le_one_of_mapsTo_ball`. Mature.
- `Analysis/Complex/Liouville.lean`: `Differentiable.apply_eq_apply_of_bounded
  (hf : Differentiable ℂ f) (hb : IsBounded (range f)) (z w : E) : f z = f w`,
  `Differentiable.exists_eq_const_of_bounded`, `Differentiable.eq_const_of_tendsto_cocompact`.
  Mature.
- **Argument principle: ABSENT. Rouché: ABSENT. Winding numbers: ABSENT** (greps clean). The
  argument principle on `X` (blueprint `meromorphic-trace`) has no planar predecessor to lift —
  we build it from the residue calculus we define.

## 6. Line/curve integrals and Stokes-type theorems (planar)

### `intervalIntegral` FTC — `MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`

Namespace `intervalIntegral`. FTC-1 comes in `_right`/`_left` variants (no bare
`integral_hasDerivAt`):

```lean
theorem intervalIntegral.integral_hasDerivAt_right (hf : IntervalIntegrable f volume a b)
    (hmeas : StronglyMeasurableAtFilter f (𝓝 b)) (hb : ContinuousAt f b) :
    HasDerivAt (fun u => ∫ x in a..u, f x) (f b) b
```

FTC-2:

```lean
theorem intervalIntegral.integral_eq_sub_of_hasDerivAt
    (hderiv : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' volume a b) : ∫ y in a..b, f' y = f b - f a
theorem intervalIntegral.integral_deriv_eq_sub
    (hderiv : ∀ x ∈ [[a, b]], DifferentiableAt ℝ f x)
    (hint : IntervalIntegrable (deriv f) volume a b) : ∫ y in a..b, deriv f y = f b - f a
```

plus `integral_eq_sub_of_hasDerivAt_of_le`, `integral_eq_sub_of_hasDeriv_right(_of_le)`,
`integral_hasStrictDerivAt_right`, `integral_hasFDerivAt`. Foundational, very mature.

### Divergence theorem — `MeasureTheory/Integral/DivergenceTheorem.lean` (namespace `MeasureTheory`)

(There is NO `Analysis/Calculus/DivergenceTheorem.lean`.) The n-dimensional statement:

```lean
theorem MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable (hle : a ≤ b)
    (f : ℝⁿ⁺¹ → Eⁿ⁺¹) (f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹) (s : Set ℝⁿ⁺¹) (hs : s.Countable)
    (Hc : ContinuousOn f (Icc a b))
    (Hd : ∀ x ∈ (Set.pi univ fun i => Ioo (a i) (b i)) \ s, HasFDerivAt f (f' x) x)
    (Hi : IntegrableOn (fun x => ∑ i, f' x (e i) i) (Icc a b)) :
    (∫ x in Icc a b, ∑ i, f' x (e i) i) =
      ∑ i, ((∫ x in face i, f (frontFace i x) i) - ∫ x in face i, f (backFace i x) i)
```

**The exact 2D Green-type statements (this is all mathlib has):**

```lean
theorem MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le
    (f g : ℝ × ℝ → E) (f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E) (a b : ℝ × ℝ) (hle : a ≤ b)
    (s : Set (ℝ × ℝ)) (hs : s.Countable)
    (Hcf : ContinuousOn f (Icc a b)) (Hcg : ContinuousOn g (Icc a b))
    (Hdf : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2 \ s, HasFDerivAt f (f' x) x)
    (Hdg : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2 \ s, HasFDerivAt g (g' x) x)
    (Hi : IntegrableOn (fun x => f' x (1, 0) + g' x (0, 1)) (Icc a b)) :
    (∫ x in Icc a b, f' x (1, 0) + g' x (0, 1)) =
      (((∫ x in a.1..b.1, g (x, b.2)) - ∫ x in a.1..b.1, g (x, a.2)) +
          ∫ y in a.2..b.2, f (b.1, y)) - ∫ y in a.2..b.2, f (a.1, y)
```

plus `integral_divergence_prod_Icc_of_hasFDerivAt_of_le` (no exceptional set),
`integral2_divergence_prod_of_hasFDerivAt_off_countable` (iterated-integral form over
`[[a₁,b₁]] ×ˢ [[a₂,b₂]]`, no `a ≤ b` needed), `integral2_divergence_prod_of_hasFDerivAt`, and
`integral_divergence_of_hasFDerivAt_off_countable_of_equiv` (transport along `F ≃L[ℝ] ℝⁿ⁺¹`).
This rectangle divergence theorem is precisely the blueprint's `planar-stokes-atoms` seed —
mature and directly usable.

### BoxIntegral — `Analysis/BoxIntegral/`

Files: `Basic`, `Integrability`, `UnitPartition`, `DivergenceTheorem`, `Box/{Basic,
SubboxInduction}`, `Partition/{Basic,Filter,Additive,Split,Tagged,SubboxInduction,Measure}`.
Main engine: `BoxIntegral.hasIntegral_GP_divergence_of_forall_hasDerivWithinAt` (Henstock-
Kurzweil divergence theorem, underlies the MeasureTheory one). Mature but low-level; consume
via the `MeasureTheory` wrappers.

### Green's theorem (curve-integral form) — ABSENT

Grep "Green" over Analysis/MeasureTheory: only arrow-color comments. The 2D results exist only
as boundary interval-integrals over rectangles (above), never as `∮_∂U ω`.

### Curve integrals of 1-forms — EXISTS (new, 2025, Kudryashov)

`MeasureTheory/Integral/CurveIntegral/Basic.lean`:

```lean
def CurveIntegrable (ω : E → E →L[𝕜] F) (γ : Path a b) : Prop :=
  IntervalIntegrable (curveIntegralFun ω γ) volume 0 1
noncomputable irreducible_def curveIntegral (ω : E → E →L[𝕜] F) (γ : Path a b) : F
-- = ∫ t in 0..1, ω (γ.extend t) (derivWithin γ.extend I t);  notation ∫ᶜ x in γ, ω x
```

(`𝕜 = ℝ` or `ℂ` via `[RCLike 𝕜]`; 1-forms are `E → E →L[𝕜] F`.) API:
`curveIntegral_refl/_symm/_trans`, linearity, `curveIntegral_eq_intervalIntegral_deriv`,
`curveIntegral_segment`, `norm_curveIntegral_segment_le`,
`ContinuousOn.curveIntegrable_of_contDiffOn`,
`HasFDerivAt.curveIntegral_segment_source`.

`MeasureTheory/Integral/CurveIntegral/Poincare.lean` — Poincaré lemma / homotopy invariance for
closed 1-forms on `E`:
`ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt_off_countable`
(+ `_of_hasFDerivWithinAt`, `_of_diffContOnCl`),
`Convex.exists_forall_hasFDerivWithinAt_of_hasFDerivWithinAt_symmetric` (primitive existence on
convex sets), `Convex.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric`.
Young but well-built; **this covers planar path integrals and their homotopy invariance** — the
blueprint's `paths-and-integrals` unit can consume it in charts, though integration of 1-forms
*on the surface itself* still needs our own layer.

## 7. Lattices and tori

### `ZLattice` — `Algebra/Module/ZLattice/{Basic,Covolume,Summable}.lean`

```lean
class IsZLattice (K : Type*) [NormedField K] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace K E] (L : Submodule ℤ E) [DiscreteTopology L] : Prop where
  span_top : span K (L : Set E) = ⊤                                    -- Basic.lean:435
```

(discreteness is a typeclass *prerequisite*, not a field). Structure theorems (under
`[NormedField K] [LinearOrder K] [IsStrictOrderedRing K] [HasSolidNorm K] [FloorRing K]
[FiniteDimensional K E] [ProperSpace E] [DiscreteTopology L]`):

- `ZLattice.FG [IsZLattice K L] : L.FG` (`:452`); `ZLattice.module_finite` (`:488`);
  `ZLattice.module_free [IsZLattice K L] : Module.Free ℤ L` (`:512`)
- `ZLattice.rank [IsZLattice K L] : finrank ℤ L = finrank K E` (`:525`) — **the full-rank
  dimension theorem**
- `Module.Basis.ofZLatticeBasis : Basis ι K E` (`:612`) — a ℤ-basis of `L` is a `K`-basis of `E`
- `IsZLattice.basis : Basis ι ℤ L` (`:686`)
- Instance `span ℤ (Set.range b)` is an `IsZLattice ℝ` for `b : Basis ι ℝ E`, `[Finite ι]` (`:440`)

`ZSpan` API (same file): `ZSpan.fundamentalDomain b : Set E` (`:92`), `fract`/`floor`/`ceil`
(`:125-199`), `ZSpan.quotientEquiv : E ⧸ span ℤ (Set.range b) ≃ fundamentalDomain b` (`:272` —
**only an `Equiv`, not `≃ₜ`**), `DiscreteTopology (span ℤ (Set.range b))` instance (`:320`),
`ZSpan.isAddFundamentalDomain [Finite ι] ... : IsAddFundamentalDomain (span ℤ (Set.range b))
(fundamentalDomain b) μ` (`:353`).

Covolume (`Covolume.lean`): `ZLattice.covolume (μ : Measure E) : ℝ` (`:72`),
`covolume_eq_measure_fundamentalDomain` (`:84`), `covolume_pos` (`:98`), `covolume_eq_det`
(`:125`), lattice-point counting asymptotics `ZLattice.covolume.tendsto_card_div_pow` (`:214ff`).
Mature (used heavily by number theory).

### Quotient topology `E ⧸ L` — `Topology/Algebra/Group/Quotient.lean`

`QuotientAddGroup.instTopologicalSpace` (`:32`), `instIsTopologicalGroup [N.Normal]` (`:151`),
`instLocallyCompactSpace` (`:121`), `discreteTopology_iff : DiscreteTopology (G ⧸ N) ↔ IsOpen N`
(`:88`), `instT1Space [IsClosed N]` (`:109`), `instT3Space` (`:165`). `CompactSpace (G ⧸ N)`
only from `[CompactSpace G]` (`:36`).

**ABSENT: compactness of `E ⧸ L` for a full lattice.** No theorem anywhere states `E ⧸ L`
compact for `IsZLattice` (`ZSpan.quotientEquiv` being a bare `Equiv` transports nothing). We
must prove it (easy: continuous surjection from the compact closure of `fundamentalDomain b`).

### `AddCircle` — `Topology/Instances/AddCircle/{Defs,Real,DenseSubgroup}.lean`

`abbrev AddCircle [AddCommGroup 𝕜] (p : 𝕜) := 𝕜 ⧸ zmultiples p` (`Defs.lean:193`);
`UnitAddCircle := AddCircle (1:ℝ)`. Compactness: `instance compactSpace [Fact (0 < p)] :
CompactSpace (AddCircle p)` (`Real.lean:33`); `pathConnectedSpace` (`:29`);
`ProperlyDiscontinuousVAdd (zmultiples p).op ℝ` (`:39`); `DivisibleBy (AddCircle p) ℤ`
(`Defs.lean:553`). Normed group structure: `Analysis/Normed/Group/AddCircle.lean:43`
(`NormedAddCommGroup (AddCircle p)` via `QuotientAddGroup.instNormedAddCommGroup`).
`AddCircle.homeomorphCircle (hT : T ≠ 0) : AddCircle T ≃ₜ Circle`
(`Analysis/SpecialFunctions/Complex/Circle.lean:381`).

### Complex tori — ABSENT

Grep "torus": only `UnitAddTorus (d) := d → UnitAddCircle` (`Analysis/Fourier/
AddCircleMulti.lean:41`, no manifold structure), `torusIntegral` (`MeasureTheory/Integral/
TorusIntegral.lean` — the ℂⁿ polydisc-boundary integral, unrelated), and doc comments. **No
manifold/`ChartedSpace` structure on `AddCircle` or any `E ⧸ L`** (greps clean). The
`ZLattice`-quotient torus with its complex-manifold and Lie-group structure is entirely ours to
build; mathlib supplies the lattice algebra, discreteness, fundamental domains, and the
topological-group quotient.

## 8. Lie groups

`Geometry/Manifold/Algebra/` files: `LieGroup`, `Monoid`, `SMul`, `SmoothFunctions`,
`Structures`, `LeftInvariantDerivation`.

```lean
-- Geometry/Manifold/Algebra/Monoid.lean:51/:65  (NO SmoothMul/SmoothAdd — renamed)
class ContMDiffAdd (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (G) [Add G] [TopologicalSpace G]
    [ChartedSpace H G] : Prop extends IsManifold I n G where
  contMDiff_add : ContMDiff (I.prod I) I n fun p : G × G ↦ p.1 + p.2
@[to_additive] class ContMDiffMul ... contMDiff_mul ...

-- Geometry/Manifold/Algebra/LieGroup.lean:62/:73
class LieAddGroup (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω) (G) [AddGroup G] [TopologicalSpace G]
    [ChartedSpace H G] : Prop extends ContMDiffAdd I n G where
  contMDiff_neg : ContMDiff I I n fun a : G ↦ -a
@[to_additive] class LieGroup ... contMDiff_inv ...
```

Parametrized by `n : ℕ∞ω` (so `ω`-Lie groups are expressible). Instances:

- `instNormedSpaceLieAddGroup : LieAddGroup 𝓘(𝕜, E) n E` (`LieGroup.lean:197`) — a normed
  space is an additive Lie group (this covers `ℂ^g`).
- `ContMDiffRing.toLieAddGroup`, `instFieldContMDiffRing` (`Structures.lean:43`, `:53`).
- `Circle`: `LieGroup (𝓡 1) ω Circle` (`Geometry/Manifold/Instances/Sphere.lean:559`).
- Units of a normed algebra (`Instances/UnitsOfNormedAlgebra.lean`).

**ABSENT**: quotient of a Lie group by a discrete subgroup (no manifold structure on quotients
at all), smooth covering maps (`IsCoveringMap` never appears in `Geometry/`). The
`Jacobian = ℂ^g/Λ` Lie-group structure is a from-scratch build; the payoff is that
`LieAddGroup 𝓘(ℂ, ℂ^g)-style` classes are ready to be instantiated once we make the charts.

## 9. Topology

### Covering maps — `Topology/Covering/{Basic,Quotient,AddCircle}.lean`

```lean
def IsEvenlyCovered (f : E → X) (x : X) (I : Type*) [TopologicalSpace I] :=
  DiscreteTopology I ∧ ∃ U, x ∈ U ∧ IsOpen U ∧ IsOpen (f ⁻¹' U) ∧
    ∃ H : f ⁻¹' U ≃ₜ U × I, ∀ x, (H x).1.1 = f x                     -- Basic.lean:40
def IsCoveringMap (f : E → X) := ∀ x, IsEvenlyCovered f x (f ⁻¹' {x})  -- Basic.lean:287
```

with `IsCoveringMap.isLocalHomeomorph` (`:339`), `.isOpenMap` (`:342`), `.isQuotientMap`
(`:345`), constructors `mk`/`mk'`, `IsFiberBundle.isCoveringMap` (`:418`).
`Covering/Quotient.lean`: `IsQuotientCoveringMap` / `IsAddQuotientCoveringMap` (`:28`, `:38`) —
covering maps from properly-discontinuous group actions —
`isCoveringMapOn_quotientMk_of_properlyDiscontinuousSMul` (`:155`),
`IsQuotientCoveringMap.isCoveringMap` (`:213`). `Covering/AddCircle.lean`:
`AddCircle.isCoveringMap_coe : IsCoveringMap ((↑) : 𝕜 → AddCircle p)` (`:32`) — **ℝ covers the
circle**. This quotient-covering API is exactly what `ℂ^g → ℂ^g/Λ` will instantiate
(topologically).

### Path/homotopy lifting and monodromy — `Topology/Homotopy/Lifting.lean` (rich, recent)

- `IsCoveringMap.exists_path_lifts (γ : C(I, X)) (e : E) (γ_0 : γ 0 = p e) :
  ∃ Γ : C(I, E), p ∘ Γ = γ ∧ Γ 0 = e` (`:216`); named lift `liftPath` (`:257`) + uniqueness
  `eq_liftPath_iff'` (`:270`).
- Homotopy lifting `liftHomotopy` (`:297`), `liftHomotopyRel` (`:329`).
- `monodromy_theorem` (`:152`) — lifts of rel-endpoint-homotopic paths end at the same point.
- `IsCoveringMap.monodromy {x y : X} (γ : Path.Homotopic.Quotient x y) :
  p ⁻¹' {x} → p ⁻¹' {y}` (`:370`), `monodromy_bijective` (`:400`),
  `monodromyFunctor : FundamentalGroupoid X ⥤ Type _` (`:394`).
- **Lifting criterion**: `existsUnique_continuousMap_lifts [SimplyConnectedSpace A]
  [LocPathConnectedSpace A] (f : C(A,X)) ... : ∃! F : C(A,E), F a₀ = e₀ ∧ p ∘ F = f` (`:421`)
  and Hatcher 1.33 `existsUnique_continuousMap_lifts_of_range_le` (`:439`).

Note: mathlib's "monodromy" is for covering maps only — the blueprint's *analytic-continuation
monodromy along chains of charts* is a different device we build ourselves (but this file's
statements are the model).

### Fundamental group and simple connectivity

- `FundamentalGroup (X) (x : X) := End (FundamentalGroupoid.mk x)`
  (`AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean:35`), `Group` instance,
  `fundamentalGroupMulEquivOfPathConnected` (`:54`);
  `HomotopyGroup.pi1EquivFundamentalGroup` (`Topology/Homotopy/HomotopyGroup.lean:525`).
- `class SimplyConnectedSpace (X) : Prop where equiv_unit :
  Nonempty (FundamentalGroupoid X ≌ Discrete Unit)`
  (`AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean:38`), with
  `simply_connected_iff_paths_homotopic` (`:86`), `simply_connected_iff_loops_nullhomotopic`
  (`:104`), instance `SimplyConnectedSpace → PathConnectedSpace` (`:68`),
  `SimplyConnectedSpace.ofContractible` (`:77`).
- `Path.Homotopic` (`Topology/Homotopy/Path.lean:241`), `Path.Homotopic.Quotient`;
  `LocPathConnectedSpace` (`Topology/Connected/LocPathConnected.lean:55`). All mature.

### ABSENT (all greps clean)

- **`π₁(S¹) ≅ ℤ`** — not assembled (all ingredients present: covering, monodromy functor,
  lifting).
- **`SimplyConnectedSpace (sphere ...)` for S², or any sphere** — nothing; the only
  sphere-related statements are `proof_wanted` stubs in
  `Geometry/Manifold/PoincareConjecture.lean:47-52`. The backward headline's "S² is simply
  connected" must be proven by us (e.g. via two-chart covers and a hand-rolled van Kampen
  special case, or direct loop subdivision).
- **Topological Seifert-van Kampen** — only the *categorical* van Kampen colimit notion
  (`CategoryTheory/Limits/VanKampen.lean`), unusable directly.
- **Universal cover (topological)** — nothing.
- **Classification of surfaces, Euler characteristic (topological)** — nothing (`eulerChar` is
  the order-theoretic Möbius one in `Combinatorics/`).
- Singular homology exists but is embryonic: `AlgebraicTopology/SingularHomology/Basic.lean` —
  `singularHomologyFunctor [CategoryWithHomology C] : C ⥤ TopCat.{w} ⥤ C` (`:54`), H₀
  identified, homotopy invariance in progress; **no computations** (no `H_*(Sⁿ)`).

## 10. Sheaf / Cech machinery

### `Topology/Sheaves/` — the topological sheaf stack (mature)

`Presheaf.lean:45` `def TopCat.Presheaf (X : TopCat) := (Opens X)ᵒᵖ ⥤ C` with pushforward
`f _* ℱ`, pullback, restriction. `Sheaf.lean:85` `TopCat.Presheaf.IsSheaf` (via
`Opens.grothendieckTopology`), `:108` bundled `TopCat.Sheaf C X`. Sheaf-condition
reformulations in `SheafCondition/`: `EqualizerProducts`, `OpensLeCover`,
`PairwiseIntersections`, and crucially `UniqueGluing.lean:77` `IsSheafUniqueGluing` +
`isSheaf_iff_isSheafUniqueGluing_types` (`:125`) — the concrete gluing form. `Stalks.lean:82`
`stalk`, `:92` `germ`; `Sheafify.lean:68` (Type-valued sheafification); `Skyscraper.lean`
(`skyscraperPresheaf`/`skyscraperSheaf` + stalk adjunction — **useful for the χ ledger**);
`Abelian.lean` (`exact_iff_stalkFunctor_map_exact`); `Flasque.lean`; `MayerVietoris.lean`
(`mayerVietorisSquare` for `Opens`). `Geometry/RingedSpace/`: `PresheafedSpace`,
`SheafedSpace`, `LocallyRingedSpace`, stalk maps.

### Cech machinery — partial

- Simplicial Cech nerve: `AlgebraicTopology/CechNerve.lean` (`Arrow.cechNerve`,
  `augmentedCechNerve`, adjunction).
- **Cech cochain complex exists** (new, Riou 2026):
  `CategoryTheory/Sites/SheafCohomology/Cech.lean:65`
  `cechComplexFunctor : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ` — given `U : ι → C` (needs
  `HasFiniteProducts C`, `Preadditive A`, `HasProducts A`), degree n is
  `∏ (x : Fin (n+1) → ι), P(∏ U (x i))`. **No packaged Cech cohomology groups Hⁿ, no
  refinement maps, no Leray theorem, no Cech-to-derived comparison.**
- Degree-1 nonabelian cohomology `H1` of a presheaf of groups:
  `CategoryTheory/Sites/NonabelianCohomology/H1.lean` (`OneCocycle`, `IsCohomologous`,
  `H1 := Quot ...` `:197`).

### Abstract sheaf cohomology — exists (Ext-based, site-theoretic)

`CategoryTheory/Sites/SheafCohomology/Basic.lean:59`
`abbrev Sheaf.H (F : Sheaf J AddCommGrpCat) (n : ℕ) : Type w' := Ext ((constantSheaf J
AddCommGrpCat).obj (.of (ULift ℤ))) F n` (needs `HasSheafify`, `HasExt`), `H.equiv₀` (`:105`),
Mayer-Vietoris LES (`MayerVietoris.lean:127-140`, `sequence_exact`).

### Homological algebra toolkit (what we'd actually consume for hand-rolled Cech H¹)

`Algebra/Homology/HomologicalComplex.lean:59`; `ShortComplex/Basic.lean:34`,
`ShortComplex/Exact.lean`, `ShortComplex/ShortExact.lean:35`;
**snake lemma**: `Algebra/Homology/ShortComplex/SnakeLemma.lean` (`structure SnakeInput` `:64`
with connecting map); homology LES `Algebra/Homology/HomologySequence.lean`;
derived functors `CategoryTheory/Abelian/RightDerived.lean` (`Functor.rightDerived`);
`Ext` (derived-category): `Algebra/Homology/DerivedCategory/Ext/Basic.lean:120` +
`Ext/ExactSequences.lean`.

**Assessment.** The blueprint's plan (hand-rolled, germ-valued Cech cochains over chart-disk
covers, finite-dimensional linear algebra on `H¹ = Z/B`) does NOT need the category-theoretic
stack, and trying to use `Sheaf.H`/`cechComplexFunctor` would force us into `AddCommGrpCat`
categorical plumbing with no Leray/refinement support. Recommended: plain `Module ℂ` cochain
spaces + `LinearMap` differentials; use mathlib's `Submodule.Quotient`, `finrank` API instead.
The skyscraper/stalk material and `IsSheafUniqueGluing` are still useful references.

## 11. Partitions of unity

### Manifold PoU — `Geometry/Manifold/PartitionOfUnity.lean`

Structure names still `SmoothPartitionOfUnity` / `SmoothBumpCovering` (functions hard-coded
`C^∞⟮I, M; 𝓘(ℝ), ℝ⟯`); many lemmas renamed `exists_smooth_*` → `exists_contMDiff*` in 2025-26
(deprecated aliases still present).

```lean
structure SmoothPartitionOfUnity (ι) (I : ModelWithCorners ℝ E H) (M) (s : Set M := univ) where
  toFun : ι → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯
  locallyFinite' : LocallyFinite fun i => support (toFun i)
  nonneg' : ∀ i x, 0 ≤ toFun i x
  sum_eq_one' : ∀ x ∈ s, ∑ᶠ i, toFun i x = 1
  sum_le_one' : ∀ x, ∑ᶠ i, toFun i x ≤ 1

theorem SmoothPartitionOfUnity.exists_isSubordinate {s : Set M} (hs : IsClosed s)
    (U : ι → Set M) (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃ i, U i) :
    ∃ f : SmoothPartitionOfUnity ι I M s, f.IsSubordinate U
```

Typeclass footprint on the concrete corollaries: `[FiniteDimensional ℝ E]`,
`[IsManifold I ∞ M]`, `[SigmaCompactSpace M]`, `[T2Space M]`. Other key results:
`exists_contMDiffMap_forall_mem_convex_of_local`, `exists_contMDiffMap_zero_one_of_isClosed`,
`exists_contMDiffMap_one_nhds_of_subset_interior`, `IsOpen.exists_contMDiff_support_eq`,
`SmoothBumpCovering.exists_isSubordinate [T2Space M] [SigmaCompactSpace M]` (`:364`).

### Bump functions — `Geometry/Manifold/BumpFunction.lean`

`structure SmoothBumpFunction (c : M) extends ContDiffBump (extChartAt I c c)` with
`eventuallyEq_one`, `support_*`, `tsupport_subset_chartAt_source`, `contMDiff_smul`. Mature.

### Topological PoU — `Topology/PartitionOfUnity.lean`

`PartitionOfUnity`, `BumpCovering`; `PartitionOfUnity.exists_isSubordinate [NormalSpace X]
[ParacompactSpace X] (hs : IsClosed s) (U : ι → Set M) ... : ∃ f, f.IsSubordinate U` (`:622`).

### Applicability to complex manifolds — YES, automatic downgrade

`Geometry/Manifold/IsManifold/Basic.lean:856`:

```lean
instance {a : ℕ∞ω} [IsManifold I ω M] : IsManifold I a M := IsManifold.of_le le_top
```

so an analytic manifold instance yields `IsManifold I ∞ M` (and every lower regularity) by
instance resolution. Caveat: the PoU theorems require a **real** model `I : ModelWithCorners ℝ
E H` — for a Riemann surface with `ChartedSpace ℂ X` there is no automatic
`ChartedSpace ℂ X → IsManifold 𝓘(ℝ, ℂ) ∞ X` bridge in mathlib (see section 16); we must set up
the `𝓘(ℝ, ℂ)`-manifold structure on `X` ourselves once (the model spaces coincide: `H = E = ℂ`,
so the same charts work — the content is `contDiffGroupoid ∞ 𝓘(ℝ,ℂ)`-membership of transition
maps, i.e. holomorphic ⇒ real-smooth). After that, smooth partitions of unity on our compact
surface come for free (compact + T2 gives sigma-compact; `FiniteDimensional ℝ ℂ` holds).

## 12. Functional analysis

### Compact operators — `Analysis/Normed/Operator/Compact/` (reorganized 2026)

```lean
def IsCompactOperator {M₁ M₂ : Type*} [Zero M₁] [TopologicalSpace M₁] [TopologicalSpace M₂]
    (f : M₁ → M₂) : Prop := ∃ K, IsCompact K ∧ f ⁻¹' K ∈ (𝓝 0 : Filter M₁)   -- Basic.lean:69
```

API (`Compact/Basic.lean`): `IsCompactOperator.add` (`:240`), `.neg`/`.sub` (`:247`/`:252`),
`comp_clm` (`:274`), `clm_comp` (`:288`),
`isCompactOperator_iff_isCompact_closure_image_closedBall` (`:194`),
`IsCompactOperator.isCompact_closure_image_of_isVonNBounded` (`:130`).
`Compact/FiniteDimension.lean`: `isCompactOperator_id_iff_finiteDimensional` (`:26`).

### Fredholm / Riesz-Schauder — the crucial piece is MISSING

- **No Fredholm operator class, no index** (greps clean).
- What exists: `Analysis/Normed/Operator/Compact/FredholmAlternative.lean` (2026) —
  `antilipschitz_of_not_hasEigenvalue (hT : IsCompactOperator T) (hμ : μ ≠ 0)` (`:54`),
  `hasEigenvalue_or_mem_resolventSet` (`:165`) (Fredholm alternative),
  `hasEigenvalue_iff_mem_spectrum` (`:222`); and
  `Analysis/InnerProductSpace/Spectrum.lean:463` `finite_dimensional_eigenspace
  (hT : IsCompactOperator T) (μ : 𝕜) (hμ : μ ≠ 0)` — finite-dimensional eigenspaces.
- **The Schwartz lemma the blueprint's `finiteness-and-chi` unit needs — "if `A` is onto and
  `K` compact then `A + K` has finite-dimensional cokernel / closed finite-codim range" — does
  NOT exist** and is not close to existing (no cokernel-side results at all). The
  kernel-side ingredients (Riesz lemma, finite-dim eigenspaces) exist:
  `Analysis/Normed/Module/RieszLemma.lean` `riesz_lemma` (`:49`),
  `riesz_lemma_of_norm_lt` (`:92`); Riesz's theorem
  `FiniteDimensional.of_isCompact_closedBall₀ (rpos : 0 < r)
  (h : IsCompact (Metric.closedBall (0:V) r)) : FiniteDimensional 𝕜 V`
  (`Analysis/Normed/Module/FiniteDimension.lean:457`).

### Function spaces

- Compact-open: `Topology/CompactOpen.lean` (`ContinuousMap.compactOpen`).
- Sup-norm on `C(α, E)` for compact `α`: `Topology/ContinuousMap/Compact.lean`
  (`NormedAddCommGroup C(α,E)` `:179`, `MetricSpace` `:82`).
- `BoundedContinuousFunction` (`α →ᵇ β`): `Topology/ContinuousMap/Bounded/Basic.lean:39`,
  completeness `instCompleteSpace` (`:303`), norm in `Bounded/Normed.lean`.
- Uniform convergence structures: `Topology/UniformSpace/UniformConvergenceTopology.lean`
  (`UniformFun` `α →ᵤ β`, `UniformOnFun` `α →ᵤ[𝔖] β`).
- Stone-Weierstrass: `Topology/ContinuousMap/StoneWeierstrass.lean` —
  `ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints` (`:265`), complex
  star-algebra version `starSubalgebra_topologicalClosure_eq_top_of_separatesPoints` (`:399`).
- Arzela-Ascoli: `Topology/UniformSpace/Ascoli.lean` —
  `ArzelaAscoli.isCompact_of_equicontinuous` (`:496`),
  `isCompact_closure_of_isClosedEmbedding` (`:471`), `compactSpace_of_isClosedEmbedding`
  (`:453`); bounded-continuous version `Topology/ContinuousMap/Bounded/ArzelaAscoli.lean`
  (`arzela_ascoli₁` `:30`, `arzela_ascoli₂` `:90`, `arzela_ascoli` `:109`).

## 13. `Polynomial` / `RatFunc`, partial fractions

### `RatFunc` — `FieldTheory/RatFunc/` (Defs, Basic, AsPolynomial, Degree, Valuation, ...)

```lean
structure RatFunc [CommRing K] : Type u where ofFractionRing ::
  toFractionRing : FractionRing K[X]          -- notation K⟮X⟯ (scoped RatFunc)
instance instField [IsDomain K] : Field K⟮X⟯
def RatFunc.C : K →+* K⟮X⟯
def RatFunc.X : K⟮X⟯
def RatFunc.eval (f : K →+* L) (a : L) (p : K⟮X⟯) : L :=
  (num p).eval₂ f a / (denom p).eval₂ f a
```

`eval` reduces to coprime `num`/`denom` first (monic denominator canonical form in
`Basic.lean`), so `eval` of `(X²-1)/(X-1)` at 1 is 2. **No bridge from `RatFunc ℂ` to
meromorphic functions** (`grep RatFunc Analysis/`: no hits) — the "traced form is rational"
step (blueprint `form-trace-tower`) needs us to relate `RatFunc ℂ` (or just meromorphic
functions on `ℙ¹`) to `MeromorphicOn` by hand.

### Partial fractions — `Algebra/Polynomial/PartialFractions.lean` (namespace `Polynomial`)

```lean
theorem Polynomial.div_prod_eq_quo_add_sum_rem_div (f : R[X]) {g : ι → R[X]} {s : Finset ι}
    (hg : ∀ i ∈ s, (g i).Monic) (hcop : Set.Pairwise ↑s fun i j => IsCoprime (g i) (g j)) :
    ∃ (q : R[X]) (r : ι → R[X]), (∀ i ∈ s, (r i).degree < (g i).degree) ∧
      ((f : K) / ∏ i ∈ s, ↑(g i)) = ↑q + ∑ i ∈ s, (r i : K) / (g i : K)
```

plus two-factor `div_eq_quo_add_rem_div_add_rem_div`, uniqueness
`quo_add_sum_rem_div_unique`, and prime-power versions
(`eq_quo_mul_pow_add_sum_rem_mul_pow`, ...). Mature.

### Fundamental theorem of algebra & root counting

- `Analysis/Complex/Polynomial/Basic.lean`: `Complex.exists_root {f : ℂ[X]}
  (hf : 0 < degree f) : ∃ z : ℂ, IsRoot f z`; `instance Complex.isAlgClosed : IsAlgClosed ℂ`.
- `Algebra/Polynomial/Roots.lean`: `Polynomial.card_roots`, `card_roots'`.
- `FieldTheory/IsAlgClosed/Basic.lean`: `Polynomial.card_roots_eq_natDegree [IsAlgClosed k] :
  p.roots.card = p.natDegree` — exact "zeros = degree" for ℂ;
  `IsAlgClosed.exists_root`, `Polynomial.roots_eq_zero_iff`.

## 14. Germs and codiscrete filters

### `Filter.Germ` — `Order/Filter/Germ/Basic.lean` (+ `OrderedMonoid.lean`)

```lean
def Filter.germSetoid (l : Filter α) (β : Type*) : Setoid (α → β)   -- :74 (r = EventuallyEq l)
def Filter.Germ (l : Filter α) (β : Type*) : Type _ := Quotient (germSetoid l β)   -- :79
def Filter.Germ.map (op : β → γ) : Germ l β → Germ l γ              -- :192
```

Coercions `Germ.ofFun` (`:112`), `Germ.const` (`:119`), `map₂` (`:209`), `liftOn` (`:176`),
`LiftPred` (`:296`); hom packages `coeMulHom` (`:415`), `coeRingHom : (α → R) →+* Germ l R`
(`:598`); instances up to `Ring`/`CommRing` (`:578`/`:594`) and `Module` (`:654`). **No
`Field`/`DivisionRing` instance** (correctly — germs at a general filter aren't a field; for
germs at `𝓝[≠] x` of meromorphic functions we'll prove field structure ourselves).

### `codiscreteWithin` — `Topology/DiscreteSubset.lean` (Kebekus)

```lean
def Filter.codiscreteWithin (S : Set X) : Filter X := ⨆ x ∈ S, 𝓝[S \ {x}] x   -- :201
def Filter.codiscrete (X : Type*) [TopologicalSpace X] : Filter X := codiscreteWithin univ -- :333
theorem Filter.mem_codiscreteWithin :
    S ∈ codiscreteWithin T ↔ ∀ x ∈ T, Disjoint (𝓝[≠] x) (𝓟 (T \ S))          -- :203
theorem Filter.mem_codiscreteWithin_accPt :
    S ∈ codiscreteWithin T ↔ ∀ x ∈ T, ¬AccPt x (𝓟 (T \ S))                    -- :217
```

plus `mem_codiscreteWithin_iff_forall_mem_nhdsNE` (`:213`), `codiscreteWithin_mono` (`:228`,
`@[gcongr]`), `codiscreteWithin_iff_locallyFiniteComplementWithin [T1Space]` (`:288`),
`compl_singleton_mem_codiscreteWithin` (`:309`), `compl_finite_mem_codiscreteWithin` (`:320`),
and the `AccPt`/`IsDiscrete` API (`discreteTopology_of_noAccPts` `:59`). Used throughout the
meromorphic stack. Mature — **this is the junk-free germ substrate the blueprint's `L(D)` model
wants** (note: the meromorphic library itself never uses the `Filter.Germ` type; it works with
`=ᶠ[codiscreteWithin U]` directly — we can choose either style).

### Meromorphic identity principles at codiscrete filters — `Analysis/Meromorphic/IsolatedZeros.lean`

`MeromorphicAt.frequently_zero_iff_eventuallyEq_zero` (`:43`),
`MeromorphicAt.eventuallyEq_zero_nhdsNE_of_eventuallyEq_zero_codiscreteWithin (hf) (h₁x : x ∈ U)
(h₂x : AccPt x (𝓟 U)) (h : f =ᶠ[codiscreteWithin U] 0)` (`:59`),
`MeromorphicOn.codiscreteWithin_setOf_ne_zero` (`:71`),
`MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin` (`:99`, `_preperfect`
variant `:109`), `MeromorphicOn.eventually_nhdsSet_eventuallyEq_codiscreteWithin` (`:118`).

## 15. Algebraic geometry: genus, Riemann-Roch, Abel, Jacobian

### Hard negatives (all greps clean across the whole library)

- **Riemann-Roch**: nothing, under any spelling.
- **Genus**: no notion of genus of a curve/surface/scheme anywhere.
- **Abel/Abel-Jacobi**: nothing (hits are Abel summation `NumberTheory/AbelSummation.lean`,
  Abel's power-series limit theorem `Analysis/Complex/AbelLimit.lean`
  (`tendsto_tsum_powerSeries_nhdsWithin_stolzSet` `:161`), `FieldTheory/AbelRuffini.lean`).
- **Weil/Cartier divisors on schemes, divisor class groups of schemes**: nothing.
- **Jacobian variety / Picard scheme**: nothing. (`WeierstrassCurve.Jacobian` is the weighted
  (2,3,1) *coordinate system* for elliptic curves, not a Jacobian variety.)

### What does exist nearby

- Elliptic curves, very mature: `AlgebraicGeometry/EllipticCurve/` —
  `structure WeierstrassCurve (R)` (`Weierstrass.lean:77`), `class IsElliptic` (`:375`),
  **j-invariant** `WeierstrassCurve.j : R := W.Δ'⁻¹ * W.c₄ ^ 3` (`:397`), full group law:
  `instance : AddCommGroup W.Point` in affine (`Affine/Point.lean:769`, via
  `toClass : W.Point →+ Additive (ClassGroup W.CoordinateRing)` `:714`), projective, and
  Jacobian coordinates; division polynomials; `LFunction.lean`.
- Weierstrass ℘ (analytic, Yang 2025): `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean` —
  `structure PeriodPair` (`:60`), `PeriodPair.lattice` (`:79`),
  `PeriodPair.weierstrassP (z : ℂ) : ℂ` (`:263`), `weierstrassP_add_coe` (periodicity),
  `meromorphic_weierstrassP`, `derivWeierstrassP`. **Not connected** to `WeierstrassCurve`
  (no uniformization); still, this is prior art for lattice-periodic meromorphic functions.
- Modular forms & Eisenstein series: `NumberTheory/ModularForms/` (mature) —
  `structure ModularForm` (`Basic.lean:75`), `eisensteinSeries` (`EisensteinSeries/Defs.lean:205`),
  level-one dimension formulas (`LevelOne/DimensionFormula.lean`).
- Schemes: `AlgebraicGeometry/Scheme.lean:42`, `Proj`
  (`ProjectiveSpectrum/Scheme.lean:842`), `Scheme.functionField`
  (`AlgebraicGeometry/FunctionField.lean:37`), Dedekind domains + `ClassGroup`
  (`RingTheory/DedekindDomain/`). None of this feeds the analytic route; per the blueprint we
  deliberately avoid scheme theory.

## 16. `ContMDiff` calculus toolkit

### Composition and products

`Geometry/Manifold/ContMDiff/Basic.lean`:

```lean
theorem ContMDiff.comp {g : M' → M''} (hg : ContMDiff I' I'' n g) (hf : ContMDiff I I' n f) :
    ContMDiff I I'' n (g ∘ f)                                             -- :103
nonrec theorem ContMDiffAt.comp {g : M' → M''} (x : M) (hg : ContMDiffAt I' I'' n g (f x))
    (hf : ContMDiffAt I I' n f x) : ContMDiffAt I I'' n (g ∘ f) x         -- :129
```

plus `ContMDiffWithinAt.comp` (`:57`), `.comp'` (`:109`), `ContMDiffAt.comp_contMDiffWithinAt`
(`:116`), `ContMDiffAt.comp_of_eq` (`:134`).

`Geometry/Manifold/ContMDiff/Constructions.lean` (spelling is `prodMk`):

```lean
nonrec theorem ContMDiffAt.prodMk (hf : ContMDiffAt I I' n f x) (hg : ContMDiffAt I J' n g x) :
    ContMDiffAt I (I'.prod J') n fun x => (f x, g x)                       -- :68
nonrec theorem ContMDiff.prodMk (hf : ContMDiff I I' n f) (hg : ContMDiff I J' n g) :
    ContMDiff I (I'.prod J') n fun x => (f x, g x)                         -- :85
theorem ContMDiff.prodMk_space (hf : ContMDiff I 𝓘(𝕜, E') n f) (hg : ContMDiff I 𝓘(𝕜, F') n g) :
    ContMDiff I 𝓘(𝕜, E' × F') n fun x => (f x, g x)                        -- :89
```

also `ContMDiffWithinAt.comp₂` / `ContMDiffAt.comp₂` (`:224`, `:241`).

### `extChartAt`

`Geometry/Manifold/IsManifold/ExtChartAt.lean`: `extChartAt (x : M) : PartialEquiv M E :=
(chartAt H x).extend I` (`:454`) with the full lemma suite (`extChartAt_source :464`,
`extChartAt_target :477`, `extChartAt_to_inv :489`, `extChartAt_source_mem_nhds :500`, ...).
`Geometry/Manifold/ContMDiff/Atlas.lean`: `contMDiffAt_extChartAt :
ContMDiffAt I 𝓘(𝕜, E) n (extChartAt I x) x` (`:102`), `contMDiffAt_extChartAt'` (`:97`).

### `𝓘(ℂ)` vs `𝓘(ℝ, ℂ)`, restrictScalars — mostly ABSENT

- **No** `IsManifold.restrictScalars`, no `ContMDiff.restrictScalars` /
  `MDifferentiable.restrictScalars`: there is no packaged "a `ℂ`-manifold is an `ℝ`-manifold"
  statement. `restrictScalars` occurs in `Geometry/Manifold/` only as internal proof machinery
  (`IsManifold/Basic.lean`, `Diffeomorph.lean:406-408`, `IsManifold/InteriorBoundary.lean:361-371`
  which uses `fderiv_restrictScalars` in proofs). In practice mathlib mixes models explicitly
  (e.g. `Instances/Sphere.lean:563` states smoothness w.r.t. `𝓘(ℝ, ℂ)`;
  `UpperHalfPlane/Manifold.lean:207, :238` restricts scalars at the derivative level).
  The blueprint's warning about the ℝ↔ℂ diamond stands: we build this bridge ourselves.

### Analytic ↔ `ContMDiff ω` — ABSENT at manifold level

Greps for `contMDiffAt_iff_analyticAt`, `analyticAt_iff_contMDiffAt`, `ContMDiffAt.analyticAt`,
`AnalyticAt.contMDiff`, `analyticGroupoid`: nothing. The bridge is only the vector-space chain
`AnalyticAt.contDiffAt` + `ContDiffAt.contMDiffAt` through charts, done ad hoc (e.g.
`UpperHalfPlane/Manifold.lean:93-95`). We will want to prove a reusable
`contMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ↔ AnalyticAt ℂ (in extChartAt coordinates)` lemma early.

### Holomorphic rigidity on complex manifolds

`Geometry/Manifold/Complex.lean` — setup: `[NormedSpace ℂ E] [NormedSpace ℂ F]`,
`{I : ModelWithCorners ℂ E H} [I.Boundaryless]`, `[ChartedSpace H M] [IsManifold I 1 M]`
(only `C¹` needed!). Main results:

- `Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax
  (hd : ∀ᶠ z in 𝓝 c, MDifferentiableAt I 𝓘(ℂ, F) f z) (hc : IsLocalMax (norm ∘ f) c) :
  ∀ᶠ y in 𝓝 c, ‖f y‖ = ‖f c‖` (`:57`) — manifold maximum-modulus principle.
- `MDifferentiableOn.norm_eqOn_of_isPreconnected_of_isMaxOn` (`:89`)
- `MDifferentiableOn.eqOn_of_isPreconnected_of_isMaxOn_norm [StrictConvexSpace ℝ F]` (`:114`)
- `MDifferentiableOn.apply_eq_of_isPreconnected_isCompact_isOpen` (`:125`)
- `MDifferentiable.isLocallyConstant [CompactSpace M] (hf : MDifferentiable I 𝓘(ℂ, F) f) :
  IsLocallyConstant f` (`:157`) — **holomorphic on compact ⇒ locally constant**.
- `MDifferentiable.apply_eq_of_compactSpace [CompactSpace M] [PreconnectedSpace M] (hf : ...)
  (a b : M) : f a = f b` (`:166`)
- `MDifferentiable.exists_eq_const_of_compactSpace` (`:172`)

There is **no** manifold open-mapping theorem and no `MDifferentiable.isConst` under that name.
The file self-describes as minimal. Usable immediately for "no nonconstant global holomorphic
functions on compact `X`"; everything else (identity theorem on surfaces, open mapping, local
normal form) must be lifted from the planar theory by hand.

## 17. Integration of differential forms on manifolds

Essentially empty; every search below verified against this commit.

- **Stokes**: `grep -rli stokes` hits exactly one file —
  `Analysis/BoxIntegral/DivergenceTheorem.lean`, and only in a keyword comment. **No Stokes
  theorem of any kind on manifolds.**
- **Differential forms** exist only on normed spaces:
  `Analysis/Calculus/DifferentialForm/{Basic,VectorField}.lean` — forms are
  `ω : E → E [⋀^Fin n]→L[𝕜] F`, with `extDeriv` / `extDerivWithin`
  (`extDeriv (ω) (x) := .alternatizeUncurryFin (fderiv 𝕜 ω x)`), `extDeriv_extDeriv` (d∘d = 0),
  `extDeriv_pullback`. The file's own TODO says manifold forms are "not defined yet". No
  `⋀`/`AlternatingMap` anywhere under `Geometry/Manifold/`.
- **No measure/volume on manifolds**: no `MeasureSpace` instance, no volume form, no
  `Geometry/Manifold/Measure*`.
- Riemannian layer exists but is metric-only: `Topology/VectorBundle/Riemannian.lean`
  (`RiemannianMetric` `:370`), `Geometry/Manifold/VectorBundle/Riemannian.lean`
  (`ContMDiffRiemannianMetric` `:244`), `Geometry/Manifold/Riemannian/Basic.lean`
  (`IsRiemannianManifold`), `Geometry/Manifold/Riemannian/PathELength.lean` —
  `riemannianEDist` (`:208`) and `pathELength` (an `∫ ‖mfderiv γ‖` **length** functional —
  the only mfderiv-based path integral in mathlib; not a 1-form integral).

Consequence: the blueprint's routing is confirmed — define `∫_γ ω` on the surface ourselves
(via charts / `curveIntegral` in local coordinates, or Forster's discrete chain continuation),
and reduce all global Stokes uses to the planar rectangle divergence theorem (section 6) through
partitions of unity (section 11). Do not wait for or attempt general manifold Stokes.

---

## Gaps: the ten biggest things mathlib definitely does NOT have

Ranked by how much of our critical path they carry. Everything below was verified absent at
this commit (greps in the relevant sections above).

1. **Riemann surfaces as such, and `ℙ¹` as a complex manifold.** No 1-dimensional complex
   manifold theory; no `ChartedSpace ℂ (OnePoint ℂ)`, no complex structure on `S²` or on
   `Projectivization`. We build the surface API, the two-chart `ℙ¹`, and the
   `X ≃ₜ S²` bridge (mathlib does give `OnePoint V ≃ₜ sphere` topologically).

2. **The ℝ↔ℂ manifold bridge.** No `IsManifold.restrictScalars`, no
   `contMDiffAt ω ↔ AnalyticAt` API, no packaged "complex manifold ⇒ underlying real smooth
   manifold". Needed early (partitions of unity require a real model); the blueprint's
   diamond warning stands.

3. **Residue calculus: residues, argument principle, winding numbers, analytic Laurent
   expansions, principal parts.** None exist. We define `resAt` from `circleIntegral` +
   annulus deformation + the `meromorphicOrderAt` factorization, and build Mittag-Leffler
   principal-part distributions ourselves.

4. **Cech cohomology of sheaves on a space.** Only a categorical `cechComplexFunctor` (no Hⁿ,
   no refinements, no Leray covers, no comparison). Our germ-valued cochain complex over
   codiscrete sets is a from-scratch build (on `Function.locallyFinsuppWithin` +
   `codiscreteWithin` foundations that DO exist).

5. **Montel's theorem / normal families.** Absent. Must be assembled from Cauchy estimates +
   `ArzelaAscoli.isCompact_of_equicontinuous` + `TendstoLocallyUniformlyOn.differentiableOn`
   (all present). Input to finiteness.

6. **Schwartz finiteness / any Fredholm-cokernel theory.** "Onto + compact perturbation ⇒
   finite-dimensional cokernel" does not exist; mathlib has no cokernel-side compact-operator
   results at all (only the Fredholm alternative and finite-dim eigenspaces). This is the
   heaviest pure-functional-analysis debt on the critical path (`H¹` finiteness).

7. **The ∂̄ theory.** No Cauchy-transform solution of `∂̄u = f` on a disk, no Dolbeault
   anything, no almost-complex/`(0,1)`-projection API. The one PDE atom (Forster 13.2) and the
   intrinsic ∂̄ operator are entirely ours.

8. **Manifold integration: Stokes, differential forms on manifolds, curve integrals of 1-forms
   on manifolds.** All absent (section 17). Planar substitutes exist (`curveIntegral` on normed
   spaces with homotopy invariance; rectangle divergence theorem) — the surface-level layer
   (holomorphic 1-forms as a ℂ-vector space, `∫_γ ω` on `X`, periods) is ours.

9. **Quotient manifolds and Lie-group quotients: `ℂ^g/Λ` as a complex torus.** No manifold
   structure on `E ⧸ L` or `AddCircle`, no "quotient by discrete subgroup is a Lie group", no
   smooth covering maps, and not even compactness of `E ⧸ L` for a full `ZLattice`. Mathlib
   contributes the `ZLattice` algebra (`module_free`, `rank`, fundamental domains,
   discreteness) and the topological quotient-covering API; charts, `IsManifold`, `LieAddGroup`
   and compactness of the torus are ours.

10. **Everything genus/Riemann-Roch/Serre/Abel-shaped, plus its small prerequisites.** No
    genus, no RR, no Serre duality, no Abel-Jacobi, no divisor degree functional (no `degree`
    on `locallyFinsuppWithin`), no `RatFunc ℂ` ↔ meromorphic-function bridge, no `π₁(S¹) ≅ ℤ`,
    no simply-connectedness of `S²`, no topological van Kampen, no Hurwitz theorem on limits of
    zero-free functions. These are the theorems the project exists to prove — plus a handful of
    library-sized lemmas (divisor degree, S² topology) we should budget for explicitly.
