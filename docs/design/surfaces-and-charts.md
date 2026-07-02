# Design: surfaces-and-charts (`Jacobian/Surface/`)

Owner of CC7 (`docs/design/core-choices.md`). Blueprint entry: `clean_room_blueprint.md`
§surfaces-and-charts (foundation unit, no dependencies). References: Forster §1 (book 1–9 =
PDF 7–15), §2 (book 10–13 = PDF 16–19), Appendix A (book 237–238 = PDF 243–244).

All facts below marked **[spiked]** were verified by compilation against the pinned mathlib
(`548398201`) via `scratch_surfaces.lean`; see §7 for the spike record. Everything cited from
mathlib was read in `.lake/packages/mathlib` source, not from memory.

Standing variables (used verbatim throughout; per `CONVENTIONS.md`, `[CompactSpace X]`
/`[ConnectedSpace X]` are dropped — no lemma in this unit needs them except where written):

```lean
open scoped ContDiff Manifold
open Set Filter Topology

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {n : ℕ∞ω}   -- ℕ∞ω = WithTop ℕ∞; ω = ⊤, ∞ = ((⊤ : ℕ∞) : ℕ∞ω)
```

All declarations live in `namespace RS`. Note `Y := ℂ` instantiates every `X → Y` lemma
(`ChartedSpace ℂ ℂ` and `IsManifold 𝓘(ℂ) ω ℂ` hold by `instIsManifoldModelSpace`), so the
`X → ℂ` special cases below are provided only where the statement genuinely simplifies
(no `writtenInExtChartAt`, no `ContinuousAt` side condition).

---

## 1. The 𝓘(ℝ,ℂ) story — the true, compiled facts (CC7)

`𝓘(ℂ) = modelWithCornersSelf ℂ ℂ : ModelWithCorners ℂ ℂ ℂ` and
`𝓘(ℝ,ℂ) = modelWithCornersSelf ℝ ℂ : ModelWithCorners ℝ ℂ ℂ` are **different terms of
different types** (the scalar field is part of the type), so there is no "equality of models".
But both have `toPartialEquiv = PartialEquiv.refl ℂ` definitionally, both have `H = E = ℂ`, and
they share the *same* `ChartedSpace ℂ X` instance. Consequences, all **[spiked]**:

1. `extChartAt 𝓘(ℝ,ℂ) x = extChartAt 𝓘(ℂ) x` is **`rfl`**, both as `PartialEquiv X ℂ` and at
   the function level. (`extChartAt I x = (chartAt ℂ x).extend I` and the two `I`s contribute
   the same `PartialEquiv.refl ℂ`.) The blueprint's ⚠ is settled: no transport lemma is ever
   needed; the same chart data serves both models.
2. `writtenInExtChartAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) x f = writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f` is **`rfl`**
   (consumed by dbar-solvability).
3. `(TangentSpace 𝓘(ℝ,ℂ) x : Type) = (TangentSpace 𝓘(ℂ) x : Type)` is **`rfl`** (both reduce
   to `ℂ`). The *module structures* over ℝ vs ℂ still differ — that diamond is the dbar unit's
   declared problem, not ours; we only pin the type-level fact.
4. `IsManifold 𝓘(ℝ,ℂ) ω X` is **derivable in ~10 lines** from `IsManifold 𝓘(ℂ) ω X` via
   `isManifold_of_contDiffOn` (`Geometry/Manifold/IsManifold/Basic.lean:799`): each transition
   `e.symm ≫ₕ e'` is `ContDiffOn ℂ ω` (from `StructureGroupoid.compatible` +
   `mem_groupoid_of_pregroupoid`), hence `AnalyticOn ℝ` by
   `contDiffOn_omega_iff_analyticOn` (`Analysis/Calculus/ContDiff/Defs.lean:763`, needs
   `IsOpen.uniqueDiffOn`) + `AnalyticOn.restrictScalars`
   (`Analysis/Analytic/Constructions.lean:758`), hence `ContDiffOn ℝ ω`.
5. From the ω instance, `IsManifold 𝓘(ℝ,ℂ) a X` for **every** `a : ℕ∞ω` (in particular `∞` and
   any finite `n`) is found by instance search, via mathlib's
   `instance [IsManifold I ω M] : IsManifold I a M` (`IsManifold/Basic.lean:856`). **[spiked]**
   for `∞` and `2`.
6. With that instance, `SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,ℂ)` applies on `X`
   assuming only `[T2Space X] [CompactSpace X]` **[spiked]**: `SigmaCompactSpace X` comes from
   the instance `CompactSpace.sigmaCompact` (`Topology/Compactness/SigmaCompact.lean:179`),
   `FiniteDimensional ℝ ℂ` is a mathlib instance, and `IsManifold 𝓘(ℝ,ℂ) ∞ X` from (5).

The instance in (4) is declared with `priority := 100` so that on `X := ℂ` itself mathlib's
`instIsManifoldModelSpace` wins the (harmless, Prop-valued) overlap.

---

## 2. File plan (build order)

| # | File | Content | Est. lines | Imports (beyond earlier files) |
|---|------|---------|-----------|--------------------------------|
| 1 | `Jacobian/Surface/Bridges.lean` | ContMDiff ↔ chart-local analyticity/ContDiff bridges over 𝓘(ℂ) | ~200 | `Mathlib.Geometry.Manifold.ContMDiff.Atlas`, `Mathlib.Geometry.Manifold.ContMDiff.NormedSpace`, `Mathlib.Analysis.Complex.Basic` |
| 2 | `Jacobian/Surface/RealSmooth.lean` | CC7: `IsManifold 𝓘(ℝ,ℂ)` instance, `rfl` chart facts, ℝ-bridges, holomorphic ⇒ real-smooth, PoU corollary | ~150 | `Mathlib.Analysis.Analytic.Constructions`, `Mathlib.Geometry.Manifold.PartitionOfUnity` |
| 3 | `Jacobian/Surface/ChartedSpaceKit.lean` | toolkit: `ChartedSpace ℂ Z` + `IsManifold 𝓘(ℂ) ω Z` from a compatible chart family | ~100 | `Mathlib.Geometry.Manifold.IsManifold.Basic` (also usable standalone) |
| 4 | `Jacobian/Surface/Identity.lean` | identity theorem, isolated fibers, open mapping, surjectivity | ~250 | `Mathlib.Analysis.Analytic.IsolatedZeros`, `Mathlib.Analysis.Complex.OpenMapping` |
| 5 | `Jacobian/Surface/InverseFunction.lean` | holomorphic IFT on surfaces, mfderiv variant, `map_nhds_eq` | ~250 | `Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic`, `Mathlib.Geometry.Manifold.MFDeriv.Basic` |
| 6 | `Jacobian/Surface.lean` | unit root: imports 1–5, API-summary module docstring | ~30 | — |

Dependencies among files: 2, 4, 5 import 1; 3 is independent; 6 imports all.
Files 4 and 5 are mutually independent (either order).

---

## 3. Exported signatures

### 3.1 `Bridges.lean`

```lean
namespace RS

/-- `C^n` at `x` for `f : X → ℂ` is exactly `C^n` of the chart composite. [spiked at n = ω and,
over ℝ, at general n; same proof shape] -/
theorem contMDiffAt_iff_contDiffAt_extChartAt {f : X → ℂ} {x : X} :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) n f x ↔
      ContDiffAt ℂ n (f ∘ (extChartAt 𝓘(ℂ) x).symm) (extChartAt 𝓘(ℂ) x x)

/-- Holomorphy at `x` for `f : X → ℂ` is analyticity of the chart composite. [spiked, compiles
with full proof] -/
theorem contMDiffAt_iff_analyticAt {f : X → ℂ} {x : X} :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x ↔
      AnalyticAt ℂ (f ∘ (extChartAt 𝓘(ℂ) x).symm) (extChartAt 𝓘(ℂ) x x)

/-- Two-chart version, `f : X → Y`. `ContinuousAt` cannot be dropped on the ← side (the chart
composite does not see `f` outside the chart sources). -/
theorem contMDiffAt_iff_contDiffAt_writtenInExtChartAt {f : X → Y} {x : X} :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) n f x ↔
      ContinuousAt f x ∧
        ContDiffAt ℂ n (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f) (extChartAt 𝓘(ℂ) x x)

theorem contMDiffAt_iff_analyticAt_writtenInExtChartAt {f : X → Y} {x : X} :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x ↔
      ContinuousAt f x ∧
        AnalyticAt ℂ (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f) (extChartAt 𝓘(ℂ) x x)

/-- Analyticity may be read in ANY atlas chart whose source contains `x` (chart-invariance;
the workhorse for CC3/CC4-style definitions and for `coeffIn`). -/
theorem contMDiffAt_iff_analyticAt_of_mem_source {f : X → ℂ} {x : X}
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ atlas ℂ X) (hx : x ∈ e.source) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x ↔ AnalyticAt ℂ (f ∘ e.symm) (e x)

/-- Set version on a chart source. -/
theorem contMDiffOn_iff_analyticOnNhd_of_subset_source {f : X → ℂ} {s : Set X}
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ atlas ℂ X) (hs : s ⊆ e.source)
    (hso : IsOpen s) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f s ↔ AnalyticOnNhd ℂ (f ∘ e.symm) (e '' s)

end RS
```

What mathlib already gives (cited, not re-proved): `contMDiffAt_iff`
(`ContMDiff/Defs.lean:181`, chart composite as `ContDiffWithinAt … (range I)`),
`contMDiffAt_iff_of_mem_source` (`:426`), `contMDiffOn_iff_of_mem_maximalAtlas` (`:435`),
`contMDiffAt_iff_contDiffAt` (`ContMDiff/NormedSpace.lean:54`, both spaces = model),
`contMDiffAt_extChartAt` / `contMDiffOn_extChartAt_symm` / `contMDiffOn_chart` /
`contMDiffOn_chart_symm` (`ContMDiff/Atlas.lean:102/:118/:83/:86`),
`ContDiffAt.analyticAt` / `AnalyticAt.contDiffAt` (`ContDiff/Defs.lean:968/:976`). Our wrappers
are thin: they eliminate `range 𝓘(ℂ) = univ` and the trivial target chart once and for all, so
no downstream unit ever touches `ContDiffWithinAt`-over-`range I` again.

### 3.2 `RealSmooth.lean` (CC7)

```lean
namespace RS

/-- CC7. A holomorphic atlas is ℝ-analytically compatible. Priority below the model-space
instance so `X := ℂ` resolves to mathlib's instance first. [spiked, compiles] -/
instance (priority := 100) isManifoldRealOfComplex : IsManifold 𝓘(ℝ, ℂ) ω X

-- `IsManifold 𝓘(ℝ, ℂ) ∞ X`, `IsManifold 𝓘(ℝ, ℂ) n X` need NO declaration: instance search
-- derives them from ω (IsManifold/Basic.lean:856). [spiked]

/-- CC7 pinned fact; `rfl`. [spiked] -/
theorem extChartAt_real_eq (x : X) : extChartAt 𝓘(ℝ, ℂ) x = extChartAt 𝓘(ℂ) x := rfl

/-- Function-level variant; `rfl`. [spiked] -/
theorem coe_extChartAt_real_eq (x : X) :
    (extChartAt 𝓘(ℝ, ℂ) x : X → ℂ) = extChartAt 𝓘(ℂ) x := rfl

/-- `rfl`; consumed by dbar-solvability. [spiked] -/
theorem writtenInExtChartAt_real_eq {f : X → Y} (x : X) :
    writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) x f = writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f := rfl

/-- ℝ-smoothness bridge in the (shared) charts. [spiked, compiles with full proof] -/
theorem contMDiffAt_real_iff_contDiffAt {f : X → ℂ} {x : X} :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n f x ↔
      ContDiffAt ℝ n (f ∘ (extChartAt 𝓘(ℂ) x).symm) (extChartAt 𝓘(ℂ) x x)

theorem contMDiffAt_real_iff_contDiffAt_writtenInExtChartAt {f : X → Y} {x : X} :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n f x ↔
      ContinuousAt f x ∧
        ContDiffAt ℝ n (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f) (extChartAt 𝓘(ℂ) x x)

/-- Holomorphic ⇒ real-C^n, pointwise (n arbitrary, incl. ω and ∞). Covers `Y := ℂ`. -/
theorem contMDiffAt_real_of_holomorphicAt {f : X → Y} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n f x

/-- Holomorphic ⇒ real-C^n, global. -/
theorem contMDiff_real_of_holomorphic {f : X → Y}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n f

/-- On an open set. -/
theorem contMDiffOn_real_of_holomorphicOn {f : X → Y} {s : Set X} (hs : IsOpen s)
    (hf : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f s) : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n f s

/-- PoU availability, restated on our surface as a compile-time guarantee. [spiked] -/
theorem exists_smoothPartitionOfUnity [T2Space X] [CompactSpace X] {ι : Type*}
    (U : ι → Set X) (ho : ∀ i, IsOpen (U i)) (hU : (univ : Set X) ⊆ ⋃ i, U i) :
    ∃ p : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) X univ, p.IsSubordinate U

end RS
```

### 3.3 `ChartedSpaceKit.lean` (toolkit for ℙ¹ and the torus)

Mathlib inventory for this problem: `ChartedSpace` is a plain structure (`ChartedSpace.lean:139`)
— constructing an instance from a family is trivial once the charts are
`OpenPartialHomeomorph Z ℂ`; `ChartedSpaceCore` (`ChartedSpace.lean:606`) exists for the case
where the *topology* must be generated from the charts (not needed for `OnePoint ℂ` or `E ⧸ Λ`,
which have topologies; noted as available, not wrapped). For the manifold structure the
constructor is `isManifold_of_contDiffOn` (`IsManifold/Basic.lean:799`), fed through
`hasGroupoid_of_pregroupoid` (`HasGroupoid.lean:55`); single-chart spaces can instead use
`Topology.IsOpenEmbedding.isManifold_singleton` (`IsManifold/Basic.lean:1008`) /
`OpenPartialHomeomorph.isManifold_singleton` (`:1000`) — insufficient for two-chart ℙ¹,
hence this kit.

```lean
namespace RS

variable {Z : Type*} [TopologicalSpace Z] {ι : Type*}

/-- Package a covering family of ℂ-charts as a `ChartedSpace`. -/
def chartedSpaceOfFamily (c : ι → OpenPartialHomeomorph Z ℂ) (idx : Z → ι)
    (h : ∀ z, z ∈ (c (idx z)).source) : ChartedSpace ℂ Z where
  atlas := Set.range c
  chartAt z := c (idx z)
  mem_chart_source := h
  chart_mem_atlas z := Set.mem_range_self _

@[simp] theorem chartedSpaceOfFamily_chartAt (c : ι → OpenPartialHomeomorph Z ℂ)
    (idx : Z → ι) (h : ∀ z, z ∈ (c (idx z)).source) (z : Z) :
    @chartAt ℂ _ Z _ (chartedSpaceOfFamily c idx h) z = c (idx z) := rfl

@[simp] theorem chartedSpaceOfFamily_atlas (c : ι → OpenPartialHomeomorph Z ℂ)
    (idx : Z → ι) (h : ∀ z, z ∈ (c (idx z)).source) :
    @atlas ℂ _ Z _ (chartedSpaceOfFamily c idx h) = Set.range c := rfl

/-- An atlas with ℂ-analytic transitions is an `ω`-manifold. [spiked, compiles with proof] -/
theorem isManifold_of_analyticOn_transitions [ChartedSpace ℂ Z]
    (h : ∀ e ∈ atlas ℂ Z, ∀ e' ∈ atlas ℂ Z,
      AnalyticOnNhd ℂ (e.symm ≫ₕ e') (e.symm ≫ₕ e').source) :
    IsManifold 𝓘(ℂ) ω Z

/-- Family version: pairwise-analytic transitions of the generating family suffice. -/
theorem isManifold_of_family (c : ι → OpenPartialHomeomorph Z ℂ) (idx : Z → ι)
    (h : ∀ z, z ∈ (c (idx z)).source)
    (htrans : ∀ i j, AnalyticOnNhd ℂ ((c i).symm ≫ₕ c j) ((c i).symm ≫ₕ c j).source) :
    @IsManifold ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ) ω Z _ (chartedSpaceOfFamily c idx h)

end RS
```

Usage (projective-line, CC5): `instance : ChartedSpace ℂ (OnePoint ℂ) := chartedSpaceOfFamily ![e₀, e∞] …` then `instance : IsManifold 𝓘(ℂ) ω (OnePoint ℂ) := isManifold_of_family …` with the single nontrivial transition `z ↦ 1/z` analytic on `ℂ \ {0}`. The torus unit (CC9) uses the same kit with quotient charts.

### 3.4 `Identity.lean`

```lean
namespace RS

/-- Local dichotomy at a point (no connectedness, no T2): locally constant value or isolated
in its fiber. -/
theorem eventually_eq_const_or_eventually_ne {f : X → Y} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) :
    (∀ᶠ z in 𝓝 x, f z = f x) ∨ (∀ᶠ z in 𝓝[≠] x, f z ≠ f x)

variable [T2Space Y]   -- ℂ qualifies, so all lemmas apply to f g : X → ℂ

/-- **Identity theorem** on a connected surface: holomorphic maps agreeing frequently near a
point (equivalently: on a set accumulating at a point) are equal. Route: chart-local
`AnalyticAt.frequently_eq_iff_eventually_eq` + clopen argument. -/
theorem eq_of_frequently_eq [PreconnectedSpace X] {f g : X → Y}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) {z₀ : X}
    (hfg : ∃ᶠ z in 𝓝[≠] z₀, f z = g z) : f = g

/-- Accumulation-set formulation (the one meromorphic-and-divisors quotes for `div` support). -/
theorem eq_of_eqOn_of_accPt [PreconnectedSpace X] {f g : X → Y}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    {s : Set X} {z₀ : X} (hz₀ : AccPt z₀ (𝓟 s)) (heq : EqOn f g s) : f = g

/-- Nonconstant holomorphic maps have **isolated fibers**. -/
theorem eventually_ne_of_not_const [PreconnectedSpace X] {f : X → Y}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hne : ¬ ∃ y, ∀ x, f x = y) (x : X) :
    ∀ᶠ z in 𝓝[≠] x, f z ≠ f x

/-- Nonconstant holomorphic maps are **open** (Forster 2.4 on surfaces). -/
theorem isOpenMap_of_not_const [PreconnectedSpace X] {f : X → Y}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hne : ¬ ∃ y, ∀ x, f x = y) : IsOpenMap f

/-- Forster 2.7: nonconstant + compact source + connected target ⇒ surjective (and the target
is then compact). Consumed by mapping-degree and the headline. -/
theorem surjective_of_not_const [ConnectedSpace X] [CompactSpace X] [PreconnectedSpace Y]
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hne : ¬ ∃ y, ∀ x, f x = y) :
    Function.Surjective f

end RS
```

(Mathlib's `Geometry/Manifold/Complex.lean` was checked first, per the inventory: it has the
manifold maximum principle and `MDifferentiable.isLocallyConstant`/`apply_eq_of_compactSpace`
for maps into a normed space `F` on compact `M` — useful elsewhere, but it contains **no**
identity theorem, no open mapping, no surface-to-surface statement; everything above is new.)

### 3.5 `InverseFunction.lean`

Mathlib's planar analytic IFT (all verified in source, **[spiked]** that the pieces compose):

- `HasStrictFDerivAt.toOpenPartialHomeomorph (hf : HasStrictFDerivAt f (f' : E ≃L[𝕜] F) a) :
  OpenPartialHomeomorph E F` — `InverseFunctionTheorem/FDeriv.lean:114`, with
  `toOpenPartialHomeomorph_coe` (`:126`, `⇑… = f`), `mem_toOpenPartialHomeomorph_source`
  (`:130`), `image_mem_toOpenPartialHomeomorph_target` (`:134`), `localInverse` (`:146`),
  `eventually_left_inverse` (`:155`), `eventually_right_inverse` (`:164`),
  `to_localInverse` (`:183`).
- 1-D packaging: `HasStrictDerivAt.localInverse`, `.hasStrictFDerivAt_equiv`,
  `.map_nhds_eq`, `.to_localInverse` — `InverseFunctionTheorem/Deriv.lean:33/:44/:47`.
- `AnalyticAt.hasStrictDerivAt` — `Analysis/Calculus/FDeriv/Analytic.lean:147`.
- **Analyticity of the local inverse**: `AnalyticAt.analyticAt_localInverse
  (hf : AnalyticAt 𝕜 f x) (hf' : deriv f x ≠ 0) :
  AnalyticAt 𝕜 (hf.hasStrictDerivAt.localInverse _ _ _ hf') (f x)` —
  `InverseFunctionTheorem/Analytic.lean:26` (via `OpenPartialHomeomorph.hasFPowerSeriesAt_symm`,
  `Analysis/Analytic/Inverse.lean:657`). Also `analyticAt_comp_iff_of_deriv_ne_zero` (`:40`).

The manifold wrapper (statement **[spiked]**, elaborates against the pin):

```lean
namespace RS

/-- **Holomorphic inverse function theorem on surfaces.** If `f` is holomorphic at `x` with
nonvanishing chart-derivative, there is a partial homeomorphism around `x` agreeing with `f`
that is holomorphic with holomorphic inverse. -/
theorem exists_openPartialHomeomorph_of_deriv_ne_zero {f : X → Y} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x)
    (hf' : deriv (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f) (extChartAt 𝓘(ℂ) x x) ≠ 0) :
    ∃ e : OpenPartialHomeomorph X Y, x ∈ e.source ∧ EqOn f e e.source ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω e e.source ∧ ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω e.symm e.target

/-- The chart-free (invariant) form of the hypothesis. -/
theorem mfderiv_ne_zero_iff_deriv_ne_zero {f : X → Y} {x : X}
    (hf : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) f x ≠ 0 ↔
      deriv (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f) (extChartAt 𝓘(ℂ) x x) ≠ 0

/-- IFT keyed on `mfderiv` (invariant interface for mapping-degree). -/
theorem exists_openPartialHomeomorph_of_mfderiv_ne_zero {f : X → Y} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) (hf' : mfderiv 𝓘(ℂ) 𝓘(ℂ) f x ≠ 0) :
    ∃ e : OpenPartialHomeomorph X Y, x ∈ e.source ∧ EqOn f e e.source ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω e e.source ∧ ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω e.symm e.target

/-- Local-homeomorphism consequence: `f` maps neighborhoods onto neighborhoods. -/
theorem map_nhds_eq_of_deriv_ne_zero {f : X → Y} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x)
    (hf' : deriv (writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f) (extChartAt 𝓘(ℂ) x x) ≠ 0) :
    Filter.map f (𝓝 x) = 𝓝 (f x)

end RS
```

---

## 4. Proof plans (nontrivial items)

**P1. `isManifoldRealOfComplex`** — done, see §1(4); the compiled proof is in the spike
(11 lines). Same skeleton proves `isManifold_of_analyticOn_transitions` (compiled, 6 lines).

**P2. Bridges (`contMDiffAt_iff_analyticAt`, both directions)** — compiled in spike:
(→) compose `hf` with the holomorphic chart inverse:
`(contMDiffOn_extChartAt_symm x).contMDiffAt (extChartAt_target_mem_nhds x)` (boundaryless), via
`ContMDiffAt.comp_of_eq … (extChartAt_to_inv x)`; land in `contMDiffAt_iff_contDiffAt`, finish
with `ContDiffAt.analyticAt`. (←) `AnalyticAt.contDiffAt`, `contMDiffAt_iff_contDiffAt.2`,
compose with `contMDiffAt_extChartAt`, then `ContMDiffAt.congr_of_eventuallyEq` using
`extChartAt_source_mem_nhds` + `(chartAt ℂ x).left_inv` (after `rw [extChartAt_source]`).
The two-chart `X → Y` versions instead rewrite `contMDiffAt_iff` (`Defs.lean:181`) directly:
`range 𝓘(ℂ) = univ` (`modelWithCornersSelf_coe`, `Set.range_id`), `contDiffWithinAt_univ`,
`ContDiffAt ℂ ω ↔ AnalyticAt` as above; the `ContinuousAt` conjunct is `contMDiffAt_iff`'s own.

**P3. `contMDiffAt_iff_analyticAt_of_mem_source`** — Forster §1 chart compatibility. Both `e`
and `chartAt ℂ x` are in the (ω-maximal) atlas; `StructureGroupoid.compatible_of_mem_maximalAtlas`
(`HasGroupoid.lean:110`) makes the transition `τ = (chartAt ℂ x).symm ≫ₕ e` a member of
`contDiffGroupoid ω 𝓘(ℂ)`, i.e. analytic with analytic inverse on its open source. Then
`f ∘ e.symm = (f ∘ (chartAt ℂ x).symm) ∘ τ.symm` near `e x`, and `AnalyticAt.comp` +
`AnalyticAt.congr` transport analyticity through τ in both directions. 10–20 lines.

**P4. Identity theorem `eq_of_frequently_eq`** (Forster 1.11-adjacent; planar input
`AnalyticAt.frequently_eq_iff_eventually_eq`, `Analysis/Analytic/IsolatedZeros.lean:141`).
Let `S := {x | f =ᶠ[𝓝 x] g}`. (i) `S` is open by definition of germ-equality.
(ii) `S` is closed: let `x ∈ closure S`. Frequent equality of `f, g` near `x` (points of `S`
arbitrarily close to `x`, minus the trivial case `x ∈ S`) plus continuity plus `[T2Space Y]`
gives `f x = g x` via `tendsto_nhds_unique_of_frequently_eq`
(`Topology/Separation/Hausdorff.lean:191`). Now read both maps in `chartAt ℂ x` /
`chartAt ℂ (f x)` (Bridges, `contMDiffAt_iff_analyticAt_writtenInExtChartAt`): the two
composites are `AnalyticAt ℂ` at `extChartAt 𝓘(ℂ) x x` and agree frequently in the punctured
neighborhood (the chart is a homeomorphism on its source, so frequency transports); by
`frequently_eq_iff_eventually_eq` they agree eventually, and pulling back through the chart
(`left_inv`) gives `f =ᶠ[𝓝 x] g`, i.e. `x ∈ S`. (iii) `z₀ ∈ S` by the same chart-local
argument applied to the hypothesis. (iv) `isClopen_iff` (`Topology/Connected/Clopen.lean:114`,
`[PreconnectedSpace X]`) forces `S = univ`; `f = g` follows pointwise (`funext`, each `x ∈ S`).
`eq_of_eqOn_of_accPt` = `accPt_iff_frequently_nhdsNE` (`Topology/ClusterPt.lean:217`) +
`eq_of_frequently_eq`.

**P5. Isolated fibers & dichotomy** — `eventually_eq_const_or_eventually_ne`: apply
`AnalyticAt.eventually_eq_or_eventually_ne` (`IsolatedZeros.lean:132`) to the chart composite
and `analyticAt_const` (constant `extChartAt 𝓘(ℂ) (f x) (f x)`); transport both branches back
through the source chart; injectivity of `extChartAt 𝓘(ℂ) (f x)` on its source converts
composite-inequality to `f z ≠ f x` (continuity keeps `f z` in the chart source).
`eventually_ne_of_not_const`: if the first branch held at some `x`, then `f =ᶠ[𝓝 x] const (f x)`,
so `eq_of_frequently_eq` (with `g := const`, holomorphic by `contMDiff_const`) makes `f`
globally constant — contradiction. 
**P6. Open mapping** — at each `x`, `AnalyticAt.eventually_constant_or_nhds_le_map_nhds`
(`Analysis/Complex/OpenMapping.lean:119`) on the composite; the constant branch is killed by P5;
in the open branch, conjugate filters: `𝓝 (f x) = map (extChartAt 𝓘(ℂ) (f x)).symm (𝓝 (…))`
(charts are `OpenPartialHomeomorph`s: `OpenPartialHomeomorph.map_nhds_eq`), then
`Filter.map_congr` with `f =ᶠ λ.symm ∘ g ∘ κ` near `x`; conclude with `isOpenMap_iff_nhds_le`
(`Topology/Maps/Basic.lean:480`). Surjectivity: image open (P6) + compact-closed (T2) +
nonempty, clopen-in-preconnected ⇒ `range f = univ`.

**P7. Holomorphic IFT `exists_openPartialHomeomorph_of_deriv_ne_zero`** (Forster 2.1/2.5 local
part; standard complex IFT). Write `κ := extChartAt 𝓘(ℂ) x`, `λ := extChartAt 𝓘(ℂ) (f x)`,
`g := writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f`. (1) Bridges: `AnalyticAt ℂ g (κ x)`; with `hf'`,
`R := (hg.hasStrictDerivAt.hasStrictFDerivAt_equiv hf').toOpenPartialHomeomorph g :
OpenPartialHomeomorph ℂ ℂ` has `κ x ∈ R.source`, `⇑R = g`, and `R.symm` is `AnalyticAt` at
`g (κ x)` (`analyticAt_localInverse` + `localInverse` = `R.symm` by `localInverse_def` /
`eventually_left_inverse` uniqueness). (2) By `AnalyticAt.eventually_analyticAt`
(`Analysis/Analytic/ChangeOrigin.lean:377`) pick an open `V ∋ g (κ x)`, `V ⊆ R.target`, with
`R.symm` analytic on `V` and `λ.symm` defined (`V ⊆ λ.target ∩ …`). (3) Assemble
`e₀ := (chartAt ℂ x) ≫ₕ (R.restr (κ.source-image ∩ R ⁻¹' V region)) ≫ₕ (chartAt ℂ (f x)).symm`
(`OpenPartialHomeomorph.trans`, `.restr`, `.symm`); `x ∈ e₀.source` by construction, all
sources/targets open. (4) `EqOn f e₀ e₀.source`: for `z ∈ e₀.source`,
`e₀ z = λ.symm (g (κ z)) = λ.symm (λ (f z)) = f z` using `g ∘ κ = λ ∘ f` on `κ.source ∩ f ⁻¹' λ.source`
and `λ.left_inv` — the source shrinking in (3) guarantees membership. (5) Holomorphy of `e₀` on
source: from `hf` + `EqOn` (`ContMDiffOn.congr`); of `e₀.symm = chartAt (f x) ≫ₕ R.symm ≫ₕ chart x .symm`
on target: Bridges (←) with analyticity of `R.symm` on `V`, `contMDiffOn_chart`,
`contMDiffOn_chart_symm`, `ContMDiffOn.comp`. ~120–180 lines; the only genuinely fiddly parts
are the `source`-bookkeeping intersections in (3)–(4).

**P8. `mfderiv_ne_zero_iff_deriv_ne_zero`** — `mfderiv` unfolds (`MFDeriv/Defs.lean`, under
`MDifferentiableAt`) to `fderivWithin ℂ (writtenInExtChartAt …) (range 𝓘(ℂ)) (κ x)`;
`range 𝓘(ℂ) = univ` + `fderivWithin_univ` + `fderiv_deriv`-style `ContinuousLinearMap.smulRight`
translation (`deriv g z ≠ 0 ↔ fderiv ℂ g z ≠ 0` since a 1-D CLM is zero iff its `1`-value is).
`map_nhds_eq_of_deriv_ne_zero`: from the IFT `e` via `OpenPartialHomeomorph.map_nhds_eq` +
`Filter.map_congr` (or directly `HasStrictDerivAt.map_nhds_eq` in charts).

---

## 5. Spike results (compiled reality)

`scratch_surfaces.lean` (gitignored), pinned toolchain `v4.30.0-rc2`, prebuilt mathlib oleans;
command `lake env lean scratch_surfaces.lean`. Two spike configurations were run:

**Spike 1** (imports: `Geometry.Manifold.ContMDiff.Atlas`, `Geometry.Manifold.ContMDiff.NormedSpace`,
`Analysis.Analytic.Constructions`, `Analysis.Complex.Basic`) — **compiles clean, 5.9 s wall**
(≈4.5 s user; ≈6 s is the import-load floor for any manifold file on this machine):
- `extChartAt 𝓘(ℝ,ℂ) x = extChartAt 𝓘(ℂ) x := rfl` ✓ (PartialEquiv and function level);
- `instance : IsManifold 𝓘(ℝ,ℂ) ω X` full proof ✓ (11 lines, route of §1(4));
- `IsManifold 𝓘(ℝ,ℂ) ∞ X` and `IsManifold 𝓘(ℝ,ℂ) 2 X` by `inferInstance` ✓;
- `contMDiffAt_iff_analyticAt` (f : X → ℂ, ω, both directions) full proof ✓;
- ℝ-side bridge at generic `n : WithTop ℕ∞` full proof ✓.
  Gotcha found: the final congruence must rewrite `extChartAt_source` and use
  `(chartAt ℂ x).left_inv` (the goal surfaces in `chartAt` form, not `extChartAt` form).

**Spike 2** (imports: `Geometry.Manifold.PartitionOfUnity`,
`Analysis.Calculus.InverseFunctionTheorem.Analytic`) — **compiles, 6.1–6.6 s wall**, one
intentional `sorry` (the IFT wrapper *statement* elaborates; proof is the unit's work):
- `isManifold_of_analyticOn_transitions` full proof ✓ (6 lines);
- planar IFT ingredients exist and compose with the exact names of §3.5 ✓
  (`toOpenPartialHomeomorph` is `noncomputable`);
- IFT wrapper statement elaborates ✓;
- `writtenInExtChartAt` two-model equality `rfl` ✓; `TangentSpace` type-level equality `rfl` ✓;
- `SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,ℂ)` on `X` with only
  `[T2Space X] [CompactSpace X]` extra ✓.

Import-footprint note: `Analysis.Complex.Basic` (or anything transitively providing the normed
instances on ℂ) is required — the manifold imports alone leave `NormedAddCommGroup ℂ`
unsynthesized. `Geometry.Manifold.PartitionOfUnity` and
`InverseFunctionTheorem.Analytic` add no measurable compile-time over the floor.

---

## 6. Risks & fallbacks

1. **Instance overlap on `X := ℂ`** — `isManifoldRealOfComplex` also fires for `ℂ` itself,
   overlapping `instIsManifoldModelSpace`. Prop-valued, so at worst a search-order effect;
   mitigated with `priority := 100`. Watched during the unit's `#synth` smoke tests.
   Fallback: demote to a `theorem` + explicit `haveI` at use sites (PoU units would then write
   one `haveI` line each).
2. **IFT source-bookkeeping (P7 step 3–4)** — `OpenPartialHomeomorph.trans/restr` source
   algebra is verbose. Fallback: build `e` directly by the `OpenPartialHomeomorph` constructor
   on explicitly chosen open sets `U := κ.symm '' W`, `f '' U`, proving the six fields by hand;
   or weaken the conclusion to the `∃ U ∈ 𝓝 x, …`-with-local-inverse-function form that
   mapping-degree can also consume. The *statement* is frozen only up to providing: a
   neighborhood of `x`, agreement with `f`, holomorphic two-sided inverse data.
3. **`mfderiv` variant friction** (P8) — `fderivWithin`/`range`/`smulRight` normalization may
   fight. Fallback: drop `exists_openPartialHomeomorph_of_mfderiv_ne_zero` to a corollary in
   mapping-degree; the chart-derivative primary form (spiked) is self-sufficient downstream.
4. **Frequency transport through charts** (P4/P5) — moving `∃ᶠ z in 𝓝[≠] x` across
   `extChartAt` needs `map_extChartAt_nhdsWithin`-style lemmas on punctured neighborhoods;
   mathlib has `OpenPartialHomeomorph.map_nhds_eq` and `nhdsWithin` images but possibly not the
   exact punctured version. Fallback: hand-roll via
   `Filter.map (κ) (𝓝[≠] x) = 𝓝[≠] (κ x)` proved from `map_nhds_eq` + injectivity on source
   (5–10 lines, self-contained).
5. **`n`-generic bridges** — instances `IsManifold 𝓘(ℂ) n X` for arbitrary `n` are derived
   from ω by mathlib's instance; if elaboration stalls at a *variable* `n`, specialize the
   generic-`n` bridge statements to the three used levels (`ω`, `∞`, finite) — downstream only
   ever uses those.
6. **Model-space `Y := ℂ` instantiation quirks** — `chartAt ℂ (z : ℂ) = refl` needs
   `chartAt_self_eq`/`extChartAt_self_eq` simp steps at use sites; the `X → ℂ` special-case
   lemmas in Bridges exist precisely so downstream never re-derives this.

## 7. What downstream units consume (interface contract)

- **local-multiplicity**: `Bridges` (chart-local analyticity ↔ `ContMDiffAt`, chart-invariance
  `contMDiffAt_iff_analyticAt_of_mem_source`) for the `z^k·unit` normal form's well-posedness.
- **mapping-degree**: the IFT (`exists_openPartialHomeomorph_of_*`, `map_nhds_eq_…`) as the
  substrate for local normal forms and sheet counting; `Identity` (`eventually_ne_of_not_const`
  = isolated fibers, `isOpenMap_of_not_const`, `surjective_of_not_const`) for fibre finiteness
  and the clopen degree argument.
- **holomorphic-forms (CC1)**: `Bridges` (`coeffIn` analyticity transfer,
  `contMDiffOn_iff_analyticOnNhd_of_subset_source`); the CC7 instance for any real-smooth
  section arguments.
- **projective-line (CC5)** and **jacobian-construction (CC9)**: `ChartedSpaceKit`
  (`chartedSpaceOfFamily`, `isManifold_of_family`, `isManifold_of_analyticOn_transitions`).
- **dbar-solvability / dolbeault-comparison / residue-theorem / planar-stokes (PoU users)**:
  `IsManifold 𝓘(ℝ,ℂ) ∞ X` (automatic from the instance), `exists_smoothPartitionOfUnity`
  (verified: needs only `[T2Space X] [CompactSpace X]`), `contMDiff_real_of_holomorphic`,
  and the `rfl` facts `extChartAt_real_eq` / `writtenInExtChartAt_real_eq` (their charts are
  *literally* ours; no transport).
- **meromorphic-and-divisors (CC3)**: `eq_of_eqOn_of_accPt` (finite divisor support on compact
  `X`), `Bridges` for `MeromorphicAtX` chart-invariance.
- **genus-zero-headline**: `surjective_of_not_const` and the IFT via proper-map-degree.

Freeze policy: the six files' exported names and statement shapes above are the unit's
interface; conclusions of the IFT may be strengthened (extra conjuncts) but not weakened
without orchestrator sign-off (risk 2's fallback is the sole sanctioned reshape).
