# Design: mapping-degree (`Jacobian/MappingDegree/`)

Blueprint unit **mapping-degree** (largest unit). **Builds on:** surfaces-and-charts,
local-multiplicity — both are being built concurrently; this doc designs against their design
docs (`docs/design/surfaces-and-charts.md`, `docs/design/local-multiplicity.md`); where the
actual builds deviate, the builder of THIS unit adapts (risk §8.1). References: Forster §4
(book 20–31 = PDF 26–37, esp. Thm 4.24 book 29 = PDF 35), §2 (Thm 2.1); Miranda Ch. II
(multiplicity, degree). Mathlib facts cited by `file:line` were **read in the pinned source**
(`548398201`); those marked **[spiked]** also compiled in `scratch_mapdeg.lean` (§10).

## 0. Route (the key decisions)

**Deliverable:** for nonconstant holomorphic `F : X → Y` between compact connected Riemann
surfaces: `F` surjective/open/finite-fibered; ramification and branch loci FINITE; a degree
`RS.degree F : ℕ` = total multiplicity `∑_{x ∈ F⁻¹(y)} multiplicity F x` over **any** `y`
(the core well-definedness theorem); fiber cardinality = degree over regular values; regular
values cofinite and dense; `IsCoveringMapOn F (branchLocus F)ᶜ`; degree 1 ⇒ bijective ⇒
homeomorphism; degree of composition = product. `ContMDiff.degree` (challenge API) will be the
one-line wrapper `RS.degree F` in final assembly — our `degree` is junk-0 on constants by
construction, so the wrapper is trivial.

1. **No covering-space detour for well-definedness.** Forster proves 4.24 by first making
   `F` an unbranched covering over `Y ∖ B` (4.22), counting sheets there, then patching
   multiplicities across `B` — this needs connectedness of `Y ∖ B` (a finite set removed).
   We instead prove directly: **the total-multiplicity function
   `fiberMultSum F : Y → ℕ`, `y ↦ ∑_{x∈F⁻¹(y)} multiplicity F x`, is locally constant on all
   of `Y`** (including at branch values), via the "stack of adapted charts" at an arbitrary
   fiber (Forster's own 4.24-proof mechanism, upgraded to count WITH multiplicity in every
   chart so no case split between branched/unbranched neighborhoods is needed). Then
   `IsLocallyConstant.apply_eq_of_preconnectedSpace` finishes. Path-connectedness of
   `Y ∖ (finite set)` is never used anywhere in the unit.
2. **The fiber-trapping step is filter-algebra, not sequences.** "For `y` near `y₀`,
   `F⁻¹(y) ⊆ ⋃ chart sources" is proved by: `F` is a closed map (compact source, T2 target,
   `Continuous.isClosedMap`), and closed maps satisfy `comap F (𝓝 y₀) ≤ 𝓝ˢ (F⁻¹{y₀})`
   (`IsClosedMap.comap_nhds_le`); the union of sources is a `𝓝ˢ`-neighborhood of the fiber.
   No sequential compactness, no first-countability.
3. **The per-chart count is one planar identity**: total multiplicity of `z ↦ z^k` over any
   `w ∈ ℂ` is `k` (roots of `z^k = w`: one root of order `k` when `w = 0`; `k` simple roots
   otherwise, all trapped in the chart ball since `|root|^k = |w|`). Packaged as a single
   finsum identity so the surface-level proof needs no `w = 0` case split.
4. **Covering structure is free from mathlib**: the pin has
   `IsCoveringMapOn.of_openPartialHomeomorph` (`Topology/Covering/Basic.lean:580`) — exactly
   "compact T2 source + local-homeo at every point of the fiber ⇒ evenly covered". We supply
   local homeomorphisms from multiplicity-1 points (local-multiplicity's Forster 2.5 export)
   and get `IsCoveringMapOn F (branchLocus F)ᶜ` with ~40 lines of glue. We do NOT hand-build
   trivializations, and we additionally export our own multiplicity-aware `FiberStack`
   (needed by meromorphic-trace, and strictly stronger over branch points).
5. **Junk conventions** (CC4-compatible): `fiberMultSum` is a `finsum`; for constant or
   non-holomorphic `F` every `multiplicity` summand is junk `0`, so `fiberMultSum ≡ 0` and
   `degree = 0` — the challenge's "0 for constant maps" holds definitionally, no case split
   in the wrapper.

## 1. Standing variables and hypothesis spelling

```lean
open scoped ContDiff Manifold Topology
open Filter Set

namespace RS
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {F : X → Y}
```

- `[CompactSpace Y]` is intentionally ABSENT from the standing block: no theorem in this unit
  needs it (`Y` is compact anyway once `F` is surjective, but we never use it). Files add it
  only if a proof forces it (none should).
- `[ConnectedSpace Y]` is needed for the constancy theorem and (via `Nonempty Y`) for
  `degree`; lemmas before `LocalConstancy.lean` that don't need it drop it
  (fiber finiteness, ramification finiteness need only the `X` instances).
- Global holomorphy: `hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F`. Global nonconstancy:
  `hne : ¬ ∃ c, ∀ x, F x = c` — same spelling as surfaces-and-charts'
  `surjective_of_not_const`/`isOpenMap_of_not_const`. The bridge to local-multiplicity's
  pointwise `¬ EventuallyConst F (𝓝 x)` is `not_eventuallyConst` (§4.1), used everywhere.

## 2. Core definitions (frozen for downstream)

```lean
/-- Total multiplicity of `F` over `y` (the fiber-sum). Junk-free by convention: for
holomorphic nonconstant `F` on compact `X` the fiber is finite and every summand ≥ 1; for
constant `F` all summands are junk `0` (CC4), so the value is `0`. -/
noncomputable def fiberMultSum (F : X → Y) (y : Y) : ℕ :=
  ∑ᶠ x ∈ F ⁻¹' {y}, multiplicity F x

/-- The mapping degree. Well-defined (basepoint-independent) by
`fiberMultSum_eq_degree`; equals `0` for constant maps. The challenge's
`ContMDiff.degree f hf := RS.degree f` (final assembly). Needs `[Nonempty Y]`, provided by
`[ConnectedSpace Y]`. -/
noncomputable def degree (F : X → Y) : ℕ := fiberMultSum F (Classical.arbitrary Y)

/-- Points where `F` is ramified (local multiplicity ≥ 2, CC4's `IsRamifiedAt`). -/
def ramificationLocus (F : X → Y) : Set X := {x | IsRamifiedAt F x}

/-- Branch values (critical values): images of ramification points. -/
def branchLocus (F : X → Y) : Set Y := F '' ramificationLocus F

/-- `y` is a regular value iff every point of its fiber is unramified. (For holomorphic
nonconstant `F` this is equivalent to `y ∉ branchLocus F`, and then every fiber point has
multiplicity exactly 1.) Note: values NOT attained are regular (fiber empty) — harmless,
since for nonconstant `F` every value is attained. -/
def IsRegularValue (F : X → Y) (y : Y) : Prop := ∀ x ∈ F ⁻¹' {y}, ¬ IsRamifiedAt F x
```

`multiplicity`, `IsRamifiedAt`, `AdaptedChartsAt` are local-multiplicity's (CC4, frozen).

**The stack structure** (export of `LocalStructure.lean`; the data downstream trace units
re-use). `Fin n`-indexed to avoid dependent-`Finset` pain:

```lean
/-- A stack of adapted charts over `y₀`: the (finite) fiber enumerated as `pt : Fin n → X`,
pairwise-disjoint adapted charts at each fiber point, and an open `V ∋ y₀` that is contained
in every target-chart source, whose `F`-preimage is trapped in the chart sources, and whose
target-chart images lie in the normal-form balls. -/
structure FiberStack (F : X → Y) (y₀ : Y) where
  n : ℕ
  pt : Fin n → X
  pt_injective : Function.Injective pt
  range_pt : Set.range pt = F ⁻¹' {y₀}
  one_le_mult : ∀ i, 1 ≤ multiplicity F (pt i)
  A : ∀ i, AdaptedChartsAt F (pt i) (multiplicity F (pt i))
  disjoint_sources : Pairwise (Disjoint on fun i ↦ (A i).e.source)
  V : Set Y
  isOpen_V : IsOpen V
  mem_V : y₀ ∈ V
  V_subset : ∀ i, V ⊆ (A i).e'.source
  map_V_mem_ball : ∀ i, ∀ y ∈ V, (A i).e' y ∈ Metric.ball 0 ((A i).radius ^ multiplicity F (pt i))
  preimage_V_subset : F ⁻¹' V ⊆ ⋃ i, (A i).e.source
```

(`map_V_mem_ball` is redundant under local-multiplicity's primary spec `target_eq'`
(`e'.target = ball 0 (ρ^k)`), but keeping it as a field makes this unit immune to their
declared fallback `ball ⊆ target` — see §8.1. The existence proof gets it for free either way
by intersecting `V` with `(A i).e' ⁻¹' ball ∩ (A i).e'.source`, open in `Y`.)

## 3. File plan

| # | File | Content | Est. | Imports (project / new mathlib) |
|---|------|---------|------|-------------------------------|
| 1 | `MappingDegree/Basics.lean` | nonconstancy bridges, surface perfectness (`𝓝[≠]` NeBot, Compat), open/surjective re-exports, fiber closed+discrete+finite, `fiberMultSum` + junk API | ~250 | `Jacobian.Surface`, `Jacobian.LocalMultiplicity` / `Mathlib.Topology.DiscreteSubset`, `Mathlib.Algebra.BigOperators.Finprod` |
| 2 | `MappingDegree/RootCounting.lean` | planar: roots of `z^k = w`, count, orders, THE counting identity | ~250 | **mathlib only**: `Mathlib.RingTheory.RootsOfUnity.Complex`, `Mathlib.Analysis.Analytic.Order`, `Mathlib.Algebra.BigOperators.Finprod`, `Mathlib.Data.Set.Card` |
| 3 | `MappingDegree/Ramification.lean` | ramification/branch loci finite; regular values: characterization, cofinite, dense | ~220 | file 1 |
| 4 | `MappingDegree/LocalStructure.lean` | `FiberStack`, existence (heart, part 1), basic stack API | ~300 | file 1 (uses `AdaptedCharts`) |
| 5 | `MappingDegree/LocalConstancy.lean` | per-chart count, `FiberStack.fiberMultSum_eq_sum` (heart, part 2), `isLocallyConstant_fiberMultSum`, global constancy | ~350 | files 2, 4 |
| 6 | `MappingDegree/Degree.lean` | `degree`, `fiberMultSum_eq_degree`, positivity, regular-fiber cardinality, degree-1 ⇒ bijective/homeo, `degree_comp` | ~330 | files 3, 5 / `Mathlib.Topology.Homeomorph.Lemmas` |
| 7 | `MappingDegree/Covering.lean` | coe-exact local homeos at mult-1 points, `IsEvenlyCovered`, `IsCoveringMapOn` off the branch locus | ~200 | file 3 / `Mathlib.Topology.Covering.Basic` |
| 8 | `Jacobian/MappingDegree.lean` | unit root, API docstring | ~30 | all |

**Dependency order / build waves for parallel builders** (files are proof-independent except
through the listed imports; no file uses another's private lemmas, only §4 exports):

- Wave 1 (parallel): **1** and **2** (2 has zero project deps — can start before
  surfaces/local-multiplicity are even done, and should be built first if upstream is late).
- Wave 2 (parallel): **3** and **4** (both only need 1).
- Wave 3 (parallel): **5** and **7** (5 needs 2+4; 7 needs 3 only).
- Wave 4: **6**, then **8**.

Cross-file proof dependencies are exactly the export lists below — a builder may `sorry` an
upstream export's *statement* locally to keep moving, then delete when the file lands.

## 4. Exports (exact signatures)

### 4.1 `Basics.lean`

```lean
namespace RS

/-- A Riemann surface is perfect: punctured neighborhoods are nontrivial. (Compat: candidate
for upstreaming to surfaces-and-charts; proof via `chartAt` + ℂ's `nhdsNE_neBot`.) -/
instance (priority := 100) nhdsNE_neBot_of_chartedSpace (x : X) : (𝓝[≠] x).NeBot
  -- stated with only [TopologicalSpace X] [ChartedSpace ℂ X]; applies to Y too

/-- Globally nonconstant holomorphic maps on connected X are nowhere locally constant
(identity theorem). THE bridge to every local-multiplicity hypothesis. -/
theorem not_eventuallyConst (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) (x : X) : ¬ Filter.EventuallyConst F (𝓝 x)

/-- Pointwise multiplicity ≥ 1 under the global hypotheses (glue over
local-multiplicity's `one_le_multiplicity`). -/
theorem one_le_multiplicity_of_not_const (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) (x : X) : 1 ≤ multiplicity F x

/-- Fibers are closed and discrete, hence finite (compactness). -/
theorem isDiscrete_fiber (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hne : ¬ ∃ c, ∀ x, F x = c)
    (y : Y) : IsDiscrete (F ⁻¹' {y})
theorem fiber_finite (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hne : ¬ ∃ c, ∀ x, F x = c)
    (y : Y) : (F ⁻¹' {y}).Finite

-- re-exported (thin wrappers over surfaces-and-charts, so downstream needs one import):
theorem isOpenMap_of_not_const' (hF …) (hne …) : IsOpenMap F        -- := RS.isOpenMap_of_not_const
theorem surjective_of_not_const' (hF …) (hne …) : Function.Surjective F

-- fiberMultSum API:
theorem fiberMultSum_def (F : X → Y) (y : Y) :
    fiberMultSum F y = ∑ᶠ x ∈ F ⁻¹' {y}, multiplicity F x := rfl
theorem fiberMultSum_eq_finset_sum (hfin : (F ⁻¹' {y}).Finite) :
    fiberMultSum F y = ∑ x ∈ hfin.toFinset, multiplicity F x
theorem fiberMultSum_of_forall_eq (c : Y) : fiberMultSum (fun _ : X ↦ c) y = 0
theorem multiplicity_le_fiberMultSum (hF …) (hne …) {x : X} :
    multiplicity F x ≤ fiberMultSum F (F x)
theorem one_le_fiberMultSum (hF …) (hne …) (y : Y) : 1 ≤ fiberMultSum F y
  -- via surjectivity: fiber nonempty, terms ≥ 1
end RS
```

### 4.2 `RootCounting.lean` (mathlib-only; everything in `namespace RS`)

```lean
theorem exists_pow_eq {k : ℕ} (hk : k ≠ 0) {w : ℂ} (hw : w ≠ 0) : ∃ α : ℂ, α ^ k = w
  -- via `exp (log w / k)` — do NOT use `IsAlgClosed.exists_pow_nat_eq` (would drag in the
  -- FTA import `Mathlib.Analysis.Complex.Polynomial.Basic`); [spiked] with the exp/log proof
theorem setOf_pow_eq_zero {k : ℕ} (hk : k ≠ 0) : {z : ℂ | z ^ k = 0} = {0}
theorem setOf_pow_eq_finite (k : ℕ) (hk : k ≠ 0) (w : ℂ) : {z : ℂ | z ^ k = w}.Finite
theorem ncard_setOf_pow_eq {k : ℕ} (hk : k ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    {z : ℂ | z ^ k = w}.ncard = k
/-- Roots are trapped in the ball whose k-th power ball contains `w`. -/
theorem norm_lt_of_pow_eq {k : ℕ} (hk : k ≠ 0) {z w : ℂ} {ρ : ℝ}
    (h : z ^ k = w) (hw : ‖w‖ < ρ ^ k) : ‖z‖ < ρ
theorem analyticOrderAt_pow_sub_pow {k : ℕ} (hk : k ≠ 0) {ζ : ℂ} (hζ : ζ ≠ 0) :
    analyticOrderAt (fun z : ℂ ↦ z ^ k - ζ ^ k) ζ = 1
theorem analyticOrderAt_pow_zero (k : ℕ) : analyticOrderAt (fun z : ℂ ↦ z ^ k) 0 = k

/-- THE planar counting identity: the total multiplicity of `z ↦ z^k` over any `w` is `k`
(uniform in `w` — no branched/unbranched case split for consumers). -/
theorem sum_toNat_analyticOrderAt_pow_sub {k : ℕ} (hk : k ≠ 0) (w : ℂ) :
    ∑ᶠ ζ ∈ {z : ℂ | z ^ k = w}, (analyticOrderAt (fun z ↦ z ^ k - w) ζ).toNat = k
```

(Stated in raw `analyticOrderAt` terms — zero project imports. `LocalConstancy.lean` bridges to
`RS.multiplicity` via local-multiplicity's `multiplicityENat_planar` in two lines.)

### 4.3 `Ramification.lean`

```lean
theorem isClosed_ramificationLocus (hF …) (hne …) : IsClosed (ramificationLocus F)
theorem isDiscrete_ramificationLocus (hF …) (hne …) : IsDiscrete (ramificationLocus F)
theorem ramificationLocus_finite (hF …) (hne …) : (ramificationLocus F).Finite
theorem branchLocus_finite (hF …) (hne …) : (branchLocus F).Finite

theorem isRegularValue_iff_notMem_branchLocus (y : Y) :
    IsRegularValue F y ↔ y ∉ branchLocus F              -- pure set algebra, no hypotheses
theorem multiplicity_eq_one_of_isRegularValue (hF …) (hne …)
    {y : Y} (hy : IsRegularValue F y) {x : X} (hx : F x = y) : multiplicity F x = 1

/-- Regular values are cofinite… -/
theorem setOf_isRegularValue_mem_cofinite (hF …) (hne …) :
    {y | IsRegularValue F y} ∈ Filter.cofinite
/-- …and dense (Y is perfect + T1). -/
theorem dense_setOf_isRegularValue (hF …) (hne …) : Dense {y | IsRegularValue F y}
theorem exists_isRegularValue (hF …) (hne …) : ∃ y, IsRegularValue F y
```

### 4.4 `LocalStructure.lean`

`FiberStack` as in §2, plus:

```lean
/-- Existence of a stack over every point (heart, part 1). Note: does NOT need `F`
surjective, `Y` connected, nor the fiber nonempty (n = 0 allowed). -/
theorem exists_fiberStack (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hne : ¬ ∃ c, ∀ x, F x = c)
    (y₀ : Y) : Nonempty (FiberStack F y₀)

namespace FiberStack
variable {y₀ : Y} (S : FiberStack F y₀)
theorem maps_pt_eq (i : Fin S.n) : F (S.pt i) = y₀            -- from range_pt
theorem radius_pos (i) : 0 < (S.A i).radius                   -- re-export of chart field
theorem mem_source_pt (i) : S.pt i ∈ (S.A i).e.source
/-- The fiber over any `y ∈ V` decomposes disjointly along the chart sources. -/
theorem fiber_eq_iUnion {y : Y} (hy : y ∈ S.V) :
    F ⁻¹' {y} = ⋃ i, (F ⁻¹' {y} ∩ (S.A i).e.source)
theorem fiberMultSum_base : fiberMultSum F y₀ = ∑ i, multiplicity F (S.pt i)
  -- (also provable directly: the fiber IS the pt's; but derive it from
  --  fiberMultSum_eq_sum at y := y₀ in LocalConstancy to avoid duplication — keep here
  --  only if a builder finds the direct proof shorter)
end FiberStack
```

(`fiberMultSum_base` may live in file 5 instead — builder's choice; do not export it from both.)

### 4.5 `LocalConstancy.lean`

```lean
/-- Per-chart count (heart, part 2a): over `y ∈ V`, the part of the fiber inside the i-th
chart source carries total multiplicity `multiplicity F (pt i)`. -/
theorem FiberStack.sum_multiplicity_inter_source (S : FiberStack F y₀)
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) {y : Y} (hy : y ∈ S.V) (i : Fin S.n) :
    ∑ᶠ x ∈ F ⁻¹' {y} ∩ (S.A i).e.source, multiplicity F x = multiplicity F (S.pt i)

/-- Heart, part 2b: the fiber-sum is the same for every `y ∈ V`. -/
theorem FiberStack.fiberMultSum_eq_sum (S : FiberStack F y₀)
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) {y : Y} (hy : y ∈ S.V) :
    fiberMultSum F y = ∑ i, multiplicity F (S.pt i)

theorem isLocallyConstant_fiberMultSum (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) : IsLocallyConstant (fiberMultSum F)

/-- THE well-definedness theorem ([ConnectedSpace Y] enters here). -/
theorem fiberMultSum_const (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) (y y' : Y) : fiberMultSum F y = fiberMultSum F y'
```

### 4.6 `Degree.lean`

```lean
theorem fiberMultSum_eq_degree (hF …) (hne …) (y : Y) : fiberMultSum F y = degree F
theorem degree_eq_fiberMultSum (hF …) (hne …) (y : Y) : degree F = ∑ᶠ x ∈ F ⁻¹' {y}, multiplicity F x
theorem degree_of_forall_eq (c : Y) : degree (fun _ : X ↦ c) = 0
theorem one_le_degree (hF …) (hne …) : 1 ≤ degree F
theorem degree_pos_iff (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) :
    0 < degree F ↔ ¬ ∃ c, ∀ x, F x = c
theorem multiplicity_le_degree (hF …) (hne …) (x : X) : multiplicity F x ≤ degree F

/-- Fiber cardinality equals the degree over regular values. -/
theorem ncard_fiber_of_isRegularValue (hF …) (hne …) {y : Y} (hy : IsRegularValue F y) :
    (F ⁻¹' {y}).ncard = degree F
theorem ncard_fiber_le_degree (hF …) (hne …) (y : Y) : (F ⁻¹' {y}).ncard ≤ degree F

-- Abel / genus-zero-headline bank (ASSIGNED HERE, not in proper-map-degree):
theorem bijective_of_degree_eq_one (hF …) (hne …) (h1 : degree F = 1) :
    Function.Bijective F
theorem isHomeomorph_of_degree_eq_one (hF …) (hne …) (h1 : degree F = 1) : IsHomeomorph F
noncomputable def homeomorphOfDegreeEqOne (hF …) (hne …) (h1 : degree F = 1) : X ≃ₜ Y
theorem coe_homeomorphOfDegreeEqOne … : ⇑(homeomorphOfDegreeEqOne hF hne h1) = F

/-- Degree is multiplicative (statement bank; consumers: none critical — drop LAST if the
unit runs long, after clearing with the orchestrator). `Z` a third compact connected
surface, `X --F--> Y --G--> Z`. -/
theorem degree_comp {Z : Type*} [inst…] {G : Y → Z} (hG : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω G)
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hneG : ¬ ∃ c, ∀ y, G y = c) (hneF : ¬ ∃ c, ∀ x, F x = c) :
    degree (G ∘ F) = degree G * degree F
```

NOTE for `degree_comp`: it needs `[CompactSpace Y]` (fibers of `G` finite) — the only
statement in the unit that does; add the instance to its signature locally.

### 4.7 `Covering.lean`

```lean
/-- Multiplicity-1 points admit an `OpenPartialHomeomorph` whose coe is literally `F`
(the coe-exact upgrade of local-multiplicity's Forster 2.5 export; mathlib's covering
constructor requires `↑φ = F` on the nose). -/
theorem exists_openPartialHomeomorph_coe_eq (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) {x : X} (h1 : ¬ IsRamifiedAt F x) :
    ∃ φ : OpenPartialHomeomorph X Y, x ∈ φ.source ∧ ⇑φ = F

theorem isEvenlyCovered_of_isRegularValue (hF …) (hne …) {y : Y}
    (hy : IsRegularValue F y) : IsEvenlyCovered F y (F ⁻¹' {y})

/-- `F` is a covering map away from the branch locus (finite, by Ramification). -/
theorem isCoveringMapOn_compl_branchLocus (hF …) (hne …) :
    IsCoveringMapOn F (branchLocus F)ᶜ
```

Downstream may compose with mathlib's `IsCoveringMapOn.isCoveringMap_restrictPreimage`
(`Covering/Basic.lean:298`) for a genuine `IsCoveringMap` of the subtype restriction, and
with `Topology/Homotopy/Lifting.lean` for path/homotopy lifting — no extra exports needed
here; say so in the root docstring.

## 5. Proof plans for the five hardest theorems

### P1. `exists_fiberStack` (heart, part 1) — Forster 4.24 proof, first half

Write `hnc x := not_eventuallyConst hF hne x` and `hFx := hF.contMDiffAt`.

1. **Enumerate the fiber.** `hfin := fiber_finite hF hne y₀`; `n := hfin.toFinset.card`;
   `pt := Subtype.val ∘ (hfin.toFinset.equivFin.symm)` gives `pt : Fin n → X` injective with
   `range pt = F ⁻¹' {y₀}` (`Finset.equivFin`, `Finset.coe_sort_coe`; massage with
   `Set.Finite.coe_toFinset`). `one_le_mult` := `one_le_multiplicity_of_not_const`.
2. **Disjoint opens.** `Set.Finite.t2_separation` (`Topology/Separation/Hausdorff.lean:110`)
   **[spiked]** on `hfin` gives `U : X → Set X` with `∀ x, x ∈ U x ∧ IsOpen (U x)` and
   `(F ⁻¹' {y₀}).PairwiseDisjoint U`. Then `Pairwise (Disjoint on fun i ↦ U (pt i))` from
   `pt_injective` + `range_pt` (`Set.PairwiseDisjoint` unfolds to pairwise-on-set; transport
   along `pt`).
3. **Adapted charts, shrunk.** For each `i`, `(U (pt i)) ∈ 𝓝 (pt i)` (open ∋ pt i);
   local-multiplicity's `exists_adaptedChartsAt (hFx (pt i)) (hnc (pt i)) hU` yields
   `A i : AdaptedChartsAt F (pt i) (multiplicity F (pt i))` with `(A i).e.source ⊆ U (pt i)`.
   (`Classical.choice`/`choose` over `Fin n`.) `disjoint_sources` follows by monotonicity of
   `Disjoint` from step 2.
4. **Trap the fiber.** `W₀ := ⋃ i, (A i).e.source` is open. `F ⁻¹' {y₀} ⊆ W₀`: any `x` in the
   fiber is `pt i` for some `i` (`range_pt`), and `pt i ∈ (A i).e.source` (`mem_source`).
   So `W₀ ∈ 𝓝ˢ (F ⁻¹' {y₀})` (`IsOpen.mem_nhdsSet.2`). `F` is a closed map:
   `hF.continuous.isClosedMap` (`Topology/Separation/Hausdorff.lean:664`,
   `[CompactSpace X] [T2Space Y]`) **[spiked]**. By `IsClosedMap.comap_nhds_le`
   (`Topology/Maps/Basic.lean:617`) **[spiked]**, `W₀ ∈ comap F (𝓝 y₀)`, i.e. by `mem_comap`
   there is `W ∈ 𝓝 y₀` with `F ⁻¹' W ⊆ W₀`; shrink `W` to open (`mem_nhds_iff`).
5. **Assemble `V`.**
   `V := W ∩ ⋂ i, ((A i).e'.source ∩ (A i).e' ⁻¹' Metric.ball 0 ((A i).radius ^ mult…))`.
   - Open: `W` open (step 4); each intersectand is open — `e'.source` open, and the
     preimage-of-ball term is `e'.source ∩ e' ⁻¹' ball` which is open because `e'` is
     continuous on its open source (`OpenPartialHomeomorph.continuousOn_toFun`,
     `ContinuousOn.isOpen_inter_preimage`); finite intersection via
     `isOpen_iInter_of_finite`.
   - `y₀ ∈ V`: `y₀ ∈ W`; for each `i`: `F (pt i) = y₀` (`range_pt` ∋ pt i), so
     `y₀ ∈ e'.source` (`mem_source'`) and `e' y₀ = 0 ∈ ball` (`map_eq_zero'`,
     `radius_pos` + `one_le_mult` ⇒ `0 < ρ^k`, `pow_pos`).
   - `V_subset`, `map_V_mem_ball`, `preimage_V_subset` (via `F ⁻¹' V ⊆ F ⁻¹' W ⊆ W₀`),
     `isOpen_V`, `mem_V`: by construction.

Est. 150–200 lines. The only delicate Lean is step 1's enumeration (use
`Set.Finite.toFinset` + `Finset.equivFin`; alternatively `Set.Finite.exists_finset_coe` +
`Finset.orderIsoOfFin`-free enumeration — builder's choice, the interface only needs SOME
`pt`).

### P2. `FiberStack.sum_multiplicity_inter_source` + `fiberMultSum_eq_sum` (heart, part 2)

Fix `y ∈ S.V`, `i`; abbreviate `A := S.A i`, `e := A.e`, `e' := A.e'`,
`k := multiplicity F (S.pt i)` (`k ≥ 1` by `one_le_mult`), `ρ := A.radius`,
`w := e' y` (defined: `hy` + `V_subset`), `hw : ‖w‖ < ρ ^ k` (`map_V_mem_ball` +
`Metric.mem_ball_zero_iff` — note `dist w 0 = ‖w‖`, `mem_ball_zero_iff` is the mathlib name).

**(a) Chart bijection.** `Set.BijOn e (F ⁻¹' {y} ∩ e.source) {ζ : ℂ | ζ ^ k = w}`:
- *MapsTo*: `x ∈ F⁻¹{y} ∩ source` ⇒ `e' (F x) = (e x)^k` (`eqOn_pow`) and `F x = y` ⇒
  `(e x)^k = w`. ✓
- *InjOn*: `e.injOn` restricted (charts are injective on source). ✓
- *SurjOn*: given `ζ` with `ζ^k = w`: `‖ζ‖ < ρ` by `norm_lt_of_pow_eq` (§4.2, using `hw`),
  so `ζ ∈ Metric.ball 0 ρ ⊆ e.target` (primary spec: `target_eq` gives equality; fallback
  spec: inclusion — both fine). Put `x := e.symm ζ ∈ e.source`
  (`OpenPartialHomeomorph.map_target`). Then `e' (F x) = (e x)^k = ζ^k = w = e' y`
  (`eqOn_pow`, `e.right_inv`). Both `F x` (by `A.mapsTo`) and `y` (by `V_subset`) lie in
  `e'.source`, and `e'` is injective there ⇒ `F x = y`, and `e x = ζ` exhibits surjectivity. ✓

**(b) Multiplicity transport.** For `x ∈ F⁻¹{y} ∩ e.source`:
`multiplicity F x = (analyticOrderAt (fun z ↦ z ^ k - w) (e x)).toNat`.
- local-multiplicity chart invariance (`analyticOrderAt_charts_eq_multiplicityENat`, needs
  `hF.contMDiffAt x`, `A.mem_maximalAtlas`, `A.mem_maximalAtlas'`, `x ∈ e.source`,
  `F x = y ∈ e'.source`):
  `analyticOrderAt (fun z ↦ e' (F (e.symm z)) - e' (F x)) (e x) = multiplicityENat F x`.
- Germ rewrite on the open set `e.target ∋ e x`: for `z ∈ e.target`,
  `e' (F (e.symm z)) = (e (e.symm z))^k = z^k` (`eqOn_pow` at `e.symm z ∈ e.source`,
  `e.right_inv`), and `e' (F x) = e' y = w`. So by `analyticOrderAt_congr`
  (`Analysis/Analytic/Order.lean:176`) the LHS equals
  `analyticOrderAt (fun z ↦ z ^ k - w) (e x)`.
- Apply `ENat.toNat` on both sides; `multiplicity = (multiplicityENat _ _).toNat` by CC4.

**(c) Per-chart sum.** By `finsum_mem_eq_of_bijOn` (`Finprod.lean:958`, additive version)
**[spiked]** with the bijection (a) and pointwise equality (b):
`∑ᶠ x ∈ F⁻¹{y} ∩ e.source, multiplicity F x
  = ∑ᶠ ζ ∈ {ζ | ζ^k = w}, (analyticOrderAt (fun z ↦ z^k - w) ζ).toNat = k`
by `sum_toNat_analyticOrderAt_pow_sub` (§4.2). ∎(2a)

**(d) Fiber decomposition and total.**
- `F ⁻¹' {y} = ⋃ i, (F ⁻¹' {y} ∩ (S.A i).e.source)`: `⊇` trivial; `⊆` is
  `preimage_V_subset` at `y ∈ V`.
- Each piece is finite: image under injective-on `e` of a subset of the finite root set,
  i.e. `Set.Finite.of_finite_image` + `setOf_pow_eq_finite`, or directly: subset of
  the finite fiber (`fiber_finite`) — use the latter (no `hne` needed? `fiber_finite`
  needs `hne`; the root-set route avoids `hne` — builder picks; the stack's existence
  already implies nonconstancy morally, but keep hypotheses explicit).
- Pieces pairwise disjoint: `disjoint_sources`, monotone.
- `finsum_mem_iUnion` (`Finprod.lean:1029`, `[Finite (Fin n)]`) **[spiked]**:
  `fiberMultSum F y = ∑ᶠ i, (per-chart sum) = ∑ᶠ i, multiplicity F (S.pt i)`; close with
  `finsum_eq_sum_of_fintype` to the `Finset.univ.sum` form. ∎(2b)

**(e) Local constancy and constancy.** For `isLocallyConstant_fiberMultSum`: use
`IsLocallyConstant.iff_exists_open` (`Topology/LocallyConstant/Basic.lean:73`): at `y₀` take
`S := (exists_fiberStack hF hne y₀).some`, the open `S.V ∋ y₀`; every `y ∈ S.V` has
`fiberMultSum F y = ∑ i, multiplicity F (S.pt i) = fiberMultSum F y₀` (apply (2b) twice —
at `y` and at `y₀ ∈ V`). Then `fiberMultSum_const` is
`IsLocallyConstant.apply_eq_of_preconnectedSpace` (`LocallyConstant/Basic.lean:137`)
**[spiked]** (`[ConnectedSpace Y]` provides `PreconnectedSpace Y`). ∎

Est. 250–330 lines total for file 5. Fiddly points: (b)'s germ rewrite (eta-normal forms —
ALWAYS pass through `analyticOrderAt_congr`, never syntactic equality; the congruence set is
`e.target`, open by `open_target`) and (d)'s `finsum` support-side conditions (each
`finsum_mem_*` lemma wants finiteness of the sets, provided).

### P3. `sum_toNat_analyticOrderAt_pow_sub` (planar counting identity)

Case `w = 0`: root set is `{0}` (`setOf_pow_eq_zero`: `pow_eq_zero_iff hk`);
`finsum_mem_singleton`; the order is `analyticOrderAt (fun z ↦ z^k - 0) 0`: rewrite
`sub_zero` under `analyticOrderAt_congr`(or `funext`-free `simp only [sub_zero]`), then
`analyticOrderAt_pow_zero`: `analyticOrderAt (fun z ↦ z^k) 0 = k` via `analyticOrderAt_pow`
(`Order.lean:455`) **[spiked]** applied to `f := id` (`Pi.pow_apply` bridges
`(id ^ k) z = z ^ k`; `analyticOrderAt id 0 = 1` from
`AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero` (`Order.lean:305`) **[spiked]** with
`f := id`, `deriv id 0 = 1 ≠ 0`, plus a `sub_zero`-congr); `ENat.toNat` of `k`. ✓

Case `w ≠ 0`:
1. **The root set is `k` simple points.** `hprim := Complex.isPrimitiveRoot_exp k hk`
   (`RingTheory/RootsOfUnity/Complex.lean:85`) **[spiked]**; a root exists:
   `α := Complex.exp (Complex.log w / k)`, `α ^ k = w` by `← Complex.exp_nat_mul`,
   `mul_div_assoc'` + `mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hk)`
   (`Algebra/GroupWithZero/Defs.lean:216`), `Complex.exp_log hw` — **[spiked verbatim]**
   (all available from the `RootsOfUnity.Complex` import; do NOT import the FTA).
   The set equals the coe of `(Polynomial.nthRoots k w).toFinset`
   (`Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hk)`, `Roots.lean:324`) **[spiked]**; card:
   `Set.ncard_coe_finset` (`Data/Set/Card.lean:636`, lowercase `finset`!) +
   `Multiset.toFinset_card_of_nodup` (`Finset/Card.lean:186`) with `hprim.nthRoots_nodup hw`
   (`RootsOfUnity/PrimitiveRoots.lean:667`), then `hprim.card_nthRoots`
   (`PrimitiveRoots.lean:625`) `= if ∃ α, α^k = w then k else 0 = k`. **[spiked, assembled:
   the full `ncard_setOf_pow_eq` proof compiled]**.
2. **Each root is simple.** `ζ^k = w ≠ 0` ⇒ `ζ ≠ 0`; `analyticOrderAt_pow_sub_pow`:
   apply `AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero` with `f := (· ^ k)`,
   `f ζ = ζ^k`; `deriv (· ^ k) ζ = k * ζ^(k-1) ≠ 0` (`deriv_pow`, field arithmetic,
   `hk`, `hζ`). (Statement matches the mathlib lemma's `(f · - f x)` shape after rewriting
   `f ζ = w`.)
3. **Sum = card.** All summands are `1` on the root set:
   `finsum_mem_congr` to the constant-1 function, then
   `finsum_mem_finset`-style evaluation: `∑ᶠ ζ ∈ s, (1:ℕ) = s.ncard` (via
   `finsum_mem_eq_finite_toFinset_sum` (`Finprod.lean:518`) + `Finset.sum_const` +
   `Set.ncard_eq_toFinset_card`), then step 1. ✓

Est. 200 lines with the ball-trapping and finiteness lemmas
(`norm_lt_of_pow_eq`: from `ζ^k = w`, `‖ζ‖^k = ‖w‖ < ρ^k` (`norm_pow`), conclude
`‖ζ‖ < ρ` by `pow_lt_pow_left`-monotonicity contrapositive (`le_antisymm`-style:
`ρ ≤ ‖ζ‖ ⇒ ρ^k ≤ ‖ζ‖^k`, `pow_le_pow_left` with `0 ≤ ρ` — take `0 < ρ` from
`‖w‖ ≥ 0 < ρ^k` ⇒ `ρ > 0`)).

### P4. `ramificationLocus_finite` (+ closedness/discreteness) and fiber finiteness

Both instances of one pattern — **a set `S ⊆ X` such that every `x : X` has
`∀ᶠ z in 𝓝[≠] x, z ∉ S`, and `S ⊆ {x | x-local condition}` making `x ∈ S` decidable at
itself, is closed, discrete, and (X compact) finite**:

1. *Punctured avoidance.* Ramification: local-multiplicity's
   `eventually_multiplicity_eq_one (hF.contMDiffAt x) (not_eventuallyConst hF hne x)` gives
   `∀ᶠ z in 𝓝[≠] x, multiplicity F z = 1`, hence `z ∉ ramificationLocus F`
   (`IsRamifiedAt` is `2 ≤ mult`). Fibers: surfaces' `eventually_ne_of_not_const` (or
   local-multiplicity's `eventually_ne`) gives `∀ᶠ z in 𝓝[≠] x, F z ≠ F x`; for a FIXED `y`
   and `x` in the fiber this reads `z ∉ F⁻¹{y}`; for `x ∉ F⁻¹{y}` use continuity +
   T2-openness of `{F · ≠ y}`… simpler: fibers are closed anyway
   (`IsClosed.preimage hF.continuous isClosed_singleton`), so only discreteness needs the
   punctured statement at fiber points.
2. *Discrete.* `isDiscrete_iff_nhdsNE` (`Topology/DiscreteSubset.lean:53`) **[spiked]**: for
   `x ∈ S`, `𝓝[≠] x ⊓ 𝓟 S = ⊥` follows from the eventual avoidance
   (`Filter.inf_principal_eq_bot`-style: the avoidance set is in `𝓝[≠] x` and misses `S`;
   `eventually_iff` + `inf_principal_eq_bot.2`).
3. *Closed* (ramification): complement is open: if `x ∉ S`, combine "`z ≠ x → z ∉ S`
   eventually in `𝓝 x`" (`eventually_nhdsWithin_iff.mp` of step 1) with "`z = x → z ∉ S`"
   (assumption) to get `∀ᶠ z in 𝓝 x, z ∉ S`; conclude `IsOpen Sᶜ` via `isOpen_iff_mem_nhds`.
4. *Finite.* `IsClosed.isCompact` (closed in compact `X`), then `IsCompact.finite`
   (`Topology/Compactness/Compact.lean:1023`) **[spiked]** with step 2.
5. `branchLocus_finite := (ramificationLocus_finite …).image F`. Regular-value corollaries:
   `isRegularValue_iff_notMem_branchLocus` is set algebra (`y ∉ F '' S ↔ ∀ x, F x = y → x ∉ S`
   — `Set.mem_image`, careful with the `∈ fiber` spelling);
   `multiplicity_eq_one_of_isRegularValue`: `¬(2 ≤ mult)` + `1 ≤ mult` ⇒ `= 1` (`omega`
   after `one_le_multiplicity_of_not_const`). Cofinite: `Filter.mem_cofinite` + complement
   ⊆ `branchLocus` (the complement of the regular set IS contained in the branch locus by the
   iff) + `Set.Finite.subset`. Dense: complement of a finite set in a T1 space all of whose
   points are non-isolated: finite ⇒ closed (`Set.Finite.isClosed`, T1), and its interior is
   empty — a nonempty open subset would be an infinite set (`infinite_of_mem_nhds`,
   `Topology/Separation/Basic.lean:768` **[spiked]**, with the `Basics` instance
   `(𝓝[≠] y).NeBot`) inside a finite set; then
   `interior_eq_empty_iff_dense_compl` (`Topology/Closure.lean:387`). `exists_isRegularValue`:
   density or cofiniteness + `Y` infinite (again `infinite_of_mem_nhds` on `univ`); easiest:
   `Dense.nonempty` on the (open) regular set… (builder: `dense_iff_inter_open` with `univ`).

Perfectness instance (`Basics`): for `x : X`, `chartAt ℂ x` maps `𝓝 x` to `𝓝 (chartAt ℂ x x)`
homeomorphically on its source (`OpenPartialHomeomorph.map_nhds_eq`,
`Topology/OpenPartialHomeomorph/Continuity.lean:73`); ℂ has `NeBot (𝓝[≠] z)`
(`nhdsNE_neBot`, instance, `Analysis/Normed/Field/Basic.lean:242` **[spiked]**); pull back:
if `𝓝[≠] x = ⊥` then `{x}ᶜ ∉ 𝓝[≠] x`… direct route: `mem_closure_iff_nhdsWithin_neBot`
with `x ∈ closure ({x}ᶜ)` transported through the chart (the chart image of any nbhd of `x`
is a nbhd of the center, which meets `(chart image of {x}ᶜ) ⊇ (nbhd ∩ target) \ {center}` —
5–10 lines; or the filter-map route of local-multiplicity's risk 6:
`Filter.map e (𝓝[≠] x) = 𝓝[≠] (e x)` on the source (map_nhds_eq + injectivity), and
`NeBot.map`… note the direction needed is `comap`/symm — use
`(𝓝[≠] (e x)).NeBot` + `e.symm`-map = `𝓝[≠] x` restricted; write it with
`OpenPartialHomeomorph.map_nhdsWithin_eq` at the point `e x` for `e.symm`).

### P5. Degree API: `ncard_fiber_of_isRegularValue`, `bijective_of_degree_eq_one`, `degree_comp`

- `fiberMultSum_eq_degree` := `fiberMultSum_const hF hne y (Classical.arbitrary Y)`.
- `ncard_fiber_of_isRegularValue`: `fiberMultSum F y = ∑ x ∈ hfin.toFinset, mult F x`
  (`fiberMultSum_eq_finset_sum`); every term is `1`
  (`multiplicity_eq_one_of_isRegularValue`); `Finset.sum_const` + `Finset.card` =
  `Set.ncard` (`Set.ncard_eq_toFinset_card`). Combine with `fiberMultSum_eq_degree`.
- `ncard_fiber_le_degree`: termwise `1 ≤ mult` on the fiber Finset:
  `Finset.card_nsmul_le_sum`.
- `bijective_of_degree_eq_one`: surjective by `surjective_of_not_const'`. Injective: suppose
  `F x₁ = F x₂ = y`, `x₁ ≠ x₂`. Then with `hfin := fiber_finite …`,
  `{x₁, x₂} ⊆ hfin.toFinset` (a 2-element Finset), so
  `2 = ∑ x ∈ {x₁,x₂}, 1 ≤ ∑ x ∈ {x₁,x₂}, mult F x ≤ ∑ x ∈ hfin.toFinset, mult F x
   = fiberMultSum F y = degree F = 1` (`Finset.sum_le_sum_of_subset` — multiplicities are ≥ 1
  and ℕ-valued so monotone; `Finset.card_pair` for the `2`), contradiction.
- `homeomorphOfDegreeEqOne` := `Continuous.homeoOfEquivCompactToT2`
  (`Topology/Homeomorph/Lemmas.lean:470`) **[spiked]** on `Equiv.ofBijective F hbij` with
  `hF.continuous` (coercion side condition: `⇑(Equiv.ofBijective F hbij) = F` is `rfl`).
  `isHomeomorph_of_degree_eq_one` via `isHomeomorph_iff_exists_homeomorph` (`:506`) or
  directly `Homeomorph.isHomeomorph` + the coe lemma.
- `degree_pos_iff`: (⇐) `one_le_degree` (fiber over any point nonempty by surjectivity;
  each term ≥ 1; `finsum` over nonempty finite set of positives is positive — via
  `fiberMultSum_eq_finset_sum` + `Finset.sum_pos`). (⇒) contrapositive: constant `F` has
  `multiplicity ≡ 0` (CC4 junk lemma `multiplicity_of_eventuallyConst`), so
  `fiberMultSum ≡ 0` (`finsum_mem_of_eqOn_zero`, additive of `Finprod.lean:683`), so
  `degree = 0`.
- `degree_comp` (needs `[CompactSpace Y]`): fix `z₀`. `(G∘F)⁻¹{z₀} = ⋃ y ∈ G⁻¹{z₀}, F⁻¹{y}`
  (set ext), a pairwise-disjoint union over the finite set `G⁻¹{z₀}`
  (`fiber_finite` for `G`). `finsum_mem_biUnion` (`Finprod.lean:1048`):
  `fiberMultSum (G∘F) z₀ = ∑ᶠ y ∈ G⁻¹{z₀}, ∑ᶠ x ∈ F⁻¹{y}, multiplicity (G∘F) x`.
  Pointwise `multiplicity (G∘F) x = multiplicity G (F x) * multiplicity F x`
  (local-multiplicity `multiplicity_comp`); on `F⁻¹{y}` the first factor is the constant
  `multiplicity G y`, pull it out (`finsum_mem_congr` then `Nat.mul`-distribute via
  `finsum_mem`-`mul_finsum`-style: `∑ᶠ x ∈ s, c * f x = c * ∑ᶠ x ∈ s, f x` —
  `finsum_mem_mul'`-adjacent for ℕ; if the exact ℕ-lemma is missing, convert to `Finset.sum`
  first — `Finset.mul_sum`). Get `∑ᶠ y ∈ G⁻¹{z₀}, multiplicity G y * degree F`
  (inner sum = `fiberMultSum F y = degree F`), `= degree F * fiberMultSum G z₀
  = degree G * degree F`. `G∘F` nonconstant: if `(G∘F) ≡ c` then, `F` surjective ⇒ `G ≡ c`,
  contra `hneG`; holomorphy `hG.comp hF`.

### P6 (bonus, file 7). `isCoveringMapOn_compl_branchLocus`

1. `exists_openPartialHomeomorph_coe_eq`: from `¬ IsRamifiedAt F x` + `1 ≤ mult` get
   `multiplicity F x = 1`; local-multiplicity's
   `exists_openPartialHomeomorph_of_multiplicity_eq_one` gives `ψ` with `x ∈ ψ.source` and
   `∀ z ∈ ψ.source, ψ z = F z`. Upgrade to `⇑φ = F` by rebuilding the structure with
   `toFun := F` (all `PartialEquiv`/`OpenPartialHomeomorph` axioms quantify only over
   `source`/`target`, so the `EqOn` transports each field; `continuousOn_toFun` via
   `ContinuousOn.congr`). ~20 lines; make it a general private helper
   `OpenPartialHomeomorph.copyOfEqOn (ψ) (f) (h : ∀ z ∈ ψ.source, ψ z = f z) : …` with
   `⇑ = f`, `source`/`target` unchanged.
2. `isCoveringMapOn_compl_branchLocus := IsCoveringMapOn.of_openPartialHomeomorph
   hF.continuous h` (`Topology/Covering/Basic.lean:580`; `f`, `s` are IMPLICIT there —
   verified by spike; instances: `[T2Space X]` (source, called `E` there), `[T2Space Y]`,
   `[CompactSpace X]`) **[spiked]** where `h`:
   for `e ∈ F ⁻¹' (branchLocus F)ᶜ`, `F e` is not a branch value ⇒ `e` unramified
   (`e ∈ ramificationLocus ⇒ F e ∈ branchLocus`, contrapositive of `Set.mem_image_of_mem`)
   ⇒ step 1.
3. `isEvenlyCovered_of_isRegularValue`: instance of 2 via
   `isRegularValue_iff_notMem_branchLocus` (an `IsCoveringMapOn` applied at the point IS the
   `IsEvenlyCovered` statement, definitional unfold).

## 6. Mathlib tools (all read in pinned source; **[spiked]** = compiled in §10)

| Name | Location | Use |
|---|---|---|
| `IsCompact.finite (hs) (hs' : IsDiscrete s)` | `Topology/Compactness/Compact.lean:1023` **[spiked]** | finiteness plumbing (fibers, ramification) |
| `IsDiscrete` (structure), `isDiscrete_iff_nhdsNE`, `discreteTopology_of_noAccPts` | `Topology/Constructions.lean:261`, `Topology/DiscreteSubset.lean:53` **[spiked]** | discreteness bookkeeping |
| `Set.Finite.t2_separation` | `Topology/Separation/Hausdorff.lean:110` **[spiked]** | disjoint opens around the fiber |
| `Continuous.isClosedMap` | `Topology/Separation/Hausdorff.lean:664` **[spiked]** | F closed map |
| `IsClosedMap.comap_nhds_le` (alias of `isClosedMap_iff_comap_nhds_le`) | `Topology/Maps/Basic.lean:607/:617` **[spiked]** | fiber trapping |
| `IsOpen.mem_nhdsSet`, `mem_comap`, `mem_nhds_iff` | std | fiber trapping |
| `finsum_mem_iUnion` | `Algebra/BigOperators/Finprod.lean:1029` (additive) **[spiked]** | fiber decomposition |
| `finsum_mem_eq_of_bijOn` | `Finprod.lean:958` (additive) **[spiked]** | chart transport of sums |
| `finsum_mem_coe_finset` / `finsum_mem_eq_finite_toFinset_sum` / `finsum_eq_sum_of_fintype` / `finsum_mem_of_eqOn_zero` / `finsum_mem_biUnion` | `Finprod.lean:527/518/1036(usage)/683/1048` (additive) | fiberMultSum API |
| `Complex.isPrimitiveRoot_exp (n) (h0 : n ≠ 0)` | `RingTheory/RootsOfUnity/Complex.lean:85` **[spiked]** | root counting |
| `IsPrimitiveRoot.card_nthRoots`, `.nthRoots_nodup` | `RingTheory/RootsOfUnity/PrimitiveRoots.lean:625/:667` **[spiked]** | `#roots = k`, simple |
| `Complex.exp_log`, `Complex.exp_nat_mul`, `mul_div_cancel_left₀` | std (in scope via `RootsOfUnity.Complex`) **[spiked]** | k-th root existence (NOT `IsAlgClosed.exists_pow_nat_eq` — its instance needs the FTA import) |
| `Polynomial.mem_nthRoots (hn : 0 < n)` | `Algebra/Polynomial/Roots.lean:324` **[spiked]** | set ↔ multiset of roots |
| `Multiset.toFinset_card_of_nodup` | `Data/Finset/Card.lean:186` **[spiked]** | card transfer |
| `Set.ncard_eq_toFinset_card'` / `Set.ncard_coe_finset` | `Data/Set/Card.lean:605/:636` (lowercase `finset`) **[spiked]** | ncard bridges |
| `analyticOrderAt_pow`, `AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero`, `analyticOrderAt_congr` | `Analysis/Analytic/Order.lean:455/:305/:176` **[spiked]** | planar orders |
| `IsLocallyConstant.iff_exists_open`, `.apply_eq_of_preconnectedSpace` | `Topology/LocallyConstant/Basic.lean:73/:137` **[spiked]** | constancy |
| `nhdsNE_neBot` (ℂ instance) | `Analysis/Normed/Field/Basic.lean:242` **[spiked]** | perfectness |
| `infinite_of_mem_nhds` | `Topology/Separation/Basic.lean:768` **[spiked]** | density of regular values |
| `interior_eq_empty_iff_dense_compl` | `Topology/Closure.lean:387` | density |
| `IsCoveringMapOn.of_openPartialHomeomorph` | `Topology/Covering/Basic.lean:580` **[spiked]** | covering off branch locus |
| `IsCoveringMapOn.isCoveringMap_restrictPreimage` | `Covering/Basic.lean:298` | downstream note only |
| `Continuous.homeoOfEquivCompactToT2` | `Topology/Homeomorph/Lemmas.lean:470` **[spiked]** | degree-1 homeo |
| `OpenPartialHomeomorph.map_nhds_eq` / `.map_nhdsWithin_eq` / `.continuousOn` / `.injOn` / `.right_inv` / `.map_target` | `Topology/OpenPartialHomeomorph/*` | chart plumbing |

Upstream (project) inputs consumed — from **surfaces-and-charts** (design §3.4):
`eq_of_frequently_eq` (identity theorem), `eventually_ne_of_not_const`,
`isOpenMap_of_not_const`, `surjective_of_not_const`. From **local-multiplicity** (design
§2/§4): `multiplicity`, `multiplicityENat`, `IsRamifiedAt`, `multiplicityENat_planar`,
`one_le_multiplicity`, `multiplicity_of_eventuallyConst`, `natCast_multiplicity`,
`eventually_ne`, `eventually_multiplicity_eq_one`,
`analyticOrderAt_charts_eq_multiplicityENat` (chart invariance), `AdaptedChartsAt`
(+ fields + `exists_adaptedChartsAt` with `⊆ U` shrinking),
`exists_openPartialHomeomorph_of_multiplicity_eq_one`, `multiplicity_comp`.

## 7. Downstream consumption map (what to cite, from where)

| Consumer | What it needs | Our export |
|---|---|---|
| **final assembly / proper-map-degree** | `ContMDiff.degree` wrapper; "0 if constant" | `RS.degree` (wrapper is `RS.degree f`, no case split), `degree_of_forall_eq`, `degree_pos_iff` |
| **proper-map-degree** (`deg(div f) = 0`) | zeros−poles: total multiplicity of `f : X → ℙ¹` over `0` and over `∞` both = degree | `fiberMultSum_eq_degree` at `y := 0`, `y := ∞`; `fiberMultSum_eq_finset_sum` to open the sum; their unit bridges `multiplicity` ↔ `ordAtX` (CC3/CC4 compat lemmas in local-multiplicity) |
| **genus-zero-headline / Abel** | degree-1 ⇒ bijective ⇒ homeo | `bijective_of_degree_eq_one`, `homeomorphOfDegreeEqOne` (+ coe lemma), `isHomeomorph_of_degree_eq_one` |
| **meromorphic-trace / form-trace-tower** | fiber decomposition with multiplicities + local sections over a nbhd of ANY `y₀` (branch or not); regular values cofinite | `FiberStack` (whole structure), `exists_fiberStack`, `FiberStack.sum_multiplicity_inter_source`, `fiber_finite`, `setOf_isRegularValue_mem_cofinite` |
| **paths-and-integrals / abel-weak** | perturb loops off branch values; covering over the complement (homotopy lifting via mathlib) | `branchLocus_finite`, `isCoveringMapOn_compl_branchLocus` (+ mathlib `isCoveringMap_restrictPreimage`, `Topology/Homotopy/Lifting.lean`) |
| **jacobian-construction** | (per DAG) openness/surjectivity/nonconstancy glue | `not_eventuallyConst`, `surjective_of_not_const'`, `isOpenMap_of_not_const'` |
| **anyone** | surface perfectness | `nhdsNE_neBot_of_chartedSpace` instance |

Builder must also: append to `docs/requests/surfaces-and-charts.md` (offer
`nhdsNE_neBot_of_chartedSpace` for upstreaming into their unit) and create
`docs/requests/local-multiplicity.md` if any consumed export drifted from their design doc.

## 8. Risks & fallbacks

1. **Upstream drift (HIGH — both dependencies are mid-build).** (a) local-multiplicity's
   declared fallback weakens `AdaptedChartsAt.target_eq/target_eq'` to `ball ⊆ target` plus
   an `image_source` field. Our design is already robust: the heart uses `target_eq` only for
   root-trapping (`ball 0 ρ ⊆ e.target` suffices — inclusion direction only) and
   `map_V_mem_ball` is a `FiberStack` FIELD obtained by shrinking `V`, not read off
   `target_eq'`. If field names/shapes change, only `LocalStructure.lean` (existence proof)
   and P2(a)–(b) need mechanical edits. (b) surfaces' IFT reshape (their risk 2) does not
   touch us — we consume Identity-file exports and local-multiplicity, not the raw IFT.
   (c) If `exists_adaptedChartsAt`'s shrinking conclusion (`A.e.source ⊆ U`) is dropped,
   recover it: restrict the chart (`(A.e).restrOpen`) — but then atlas-membership fields must
   be re-derived; instead ASK local-multiplicity to keep `⊆ U` (it is in their frozen design).
2. **`finsum` side-condition friction (MEDIUM).** Every `finsum_mem_*` rewrite needs
   finiteness/support facts; ℕ-valued functions have `support = {≠ 0}` which is NOT the fiber
   (mult ≥ 1 helps only under hypotheses). Mitigation: `fiberMultSum_eq_finset_sum` early,
   do all algebra at `Finset` level where possible; the two genuinely set-level steps
   (`finsum_mem_iUnion`, `finsum_mem_eq_of_bijOn`) are [spiked] with exactly the hypotheses
   we can supply (finiteness of each piece, disjointness, BijOn). Fallback: prove a private
   `Finset` analogue of the decomposition via `Finset.sum_biUnion`.
3. **Chart-invariance germ rewrite (MEDIUM, P2b).** The congruence
   `e' (F (e.symm z)) = z^k on e.target` must feed `analyticOrderAt_congr` as an
   `=ᶠ[𝓝 (e x)]` statement: `eventually_of_mem (e.open_target.mem_nhds …)`. Eta mismatches
   (`(fun z ↦ z^k - w)` vs `(· ^ k) · - …`): normalize with `simp only []`/`show` before
   `analyticOrderAt_congr`; never match syntactically. If local-multiplicity's chart
   invariance lands with a different LHS shape (their §4.4), adapt the congruence, not the
   architecture.
4. **`Fin n` enumeration plumbing (LOW-MEDIUM, P1.1).** `Finset.equivFin` composition and
   `range pt = fiber` conversions are fussy but standard; fallback: replace `Fin n` by the
   subtype `↥(F⁻¹' {y₀})` with `[Fintype]` from `Set.Finite` (then `finsum_mem_iUnion` still
   applies with `[Finite ι]`), at the cost of DecidableEq noise. The structure's interface
   would change — decide BEFORE building LocalConstancy (both files same builder, or agree
   on the signature first).
5. **`IsCoveringMapOn.of_openPartialHomeomorph` argument shape (LOW).** Explicit/implicit
   status of `f, s` verified by spike (explicit; `(h : ∀ e ∈ f ⁻¹' s, …)`). The coe-copy
   helper (P6.1) is self-contained. If anything breaks, `Covering.lean` is a leaf — nothing
   downstream in THIS project blocks on it except paths-and-integrals' optional
   mathlib-lifting route (they have a hand-rolled grid fallback per CC6).
6. **Instance perfectness clash (LOW).** `nhdsNE_neBot_of_chartedSpace` on `X := ℂ`
   overlaps mathlib's `nhdsNE_neBot`; both are Prop-valued instances (harmless); keep
   `priority := 100`. Fallback: demote to a lemma + `haveI` at the three use sites
   (Ramification density, Basics `not_eventuallyConst`, exists_isRegularValue).
7. **`degree_comp` scope creep (LOW).** It is statement-bank only (no downstream consumer in
   the challenge's critical path). If `[CompactSpace Y]` or the ℕ-finsum algebra fights,
   deliver the rest of Degree.lean and report; do NOT let it block the unit.

## 9. What is deliberately NOT here

- No `IsCoveringMap` on subtypes (mathlib's `restrictPreimage` gives it to consumers free).
- No Riemann–Hurwitz (needs canonical divisors; different unit).
- No `ordAtX`/divisor bridge (CC3-CC4 compat lives in local-multiplicity/meromorphic units).
- No path lifting/monodromy (mathlib's, over our `IsCoveringMapOn`, cited in root docstring).

## 10. Spike record (`scratch_mapdeg.lean`)

Run 2026-07-02, pinned toolchain, `lake env lean scratch_mapdeg.lean` after gating on the
3-lean semaphore. **Compiles clean, 5.9 s wall** (imports: `Topology.Covering.Basic`,
`RingTheory.RootsOfUnity.Complex`, `Algebra.BigOperators.Finprod`,
`Topology.LocallyConstant.Basic`, `Analysis.Analytic.Order`, `Data.Set.Card`). Verified by
re-typing exact statements (all marked **[spiked]** above):

1. `IsCompact.finite` + `isDiscrete_iff_nhdsNE` (exact hypothesis shapes);
2. `IsCoveringMapOn.of_openPartialHomeomorph hf h` with
   `h : ∀ e ∈ f ⁻¹' s, ∃ φ : OpenPartialHomeomorph E X, e ∈ φ.source ∧ ⇑φ = f` — coe equality
   is `⇑φ = f` (GLOBAL function equality), instance set
   `[T2Space E] [T2Space X] [CompactSpace E]` confirmed;
3. the FULL `ncard_setOf_pow_eq` proof (root set as `nthRoots` toFinset; card `k` via
   `Complex.isPrimitiveRoot_exp` + `card_nthRoots` + `nthRoots_nodup` +
   `Multiset.toFinset_card_of_nodup` + `Set.ncard_coe_finset`) and the exp/log k-th-root
   existence proof — compiled end-to-end;
4. `finsum_mem_iUnion`, `finsum_mem_eq_of_bijOn` (exact signatures);
5. `Set.Finite.t2_separation`;
6. fiber-trapping composite: `mem_comap.mp (hF.isClosedMap.comap_nhds_le hU)` from
   `hU : U ∈ 𝓝ˢ (F ⁻¹' {y})` yields `∃ W ∈ 𝓝 y, F ⁻¹' W ⊆ U` — one-liner;
7. `Continuous.homeoOfEquivCompactToT2` (implicit `{f : X ≃ Y}`);
8. `IsLocallyConstant.apply_eq_of_preconnectedSpace`;
9. ℂ-instance `(𝓝[≠] (z : ℂ)).NeBot` by `inferInstance`; `infinite_of_mem_nhds`;
10. `analyticOrderAt_pow`, `AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero`.

Gotchas found by the spike (folded into §4–§6):
- `IsCoveringMapOn.of_openPartialHomeomorph` takes `f`, `s` IMPLICITLY (a `variable {f s}`
  block at `Covering/Basic.lean:224` is still active at `:580`), despite the file-top
  `variable (f) (s)`.
- The lemma is `Set.ncard_coe_finset` (lowercase `finset`), `Data/Set/Card.lean:636`.
- `IsAlgClosed ℂ` is NOT available from this import set (the instance is the FTA,
  `Analysis/Complex/Polynomial/Basic.lean:50`); root existence must use the exp/log route
  (all pieces already in scope via `RootsOfUnity.Complex`).
- `Pairwise (Disjoint on t)` needs `open Function` for the `on` notation.
- `mul_div_cancel_left₀ (b) (ha : a ≠ 0) : a * b / a = b` after a `mul_div_assoc'` rewrite
  closes the `exp_nat_mul` bookkeeping; `field_simp` alone does NOT finish it.
