# Design: sphere-topology (`Jacobian/SphereTopology/`)

Blueprint entry: `clean_room_blueprint.md` §sphere-topology. Reference: Forster §10.5 (analytic
consequence of simple connectivity; page map `docs/refs/forster-map.md`) plus standard algebraic
topology for §1 (no textbook needed — the argument is elementary once the perturbation lemma is
in hand). **Builds on:** projective-line (CC5: `OnePoint ℂ`'s two-chart structure, `homeoSphere`),
paths-and-integrals (CC6: `pathIntegral`, homotopy invariance, `Loop.exists_homotopic_avoiding`),
holomorphic-forms (CC1: `Form1`, `coeffIn`, `mdifferential`, `genus`). No van Kampen anywhere —
per `docs/mathlib-inventory.md` §9, mathlib has no `SimplyConnectedSpace` instance for any sphere
and no topological Seifert–van Kampen usable directly; both are hand-built below from more
elementary mathlib pieces (`ContractibleSpace`/`LocPathConnectedSpace`/open-embedding transport
plus the paths unit's loop-perturbation lemma).

**All mathlib names below were verified by reading `.lake/packages/mathlib` source at the pin.
The full `SimplyConnectedSpace (OnePoint ℂ)` chain that does NOT depend on paths-and-integrals'
not-yet-built `Perturb.lean` was additionally spike-compiled (`scratch_sphtop.lean`, §6) against
the ALREADY-BUILT `Jacobian/ProjectiveLine/{Inversion,Charts}.lean` — compiles clean, 0 sorries.**

---

## 0. The two headline goals and why the plan closes

1. `SimplyConnectedSpace (OnePoint ℂ)`, transferred to any `X ≃ₜ` the challenge sphere.
2. `SimplyConnectedSpace X ⇒ genus X = 0` for our own standing surface `X` (its OWN complex
   structure, not `OnePoint ℂ`'s).

Item 2 is the mathematically substantial half (Forster 10.5: closed ⇒ exact on a simply connected
surface). It is proved here by building a *global* primitive of `η` directly from `pathIntegral`
plus simple connectivity — the "monodromy engine" in miniature, self-contained (design decision,
§4).

---

## 1. File plan

| # | File | Content | Est. lines |
|---|------|---------|-----------|
| 1 | `Jacobian/SphereTopology/SimplyConnectedP1.lean` | `SimplyConnectedSpace (OnePoint ℂ)` and its homeomorphism transfer | ~140 |
| 2 | `Jacobian/SphereTopology/GlobalPrimitive.lean` | The primitive-construction engine; `genus_eq_zero_of_simplyConnectedSpace` | ~220 |
| 3 | `Jacobian/SphereTopology/Headline.lean` | `genus_eq_zero_of_homeo_sphere` (the exact backward-headline signature) | ~30 |
| 4 | `Jacobian/SphereTopology.lean` | unit root, API docstring, register in `Jacobian.lean` | ~15 |

Import skeleton:
- File 1: `Jacobian.ProjectiveLine` (for `homeoSphere`, `inversionHomeomorph`, `coeChart`/
  `invChart` source lemmas — ALREADY BUILT), `Mathlib.AlgebraicTopology.FundamentalGroupoid.
  SimplyConnected`, `Mathlib.Analysis.Convex.Contractible`, `Mathlib.Topology.Connected.
  LocPathConnected`.
- File 2: `Jacobian.Path` (for `IsPrimitiveAlongMap`, `pathIntegral`, `Planar.exists_hasDerivAt_ball`
  — Path unit still in flight; consumes the *frozen* API in `docs/design/paths-and-integrals.md`),
  `Jacobian.Forms` (for `Form1`, `coeffIn`, `mdifferential`, `genus`), `Mathlib.Geometry.Manifold.
  Complex` (for `MDifferentiable.exists_eq_const_of_compactSpace`).
- File 3: Files 1+2 + `Jacobian.ProjectiveLine` (`homeoSphere`).

Standing surface variables for files 2–3 (verbatim per `CONVENTIONS.md`):
```lean
open scoped ContDiff Manifold
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
```
File 1 needs no standing surface variable — it is entirely about `OnePoint ℂ` and generic
homeomorphism transport.

---

## 2. Step 1 — `SimplyConnectedSpace (OnePoint ℂ)`

### 2.1 Why no van Kampen is needed

The task brief's hint is exactly right and pays off cleanly: for a loop `γ` in `OnePoint ℂ`,
**perturb it off the single point `∞`** (paths-and-integrals' `Loop.exists_homotopic_avoiding`
perturbs off any *finite* set — `{∞}` is finite), then note `OnePoint ℂ \ {∞} ≅ ℂ` is
contractible, hence simply connected, hence the perturbed loop is nullhomotopic **inside**
`{∞}ᶜ`; being nullhomotopic inside a subspace of `OnePoint ℂ` gives a nullhomotopy in
`OnePoint ℂ` itself (`isSimplyConnected_iff_exists_homotopy_refl_forall_mem`, mathlib, exact
statement below). Composed with the original perturbation homotopy, `γ` itself is nullhomotopic.

One wrinkle the naive plan misses (flagged in the task brief as something to design around):
**the loop's *basepoint* might be `∞` itself**, in which case it cannot be perturbed off `{∞}`
(a based homotopy fixes the basepoint throughout). Fix: use the atlas's OTHER point/chart. If
the basepoint `x ≠ ∞`, perturb off `S := {∞}`. If `x = ∞`, perturb off `S := {↑(0:ℂ)}` instead
(the other named point of the two-chart atlas) — `{↑0}ᶜ` is *also* contractible (swap `∞ ↔ ↑0`
via `RS.P1.inversionHomeomorph`, already built). Two symmetric cases, no basepoint-conjugation
machinery needed.

### 2.2 Exported signatures (`SimplyConnectedP1.lean`)

```lean
namespace RS.SphereTopology
open scoped ContDiff Manifold OnePoint
open Set Topology OnePoint RS RS.P1

/-- Both "polar caps" of the two-chart atlas are simply connected: they are each
homeomorphic to `ℂ` (contractible), via the open embedding `(↑) : ℂ → OnePoint ℂ` for `{∞}ᶜ`
and via `inversionHomeomorph` swapping `∞ ↔ ↑0` for `{↑0}ᶜ`. -/
theorem isSimplyConnected_compl_infty : IsSimplyConnected ({(∞ : OnePoint ℂ)}ᶜ)
theorem isSimplyConnected_compl_coeZero :
    IsSimplyConnected ({((0 : ℂ) : OnePoint ℂ)}ᶜ)

/-- `OnePoint ℂ` is path connected (local path-connectedness transports through the
already-built two-chart atlas from `ℂ`'s local convexity; combined with the existing
`ConnectedSpace (OnePoint ℂ)` instance). -/
instance : PathConnectedSpace (OnePoint ℂ)

/-- **The headline of this file**: no van Kampen, no universal cover — assembled from the
perturbation lemma + the two polar-cap facts above. -/
instance simplyConnectedSpace_onePoint : SimplyConnectedSpace (OnePoint ℂ)

/-- Homeomorphism transfer (generic; consumed directly by `Headline.lean`, and by anything
that produces `X ≃ₜ OnePoint ℂ`, e.g. `X ≃ₜ` challenge-sphere composed with `homeoSphere.symm`). -/
theorem simplyConnectedSpace_of_homeoOnePoint {X : Type*} [TopologicalSpace X]
    (e : X ≃ₜ OnePoint ℂ) : SimplyConnectedSpace X

/-- Same fact stated for the literal challenge sphere type, for convenience/reuse. -/
instance simplyConnectedSpace_sphere :
    SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)

end RS.SphereTopology
```

### 2.3 Proof plans

**`isSimplyConnected_compl_infty`.** Chain (all four steps spike-verified, §6 items 1–4):
1. `ContractibleSpace ℂ` is `inferInstance`
   (`RealTopologicalVectorSpace.contractibleSpace`, `Analysis/Convex/Contractible.lean:39` — via
   `NormedSpace.toLocallyConvexSpace` + `Convex.contractibleSpace` on `Set.univ`).
2. `SimplyConnectedSpace ℂ` is `inferInstance`
   (`SimplyConnectedSpace.ofContractible`, `FundamentalGroupoid/SimplyConnected.lean:77`,
   priority-100 instance).
3. `IsSimplyConnected (Set.univ : Set ℂ) := (Homeomorph.Set.univ ℂ).toHomotopyEquiv.
   simplyConnectedSpace` — `Homeomorph.Set.univ (X) : (univ : Set X) ≃ₜ X`
   (`Topology/Homeomorph/Lemmas.lean:347`); `Homeomorph.toHomotopyEquiv`
   (`Topology/Homotopy/Equiv.lean:75`); `ContinuousMap.HomotopyEquiv.simplyConnectedSpace
   [hY : SimplyConnectedSpace Y] (e : X ≃ₕ Y) : SimplyConnectedSpace X`
   (`FundamentalGroupoid/SimplyConnected.lean:52`) — **direction matters**: `e : ↥univ ≃ₕ ℂ`
   (domain `↥univ`, codomain `ℂ`), so this concludes `SimplyConnectedSpace ↥univ =
   IsSimplyConnected univ` from the known `SimplyConnectedSpace ℂ`; do NOT take `.symm`.
4. Transport across the open embedding: `OnePoint.isOpenEmbedding_coe : IsOpenEmbedding
   ((↑) : ℂ → OnePoint ℂ)` (`Compactification/OnePoint/Basic.lean:271`); `Topology.IsEmbedding.
   isSimplyConnected_image {f} (hf : IsEmbedding f) {s} : IsSimplyConnected (f '' s) ↔
   IsSimplyConnected s` (`FundamentalGroupoid/SimplyConnected.lean:145`) with
   `f := (↑)`, `s := univ`; `Set.image_univ : f '' univ = range f`; `OnePoint.compl_infty :
   ({∞}ᶜ : Set (OnePoint X)) = range (↑)` (`:144`) rewrites the conclusion to `{∞}ᶜ`.

**`isSimplyConnected_compl_coeZero`.** Reduce to the previous fact by symmetry, reusing the
ALREADY-BUILT `RS.P1.inversionHomeomorph : OnePoint ℂ ≃ₜ OnePoint ℂ` (self-inverse, swaps
`∞ ↔ ↑0` — `inversion_infty`, `inversion_eq_infty_iff`, `Jacobian/ProjectiveLine/Inversion.lean`):
`{↑0}ᶜ = inversionHomeomorph ⁻¹' {∞}ᶜ` (`Set.preimage_compl` + `inversion_eq_infty_iff` on
singletons — an unconditional preimage identity, no bijectivity juggling needed), then
`Homeomorph.isSimplyConnected_preimage (f : X ≃ₜ Y) {s : Set Y} : IsSimplyConnected (f ⁻¹' s) ↔
IsSimplyConnected s` (`FundamentalGroupoid/SimplyConnected.lean:156`, `.mpr` direction) closes it
from `isSimplyConnected_compl_infty`.

**`PathConnectedSpace (OnePoint ℂ)`.** NOT built via an explicit "path to infinity" (unnecessary
engineering) — instead purely local: `ChartedSpace.locPathConnectedSpace (H) (M)
[LocPathConnectedSpace H] : LocPathConnectedSpace M` (`Geometry/Manifold/ChartedSpace.lean:268`,
the *exact* path-connected analogue of the already-used `.locallyConnectedSpace`/
`.locallyCompactSpace` manifold-inheritance lemmas) with `H := ℂ`, `M := OnePoint ℂ`, consuming
the ALREADY-BUILT `RS.P1.instChartedSpace : ChartedSpace ℂ (OnePoint ℂ)`
(`Jacobian/ProjectiveLine/Charts.lean:140`); `LocPathConnectedSpace ℂ` is `inferInstance`
(`LocallyConvexSpace.toLocPathConnectedSpace`, `Topology/Algebra/Module/LocallyConvex.lean:103`,
via `NormedSpace.toLocallyConvexSpace`). Then `PathConnectedSpace.of_locPathConnectedSpace
[ConnectedSpace X] : PathConnectedSpace X` (`Topology/Connected/LocPathConnected.lean:130`) closes
it, consuming the ALREADY-EXISTING `ConnectedSpace (OnePoint ℂ)` instance (projective-line design
CC5, `inferInstance` from `PreconnectedSpace ℂ` + `NoncompactSpace ℂ`).

**`simplyConnectedSpace_onePoint` (the assembly).**
`rw [simplyConnectedSpace_iff]`? — no: use
`simply_connected_iff_loops_nullhomotopic : SimplyConnectedSpace Y ↔ PathConnectedSpace Y ∧
∀ (x : Y) (γ : Path x x), Path.Homotopic γ (Path.refl x)`
(`FundamentalGroupoid/SimplyConnected.lean:104`). First component: the `PathConnectedSpace`
instance above. Second: fix `x`, `γ : Path x x`.
- **Case `x ≠ ∞`.** Apply `Loop.exists_homotopic_avoiding γ (S := {(∞ : OnePoint ℂ)})
  (Set.finite_singleton _) (by simpa using hx) : ∃ γ', γ.Homotopic γ' ∧
  Disjoint (Set.range ⇑γ') {∞}` (paths-and-integrals `Perturb.lean`, frozen signature). From
  `Disjoint`, `∀ t, γ' t ∈ ({∞}ᶜ : Set (OnePoint ℂ))` (`Set.disjoint_left`). Apply
  `isSimplyConnected_iff_exists_homotopy_refl_forall_mem` (mathlib,
  `FundamentalGroupoid/SimplyConnected.lean:162`) `.mp isSimplyConnected_compl_infty |>.2 x γ' hmem`
  to get `F : γ'.Homotopy (.refl x)`, i.e. `γ'.Homotopic (.refl x) := ⟨F⟩`. Transitivity
  (`Path.Homotopic` is an equivalence relation, `@[trans]`) gives `γ.Homotopic (.refl x)`.
- **Case `x = ∞`.** Identical with `S := {((0:ℂ):OnePoint ℂ)}` (valid: `∞ ≠ ↑0` —
  `OnePoint.infty_ne_coe`) and `isSimplyConnected_compl_coeZero`.

**`simplyConnectedSpace_of_homeoOnePoint`.** `e.toHomotopyEquiv.simplyConnectedSpace` directly
(`e : X ≃ₕ OnePoint ℂ`, codomain known simply connected — same direction-check as step 3 above:
domain gets the conclusion).

**`simplyConnectedSpace_sphere`.** `simplyConnectedSpace_of_homeoOnePoint RS.P1.homeoSphere.symm`
(`homeoSphere : OnePoint ℂ ≃ₜ sphere`, so `.symm : sphere ≃ₜ OnePoint ℂ` is the `X ≃ₜ OnePoint ℂ`
shape needed with `X := sphere`).

---

## 3. Step 2 — simply connected compact surface has genus 0

### 3.1 Design decision: the self-contained primitive engine

Forster 10.5's argument is: fix a base point `x₀`, define `f(x) := ∫` (any path `x₀⤳x`) `η`,
well-defined by simple connectivity + homotopy invariance; `f` is holomorphic; on a compact
connected `X` a holomorphic function is constant (`MDifferentiable.exists_eq_const_of_compactSpace`,
Liouville-flavoured, `Geometry/Manifold/Complex.lean:172`); hence `df = η = 0`.

The middle step ("`f` is holomorphic and `df = η`") is *exactly* what the monodromy unit (#21)
will later provide in general (discrete continuation, no integration) — but monodromy **builds
on** sphere-topology in the DAG, so this unit cannot borrow from it. Per the task brief's design
mandate, the cleanest self-contained route reuses paths-and-integrals' own vocabulary almost
verbatim: **a global primitive of `η` is precisely a primitive of `η` "along the identity map on
`X`"** — i.e. an instance of paths' own `IsPrimitiveAlongMap (id : X → X) η f Set.univ` predicate
with `K := id`. Once phrased this way, the bridge "`IsPrimitiveAlongMap id η f univ` ⇒ `f` is
`ContMDiff` and `mdifferential f _ = η`" is a ~40-line consequence of paths' own exported
`IsPrimitiveAlongMap.rechart` plus Forms' `coeffIn_mdifferential`/`Form1.ext_coeffAt` — no new
integration theory, no covering-space machinery. **Note for the monodromy unit**: the pair
`(exists_isPrimitiveAlongMap_id, contMDiff_and_mdifferential_eq_of_isPrimitiveAlongMap_id)` below
is exactly the "primitive on simply-connected `X`" engine that monodromy's discrete-continuation
route re-derives by a different (chain-of-charts, no integration) method for the *unconditional*
(not-necessarily-simply-connected, chain-based) case; monodromy should feel free to either reuse
`contMDiff_and_mdifferential_eq_of_isPrimitiveAlongMap_id` verbatim (it only needs
`IsPrimitiveAlongMap id η F univ` as input, regardless of how that hypothesis was established) or
re-derive it — they are not required to depend on this unit for it.

### 3.2 Exported signatures (`GlobalPrimitive.lean`)

```lean
namespace RS.SphereTopology
open scoped ContDiff Manifold
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The "monodromy engine" atom: a primitive of `η` along the identity map is a genuine
holomorphic global primitive, and it IS `η`'s antiderivative in Forms' sense. Reusable verbatim
by the monodromy unit once it has established `IsPrimitiveAlongMap id η F univ` by its own
(chain-continuation) means. -/
theorem contMDiff_and_mdifferential_eq_of_isPrimitiveAlongMap_id
    {η : RS.Form1 X} {F : X → ℂ}
    (hF : RS.IsPrimitiveAlongMap (id : X → X) η F Set.univ) :
    ∃ hF' : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F, RS.mdifferential F hF' = η

/-- Construction of the global primitive on a simply connected `X`, via `pathIntegral` from a
fixed base point (well-defined by `pathIntegral_eq_of_simplyConnected`). -/
theorem exists_isPrimitiveAlongMap_id [SimplyConnectedSpace X] (x₀ : X) (η : RS.Form1 X) :
    ∃ F : X → ℂ, RS.IsPrimitiveAlongMap (id : X → X) η F Set.univ ∧ F x₀ = 0

/-- **Forster 10.5.** On a simply connected compact surface every holomorphic 1-form vanishes. -/
theorem form1_eq_zero_of_simplyConnectedSpace [SimplyConnectedSpace X] (η : RS.Form1 X) : η = 0

instance [SimplyConnectedSpace X] : Subsingleton (RS.Form1 X)
  -- `⟨fun η η' => sub_eq_zero.mp (form1_eq_zero_of_simplyConnectedSpace (η - η'))⟩`

/-- The step-2 headline. -/
theorem genus_eq_zero_of_simplyConnectedSpace [SimplyConnectedSpace X] : genus X = 0

end RS.SphereTopology
```

### 3.3 Proof plans

**`exists_isPrimitiveAlongMap_id`.** Fix `x₀` (arbitrary — `X` is `Nonempty` via `ConnectedSpace`).
Since `[SimplyConnectedSpace X]`, `PathConnectedSpace X` is an instance, so
`PathConnectedSpace.joined x₀ x : Joined x₀ x` for every `x`, and `F x := pathIntegral
(PathConnectedSpace.joined x₀ x).somePath η` (`Joined.somePath`, `Topology/Connected/
PathConnected.lean:70`); `F x₀ = 0` (`pathIntegral` of a path homotopic-to-refl is `0`, or just
choose `(Joined.refl x₀).somePath = Path.refl x₀` — cheapest: prove `F x₀ = pathIntegral
(Path.refl x₀) η = 0` via `pathIntegral_refl`, using well-definedness (below) to swap in
`Path.refl x₀` regardless of which path `somePath` picked).

Well-definedness / the local factorization, at an arbitrary `x`: let `e := chartAt ℂ x`,
`c := e x`; pick `r > 0` with `ball c r ⊆ e.target` (`Metric.isOpen_iff.mp e.open_target`).
`Form1.analyticOnNhd_coeffIn η (subset_maximalAtlas (chart_mem_atlas ℂ x)) : AnalyticOnNhd ℂ
(coeffIn e η) e.target`, restricted to the ball. Apply paths' `Planar.exists_hasDerivAt_ball`
(`hb := ball_subset`, `hz₀ := mem c r`, `z₀ := c`, `w := F x`) to get `g : ℂ → ℂ` with `g c = F x`
and `∀ z ∈ ball c r, HasDerivAt g (coeffIn e η z) z`.

**Claim:** for `y` in the open set `U := e.source ∩ e ⁻¹' (ball c r)` (∋ `x`, since `e x = c ∈
ball c r`), `F y = g (e y)`. Proof: build the *chart-local straight path* `δ_y := e.symm ∘
(t ↦ c + t • (e y − c))` on `I` (well-defined: the affine segment lies in `ball c r ⊆ e.target`
by convexity, so `e.symm` — continuous on target — composes to a genuine `Continuous`
`I → X` via `ContinuousOn.comp_continuous`; `δ_y 0 = x`, `δ_y 1 = y` by `e.left_inv'`). Since the
*whole* path stays in the single chart+ball `(e, g)`, `IsPrimitiveAlongMap δ_y.extend η
(g ∘ e ∘ δ_y.extend) Set.univ` holds with the SAME data `(e, g)` at every parameter (no gluing
needed — this is the degenerate one-piece case of paths' own `exists_isPrimitiveAlong`
induction). Hence `pathIntegral δ_y η = g (e y) − g (e x) = g(e y) − F x`
(`IsPrimitiveAlong.pathIntegral_eq`). By `pathIntegral_trans` and path-independence
(`pathIntegral_eq_of_simplyConnected`, since `X` is simply connected, EVERY path `x₀ ⤳ y`
computes `F y`, in particular the concatenation): `F y = pathIntegral ((somePath x₀ x).trans
δ_y) η = pathIntegral (somePath x₀ x) η + pathIntegral δ_y η = F x + (g(e y) − F x) = g(e y)`.

This proves `∀ᶠ y in 𝓝 x, y ∈ e.source ∧ F y = g (e y)` (the set `U` is an open neighbourhood of
`x` witnessing this), which together with `(e, g)`'s `HasDerivAt`/analyticity data is exactly
`IsPrimitiveAlongMap id η F Set.univ`'s defining data at `x` (recall `𝓝[univ] x = 𝓝 x`,
`nhdsWithin_univ`). Since `x` was arbitrary, `IsPrimitiveAlongMap id η F Set.univ` holds. ∎

**`contMDiff_and_mdifferential_eq_of_isPrimitiveAlongMap_id`.** Fix `x`. Rechart `hF`'s data at
`x` into the PREFERRED chart via the ALREADY-EXPORTED `IsPrimitiveAlongMap.rechart hF
(Set.mem_univ x) (continuous_id.continuousWithinAt) (IsManifold.subset_maximalAtlas
(chart_mem_atlas ℂ x)) (mem_chart_source ℂ x)`: get `g' : ℂ → ℂ` with
`∀ᶠ z in 𝓝 (chartAt ℂ x x), HasDerivAt g' (coeffIn (chartAt ℂ x) η z) z` and (using
`𝓝[univ] x = 𝓝 x`, `id y = y`) `F =ᶠ[𝓝 x] g' ∘ chartAt ℂ x`.
1. **`g'` is `AnalyticAt` at `chartAt ℂ x x`**: `∀ᶠ z in 𝓝 c, HasDerivAt g' (_) z` gives
   `DifferentiableOn ℂ g' (ball c ε)` for a small `ε` (`Metric.eventually_nhds_iff_ball`), hence
   `AnalyticOnNhd ℂ g' (ball c ε)` (`DifferentiableOn.analyticOnNhd`, `CauchyIntegral.lean:632`,
   as already used in Forms' Montel proof), hence `AnalyticAt` at the center.
2. **Push through the chart**: `(chartAt ℂ x).symm` is `ContinuousAt` at `chartAt ℂ x x` with
   value `x` (chart data); composing the filter map with `F =ᶠ[𝓝 x] g' ∘ chartAt ℂ x` gives
   `F ∘ (chartAt ℂ x).symm =ᶠ[𝓝 (chartAt ℂ x x)] g' ∘ chartAt ℂ x ∘ (chartAt ℂ x).symm = g'`
   (the last step by the chart's `right_inv'` on the open target, eventually near the point).
   `AnalyticAt.congr` transfers analyticity to `F ∘ (chartAt ℂ x).symm` at `chartAt ℂ x x`.
3. **Holomorphy**: Forms' `contMDiffAt_iff_analyticAt_comp` (§2.2 of `holomorphic-forms.md`,
   with `F := ℂ`) converts step 2 into `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x`. Since `x` was arbitrary,
   `hF' : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F := fun x => ‹ContMDiffAt … x›` (`ContMDiff` unfolds to `∀ x,
   ContMDiffAt … x` definitionally, `ContMDiff/Defs.lean:203`).
4. **Coefficient matching**: `coeffIn_mdifferential (subset_maximalAtlas (chart_mem_atlas ℂ x))
   hF' : Set.EqOn (coeffIn (chartAt ℂ x) (mdifferential F hF')) (deriv (F ∘ (chartAt ℂ x).symm))
   (chartAt ℂ x).target`; at `z := chartAt ℂ x x`, `deriv (F∘(chartAt ℂ x).symm) z = deriv g' z`
   (congr, step 2) `= coeffIn (chartAt ℂ x) η z` (`HasDerivAt.deriv` applied to `g'`'s defining
   property AT `z` itself). So `coeffAt x (mdifferential F hF') = coeffAt x η` for every `x`.
5. `Form1.ext_coeffAt` (Forms, `Coeffs.lean:201`) closes `mdifferential F hF' = η`. ∎

**`form1_eq_zero_of_simplyConnectedSpace`.** Combine: obtain `F` from
`exists_isPrimitiveAlongMap_id (Classical.arbitrary X) η` (`Nonempty X` from `ConnectedSpace`);
obtain `⟨hF', hFη⟩` from `contMDiff_and_mdifferential_eq_of_isPrimitiveAlongMap_id` applied to
`F`'s `IsPrimitiveAlongMap` fact. `hF'.mdifferentiable (n ≠ 0 : since n = ω is `⊤`)
: MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F` (`ContMDiff.mdifferentiable`, `Geometry/Manifold/MFDeriv/
Basic.lean:493`); with `[CompactSpace X] [ConnectedSpace X]` (⇒ `PreconnectedSpace X`),
`IsManifold 𝓘(ℂ) 1 X` (`inferInstance`, `IsManifold.of_le`/the `[IsManifold I ω M] :
IsManifold I a M` instance at `IsManifold/Basic.lean:857`, since `1 ≤ ω = ⊤`), and
`𝓘(ℂ).Boundaryless` (`modelWithCornersSelf_boundaryless`, `IsManifold/Basic.lean:613`, always an
instance for a self-model): `MDifferentiable.exists_eq_const_of_compactSpace
(Geometry/Manifold/Complex.lean:172) : ∃ v, F = Function.const X v`. Substitute:
`mdifferential F hF' = mdifferential (Function.const X v) hF'' = 0` (`mdifferential_const`,
`Jacobian/Forms/MDifferential.lean:104`, already built). Combined with `hFη`: `η = 0`. ∎

**`genus_eq_zero_of_simplyConnectedSpace`.** `Subsingleton (Form1 X)` from
`form1_eq_zero_of_simplyConnectedSpace` (any two forms' difference is `0`, i.e. they're equal —
`Form1` is an `AddCommGroup`, so `η = η' ↔ η - η' = 0`). Then `genus_eq_zero_iff_subsingleton`
(Forms, `Genus.lean:31`, already built) `.mpr` closes it. ∎

---

## 4. Step 3 — the backward headline assembly (`Headline.lean`)

```lean
namespace RS.SphereTopology
open scoped ContDiff Manifold
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The backward headline half (consumed by `genus-zero-headline` alongside Riemann–Roch's
forward half). Only `X`'s TOPOLOGY is used to get `SimplyConnectedSpace X`; `genus X = 0` then
uses `X`'s OWN complex structure via `GlobalPrimitive.lean` — consistent, since `Form1 X`/`genus X`
are defined from `X`'s own atlas, not from the sphere's. -/
theorem genus_eq_zero_of_homeo_sphere
    (h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) : genus X = 0 := by
  obtain ⟨e⟩ := h
  haveI : SimplyConnectedSpace X :=
    simplyConnectedSpace_of_homeoOnePoint (e.trans RS.P1.homeoSphere.symm)
  exact genus_eq_zero_of_simplyConnectedSpace

end RS.SphereTopology
```

Proof: `e.trans RS.P1.homeoSphere.symm : X ≃ₜ OnePoint ℂ` (compose with the ALREADY-BUILT
`RS.P1.homeoSphere : OnePoint ℂ ≃ₜ sphere`, `.symm` reverses it); feed into
`simplyConnectedSpace_of_homeoOnePoint` (§2.2); then Step 2's headline. Three lines.

---

## 5. Verified mathlib/project names (summary table)

| Fact | Name / location | Status |
|---|---|---|
| `SimplyConnectedSpace` class, `equiv_unit` field | `AlgebraicTopology/FundamentalGroupoid/SimplyConnected.lean:38` | read |
| `simply_connected_iff_loops_nullhomotopic` | `:104` | read |
| `isSimplyConnected_iff_exists_homotopy_refl_forall_mem` | `:162` | read |
| `SimplyConnectedSpace.ofContractible` | `:77` | read |
| `ContinuousMap.HomotopyEquiv.simplyConnectedSpace`/`_iff` | `:52`/`:56` | **spiked** |
| `Topology.IsEmbedding.isSimplyConnected_image` | `:145` | **spiked** |
| `Homeomorph.isSimplyConnected_image`/`_preimage` | `:151`/`:156` | **spiked** |
| `RealTopologicalVectorSpace.contractibleSpace` | `Analysis/Convex/Contractible.lean:39` | **spiked** (`inferInstance`) |
| `Homeomorph.contractibleSpace`/`_iff`, `.toHomotopyEquiv` | `Topology/Homotopy/Contractible.lean:89/:93`, `Homotopy/Equiv.lean:75` | read |
| `Homeomorph.Set.univ` | `Topology/Homeomorph/Lemmas.lean:347` | **spiked** |
| `LocallyConvexSpace.toLocPathConnectedSpace` | `Topology/Algebra/Module/LocallyConvex.lean:103` | read (feeds `LocPathConnectedSpace ℂ` `inferInstance`) |
| `ChartedSpace.locPathConnectedSpace` | `Geometry/Manifold/ChartedSpace.lean:268` | **spiked** |
| `PathConnectedSpace.of_locPathConnectedSpace` | `Topology/Connected/LocPathConnected.lean:130` | **spiked** |
| `OnePoint.isOpenEmbedding_coe`, `.compl_infty`, `Set.image_univ` | `Compactification/OnePoint/Basic.lean:271/:144` | **spiked** |
| `Joined.somePath`, `PathConnectedSpace.joined` | `Topology/Connected/PathConnected.lean:70`/(class field) | read |
| `MDifferentiable.exists_eq_const_of_compactSpace` | `Geometry/Manifold/Complex.lean:172` | read (also cited by meromorphic-and-divisors design) |
| `ContMDiff.mdifferentiable` | `Geometry/Manifold/MFDeriv/Basic.lean:493` | read |
| `modelWithCornersSelf_boundaryless` | `IsManifold/Basic.lean:613` | read |
| `instance [IsManifold I ω M] : IsManifold I a M` (order monotonicity) | `IsManifold/Basic.lean:857` | read |
| `DifferentiableOn.analyticOnNhd` | `Analysis/Complex/CauchyIntegral.lean:632` | read (cited by Forms' own Montel proof) |
| **Project (already built):** `RS.P1.homeoSphere`, `.inversionHomeomorph`, `.instChartedSpace`, `coeChart`/`invChart` + source/target simp lemmas | `Jacobian/ProjectiveLine/{Inversion,Charts}.lean` | **spiked against real files** |
| **Project (frozen design, Path unit in flight):** `IsPrimitiveAlongMap`, `.rechart`, `Planar.exists_hasDerivAt_ball`, `pathIntegral`, `pathIntegral_trans`, `pathIntegral_eq_of_simplyConnected`, `Loop.exists_homotopic_avoiding` | `docs/design/paths-and-integrals.md` §2–7 | design-only (not yet built) |
| **Project (already built):** `Form1`, `coeffIn`, `coeffIn_mdifferential`, `mdifferential_const`, `Form1.ext_coeffAt`, `Form1.analyticOnNhd_coeffIn`, `genus`, `genus_eq_zero_iff_subsingleton` | `Jacobian/Forms/*.lean` | **spiked against real files** (names) |

---

## 6. Spike record (`scratch_sphtop.lean`, project root, gitignored)

Gate respected (0 concurrent `lean` processes). `lake env lean scratch_sphtop.lean`: **compiles
clean, ~5 s wall, 0 sorries.** Imports `Jacobian.ProjectiveLine.Charts` (already-built project
file) + the four mathlib files above. Verified by full term/tactic proof (not just `#check`):

1. `ContractibleSpace ℂ` / `SimplyConnectedSpace ℂ` — both `inferInstance`.
2. `IsSimplyConnected (Set.univ : Set ℂ)` via `(Homeomorph.Set.univ ℂ).toHomotopyEquiv.
   simplyConnectedSpace` (no `.symm` — confirmed the direction the wrong way round fails to
   elaborate: `SimplyConnectedSpace ↑univ` instance-search failure was the first compile error,
   fixed by dropping `.symm`).
3. `IsSimplyConnected ({(∞ : OnePoint ℂ)}ᶜ)` via `isOpenEmbedding_coe.isEmbedding.
   isSimplyConnected_image` + `Set.image_univ` + `compl_infty` (rewriting the GOAL, not the
   hypothesis — the first attempt rewrote the wrong side and failed).
4. `PathConnectedSpace (OnePoint ℂ)` via `ChartedSpace.locPathConnectedSpace ℂ (OnePoint ℂ)` +
   `PathConnectedSpace.of_locPathConnectedSpace`, consuming the real
   `RS.P1.instChartedSpace`/`ConnectedSpace (OnePoint ℂ)` instances from the in-tree
   `Jacobian/ProjectiveLine/Charts.lean`.
5. `IsSimplyConnected ({((0:ℂ):OnePoint ℂ)}ᶜ)` via the `inversionHomeomorph`-preimage swap
   (`Set.preimage_compl` + `inversion_eq_infty_iff`, `Homeomorph.isSimplyConnected_preimage`),
   consuming the real `RS.P1.inversionHomeomorph`/`inversion_eq_infty_iff`/`inversionHomeomorph_apply`
   from `Jacobian/ProjectiveLine/Inversion.lean`.

Not spiked (depends on paths-and-integrals' not-yet-built `Perturb.lean`/`Continuation.lean`, so
no compilable target exists yet): the `Loop.exists_homotopic_avoiding`-based assembly of
`simplyConnectedSpace_onePoint`, and all of §3 (`GlobalPrimitive.lean`). Both are designed against
paths-and-integrals' *frozen* signatures (`docs/design/paths-and-integrals.md` §2, §3.2, §7) and
Forms' *already-built* files (names double-checked by `grep` against the real
`Jacobian/Forms/*.lean` sources, §5 table) — risk is concentrated in ordinary filter/chart
bookkeeping (§7 R1–R3 below), not in unresolved mathlib-name uncertainty.

---

## 7. Risks & fallbacks

- **R1 (Perturb.lean scheduling).** `simplyConnectedSpace_onePoint` needs
  `Loop.exists_homotopic_avoiding`, which is the LAST file of paths-and-integrals' plan (highest
  risk item there per its own R4). If it slips, this unit's Step 1 blocks; Step 2
  (`GlobalPrimitive.lean`) does NOT depend on Step 1 and can be built and checked independently
  (it only needs `[SimplyConnectedSpace X]` as a hypothesis, not a specific instance). Mitigation:
  build/check files in the order 2, 3(stmt only, sorry the `SimplyConnectedSpace X` step), 1 —
  or just wait; nothing else in the blueprint's DAG needs Step 1 before monodromy/genus-zero-headline.
- **R2 (the `IsPrimitiveAlongMap id η F univ` construction, §3.3).** The chart-local straight-path
  `δ_y` and its one-piece `IsPrimitiveAlongMap` fact is new code (not literally exported by
  paths-and-integrals) but mirrors EXACTLY the base case of that unit's own
  `exists_isPrimitiveAlong` induction (`Continuation.lean` design §3.2) and the affine-segment
  constructions already used in `Planar.exists_homotopy_range_subset_of_convex` and `Perturb.lean`
  §7 step 1 — same techniques, different assembly. If `IsPrimitiveAlongMap.rechart`'s exact
  filter-transport shape drifts from the frozen design, only this proof (not the exported
  signatures) needs adjustment.
- **R3 (order-monotonicity/`Boundaryless` plumbing for `exists_eq_const_of_compactSpace`).** All
  three side instances (`IsManifold 𝓘(ℂ) 1 X`, `𝓘(ℂ).Boundaryless`, `n ≠ 0` for `n = ω`) were
  confirmed as `inferInstance`/trivial from reading `IsManifold/Basic.lean` directly (§5 table);
  low risk, but if `ω ≠ 0` needs an explicit `WithTop`-order lemma instead of `decide`/`norm_num`,
  fall back to the same proof P1's `Holomorphy.lean` uses for its own `ω`-vs-order bookkeeping
  (`ContMDiffMFDeriv.lean:225`'s `hmn : ω + 1 ≤ ω` note in `docs/design/holomorphic-forms.md`
  §2.4 — same `ℕ∞ω` order facts).
- **R4 (basepoint case split, §2.3).** The `x = ∞` vs `x ≠ ∞` split is two symmetric copies of
  the same argument; if it turns out cleaner to unify via a single "some point ≠ x" lemma using
  `Nontrivial`/an explicit third point, that is a strictly optional simplification, not a
  correctness risk (both branches are independently spiked-adjacent, §6 items 3/5).
- **R5 (constancy lemma naming).** `MDifferentiable.exists_eq_const_of_compactSpace` is also
  relied on by `meromorphic-and-divisors` (`docs/design/meromorphic-and-divisors.md` line 157) —
  cross-checked, same name, same instance set (`IsManifold I 1 M`, `I.Boundaryless`,
  `[CompactSpace M] [PreconnectedSpace M]`); no drift risk between units.

---

## 8. Downstream map

- **genus-zero-headline** consumes exactly `RS.SphereTopology.genus_eq_zero_of_homeo_sphere`
  (item 3/Step 3) — the backward half of `genus X = 0 ↔ X ≃ₜ S²`, to be paired with
  Riemann–Roch's forward half (`l(D) ≥ deg D + 1 − g` at a single point ⇒ degree-1 map ⇒ homeo).
- **monodromy (unit 21)** may reuse
  `RS.SphereTopology.contMDiff_and_mdifferential_eq_of_isPrimitiveAlongMap_id` verbatim (it only
  needs an `IsPrimitiveAlongMap id η F univ` fact, however obtained — monodromy's own chain
  continuation produces exactly this kind of fact by a different, non-integration route on a
  general simply connected `X`, so the "engine" half is shared even though monodromy will NOT
  literally import this unit for it, per the blueprint's dependency direction — sphere-topology
  builds on projective-line only, and monodromy builds on sphere-topology, so if monodromy wants
  to import this lemma, that edge is free to add; if it prefers full independence, re-deriving
  ~40 lines from the same atoms is also fine. Either way, **no design incompatibility**: both
  routes conclude `∃ hF', mdifferential F hF' = η` from the same kind of local data.)
- **abel-theorem / period-lattice-rank**: no direct consumption (those units reach simple
  connectivity arguments, if any, through Abel's dissection-free route per the blueprint, not
  through this unit).
- Nothing else in the blueprint DAG depends on sphere-topology (blueprint: monodromy and
  genus-zero-headline are the only two direct consumers).

---

## 9. What this unit does NOT do

Van Kampen (categorical or classical) — deliberately avoided. Universal covers. `π₁(S¹) ≅ ℤ` or
any covering-space monodromy (mathlib's `Topology/Homotopy/Lifting.lean` machinery is not used —
the perturbation-lemma route sidesteps it entirely, matching paths-and-integrals' own routing
note in its §5 that covering-space monodromy is "overkill here"). The *general* (not-necessarily-
simply-connected) primitive/monodromy theorem — that is unit 21's job; this unit only needs and
proves the simply-connected special case for its own `X`.
