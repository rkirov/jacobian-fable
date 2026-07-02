# Design: local-multiplicity (`Jacobian/LocalMultiplicity/`)

Blueprint unit **local-multiplicity** (foundation; no project dependencies). Implements **CC4**
(frozen): local multiplicity of a holomorphic map between Riemann surfaces, defined through
`analyticOrderAt` in the standard charts, plus the planar `z^k · unit` machinery it rides on.
References: Forster §2 Thm 2.1 + Remark 2.2 (book p. 10 = PDF 16) — the local normal form
`F(z) = z^k` in adapted charts — and Forster §4; Miranda Ch. II (multiplicity via normal form).

Everything below was verified against the pinned mathlib commit
`548398201a64f3a5127d90d83945278cfe38cac4` by reading source and by the compiled spike
(`scratch_localmult.lean`, §7). **Line numbers refer to files under `.lake/packages/mathlib/`.**

The blueprint trap ("junk-valued derivative count") is avoided by construction: the definition
is the vanishing order of the normal form (`analyticOrderAt`), never an `iteratedDeriv` count.
`iteratedDeriv` appears nowhere in this unit.

---

## 1. Mathlib facts at this commit (deep-dive results)

### `Analysis/Analytic/Order.lean`

- `analyticOrderAt (f : 𝕜 → E) (z₀ : 𝕜) : ℕ∞` (`:48`). Junk `0` if `¬ AnalyticAt`; `⊤` iff
  eventually `0`. `analyticOrderNatAt = (analyticOrderAt f z₀).toNat` (`:62`).
- **Factorization** (`:87`):
  ```lean
  lemma AnalyticAt.analyticOrderAt_eq_natCast (hf : AnalyticAt 𝕜 f z₀) :
      analyticOrderAt f z₀ = n ↔
        ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z
  ```
  Also `analyticOrderAt_eq_top` (`:76`), `analyticOrderAt_eq_zero :
  … ↔ ¬ AnalyticAt 𝕜 f z₀ ∨ f z₀ ≠ 0` (`:121`), `AnalyticAt.analyticOrderAt_ne_top` (`:114`),
  `analyticOrderAt_congr (hfg : f =ᶠ[𝓝 z₀] g)` (`:176`), `analyticOrderAt_mul` (`:444`),
  `analyticOrderAt_pow` (`:455`).
- **Composition lemmas EXIST** (do not re-prove):
  ```lean
  -- :475
  lemma AnalyticAt.analyticOrderAt_comp (hf : AnalyticAt 𝕜 f (g z₀)) (hg : AnalyticAt 𝕜 g z₀) :
      analyticOrderAt (f ∘ g) z₀ = analyticOrderAt f (g z₀) * analyticOrderAt (g · - g z₀) z₀
  -- :508, [CompleteSpace 𝕜] [CharZero 𝕜]
  lemma analyticOrderAt_comp_of_deriv_ne_zero (hg : AnalyticAt 𝕜 g z₀) (hg' : deriv g z₀ ≠ 0) :
      analyticOrderAt (f ∘ g) z₀ = analyticOrderAt f (g z₀)      -- f arbitrary!
  ```
- `AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero (hf) (hf' : deriv f x ≠ 0) :
  analyticOrderAt (f · - f x) x = 1` (`:305`);
  `AnalyticAt.analyticOrderAt_deriv_add_one` (`:263`);
  `eventuallyConst_iff_analyticOrderAt_sub_eq_top : EventuallyConst f (𝓝 z₀) ↔
  analyticOrderAt (f · - f z₀) z₀ = ⊤` (`:80`).

### `Analysis/Meromorphic/Order.lean` (CC3 side)

- `meromorphicOrderAt (f) (x) : WithTop ℤ` (`:47`), factorization `meromorphicOrderAt_eq_int_iff`
  (`:94`), and the **CC3 compatibility bridge** (`:279`):
  ```lean
  lemma AnalyticAt.meromorphicOrderAt_eq (hf : AnalyticAt 𝕜 f x) :
      meromorphicOrderAt f x = (analyticOrderAt f x).map (↑· : ℕ → ℤ)
  ```
- Meromorphic composition (`:809`, `:838`): `MeromorphicAt.meromorphicOrderAt_comp` (product
  formula) and `meromorphicOrderAt_comp_of_deriv_ne_zero (hg) (hg') :
  meromorphicOrderAt (f ∘ g) x = meromorphicOrderAt f (g x)` — this is exactly what CC3's
  `ordAtX` chart-invariance will consume; record for the meromorphic-and-divisors unit.
- `meromorphicOrderAt_smul_of_ne_zero`/`_mul_of_ne_zero` (`:854`, `:862`).

### `Analysis/Analytic/IsolatedZeros.lean`, `Analysis/Meromorphic/{IsolatedZeros,NormalForm}.lean`

- `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero :
  (∀ᶠ z in 𝓝 z₀, f z = 0) ∨ ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0` (`:125`) — isolated-fibre atom.
- `AnalyticAt.unique_eventuallyEq_pow_smul_nonzero` (`:173`) — uniqueness of `k`;
  `exists_eventuallyEq_pow_smul_nonzero_iff` (`:185`); `AnalyticAt.map_nhdsNE
  (hfx) (h₂f : ¬EventuallyConst f (𝓝 x)) : (𝓝[≠] x).map f ≤ 𝓝[≠] f x` (`:335`).
- `NormalForm.lean` (`MeromorphicNFAt` `:47`, `toMeromorphicNFOn` `:656`) is CC3 repair
  machinery; this unit does not use it, but our conventions match its `(· - x) ^ n • g` shape.

### Planar analytic inverse function theorem (shared with surfaces-and-charts)

`Analysis/Calculus/InverseFunctionTheorem/Analytic.lean` — verified by spike:

```lean
-- :26, 𝕜 nontrivially normed, [CompleteSpace 𝕜] [CharZero 𝕜]
lemma AnalyticAt.analyticAt_localInverse (hf : AnalyticAt 𝕜 f x) (hf' : deriv f x ≠ 0) :
    AnalyticAt 𝕜 (hf.hasStrictDerivAt.localInverse _ _ _ hf') (f x)
-- :40
lemma analyticAt_comp_iff_of_deriv_ne_zero (hf : AnalyticAt 𝕜 f x) (hf' : deriv f x ≠ 0) :
    AnalyticAt 𝕜 (g ∘ f) x ↔ AnalyticAt 𝕜 g (f x)
```

Supporting: `HasStrictDerivAt.localInverse f f' a hf hf' : 𝕜 → 𝕜` (abbrev,
`InverseFunctionTheorem/Deriv.lean:33`, via `hasStrictFDerivAt_equiv`), with
`eventually_left_inverse`/`eventually_right_inverse`/`map_nhds_eq`/`to_localInverse` (same file);
`HasStrictFDerivAt.toOpenPartialHomeomorph` (`InverseFunctionTheorem/FDeriv.lean:114`) with
`toOpenPartialHomeomorph_coe` (`:126`, coe defeq `f`), `mem_toOpenPartialHomeomorph_source`
(`:130`); `AnalyticAt.hasStrictDerivAt` (`Analysis/Calculus/FDeriv/Analytic.lean:147`).
**These exact names are the planar IFT contract with the surfaces-and-charts designer.**

### `Complex.log` analyticity and k-th-root ingredients — verified by spike

`Analysis/SpecialFunctions/Complex/Analytic.lean` (root namespace, NOT `Complex.*`):
`analyticAt_clog (m : z ∈ slitPlane) : AnalyticAt ℂ log z` (`:29`);
`AnalyticAt.clog (fa : AnalyticAt ℂ f x) (m : f x ∈ slitPlane)` (`:37`); also
`AnalyticOnNhd.clog` (`:46`), `AnalyticAt.cpow` (`:66`).
Plus: `analyticAt_cexp` (`SpecialFunctions/ExpDeriv.lean:52`), `Complex.exp_log (h : z ≠ 0)`,
`Complex.exp_nat_mul : exp (n * x) = exp x ^ n` (`Analysis/Complex/Exponential.lean:153`),
`Complex.exp_ne_zero`, `Complex.log_one`, `Complex.slitPlane` + `one_mem_slitPlane`
(`Analysis/Complex/Basic.lean:629,655`).

### Manifold-side vocabulary

- Charts are `OpenPartialHomeomorph M H` at this commit. `chartAt_self_eq : chartAt H x =
  OpenPartialHomeomorph.refl H` is `rfl` (`ChartedSpace.lean:350`) — makes the planar
  specialization of our definition definitional.
- `IsManifold.maximalAtlas I n M` (`IsManifold/Basic.lean:876`, namespace `IsManifold`), with
  `subset_maximalAtlas` (`:883`), `chart_mem_maximalAtlas` (`:886`),
  `compatible_of_mem_maximalAtlas : e.symm.trans e' ∈ contDiffGroupoid n I` (`:889`).
  Groupoid membership criterion: `mem_groupoid_of_pregroupoid`
  (`StructureGroupoid.lean:326`) with `contDiffPregroupoid` (property = `ContDiffOn`),
  `ofSet_mem_contDiffGroupoid` (`IsManifold/Basic.lean:729`),
  `StructureGroupoid.mem_maximalAtlas_of_eqOnSource` (`HasGroupoid.lean:135`),
  `mem_maximalAtlas_iff` (`HasGroupoid.lean:104`).
- `contMDiffOn_chart` / `contMDiffOn_chart_symm` (`ContMDiff/Atlas.lean:83,86`);
  `contMDiffOn_of_mem_maximalAtlas` / `contMDiffOn_symm_of_mem_maximalAtlas` (`:64,70`).
- `contMDiffAt_iff` (`ContMDiff/Defs.lean:181`): `ContinuousAt ∧ ContDiffWithinAt 𝕜 n
  (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x)`; with
  `𝓘(ℂ)` the ext-charts are the charts and `range = univ`; `ContDiffAt.analyticAt` /
  `AnalyticAt.contDiffAt` for `n = ω` (`ContDiff/Defs.lean:968,976`);
  `contMDiffAt_iff_contDiffAt`, `contMDiff_iff_contDiff` (`ContMDiff/NormedSpace.lean:54,66`).
- `OpenPartialHomeomorph`: `trans` (`≫ₕ`), `restrOpen (s) (hs : IsOpen s)`
  (`Topology/OpenPartialHomeomorph/IsImage.lean:216`), `map_nhds_eq` (`Continuity.lean:73`),
  `map_nhdsWithin_eq` (`:83`), `Homeomorph.toOpenPartialHomeomorph` (`Basic.lean:244`).
- `Filter.EventuallyConst f l` (`Order/Filter/EventuallyConst.lean:35`) — our nonconstancy
  predicate; `ENat.toNat_mul : (a * b).toNat = a.toNat * b.toNat` (`Data/ENat/Basic.lean:257`,
  unconditional) — makes the ℕ-valued composition law junk-robust.

**Absent (we must build):** any notion of multiplicity of maps of complex manifolds; the analytic
local k-th root; the `f = f z₀ + φ^k` normal form; adapted charts. All planar order/IFT atoms
exist.

---

## 2. Definitions (CC4, frozen) and conventions

Standing variables for every file in this unit (per CONVENTIONS.md, compactness/connectedness
dropped — the local theory never needs them; `T2Space` also unused and omitted; two/three
surfaces as needed):

```lean
open scoped ContDiff Manifold Topology
open Filter
namespace RS
variable {X Y Z : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
```

Holomorphy at a point is spelled `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x` (if surfaces-and-charts exports
an abbreviation for this, it is defeq and the builder may switch spellings). Nonconstancy near
`x` is spelled `¬ EventuallyConst F (𝓝 x)` (mathlib-native, no new predicate).

```lean
/-- `F` read in the standard charts at `x` and `F x`, recentered to vanish at `chartAt ℂ x x`.
Junk (from the charts' junk values) away from the chart sources; only its germ matters. -/
def inChartAt (F : X → Y) (x : X) : ℂ → ℂ :=
  fun z ↦ chartAt ℂ (F x) (F ((chartAt ℂ x).symm z)) - chartAt ℂ (F x) (F x)

/-- ℕ∞-valued local multiplicity (CC4). `⊤` iff `F` is holomorphic and locally constant at `x`;
`0` iff `inChartAt F x` is not analytic (junk). Honest value: the vanishing order `k ≥ 1`. -/
noncomputable def multiplicityENat (F : X → Y) (x : X) : ℕ∞ :=
  analyticOrderAt (inChartAt F x) (chartAt ℂ x x)

/-- CC4's `multiplicity F x : ℕ`: the order when finite; junk `0` when `F` is locally constant
at `x` (order `⊤`) or not holomorphic at `x` (order junk `0`). -/
noncomputable def multiplicity (F : X → Y) (x : X) : ℕ := (multiplicityENat F x).toNat

def IsRamifiedAt (F : X → Y) (x : X) : Prop := 2 ≤ multiplicity F x
```

Notes. (i) `inChartAt F x (chartAt ℂ x x) = 0` always (no hypotheses), so the order is `≥ 1`
whenever it is honest. (ii) On `ℂ` the charts are `OpenPartialHomeomorph.refl` by `rfl`
(`chartAt_self_eq`), so `inChartAt f z₀ = fun z ↦ f z - f z₀` definitionally — the planar and
CC3 bridges are near-`rfl`. (iii) `_root_.multiplicity` (ring theory) exists in mathlib; ours is
`RS.multiplicity`, no clash inside the `RS` namespace.

---

## 3. File plan

```
Jacobian/LocalMultiplicity.lean                  -- unit root: imports all, 5-15 line API docstring
Jacobian/LocalMultiplicity/KthRoot.lean          -- planar analytic k-th root (log route)
Jacobian/LocalMultiplicity/PlanarNormalForm.lean -- packaged planar IFT; f = f z₀ + φ^k; order helpers; image_pow_ball
Jacobian/LocalMultiplicity/ChartBridge.lean      -- inChartAt; ContMDiffAt ω ↔ AnalyticAt bridge (Compat); transition lemmas
Jacobian/LocalMultiplicity/Multiplicity.lean     -- multiplicityENat/multiplicity; junk API; chart invariance; isolated fibres; CC3 compat
Jacobian/LocalMultiplicity/AdaptedCharts.lean    -- AdaptedChartsAt structure; existence (THE z^k atom); multiplicity_eq
Jacobian/LocalMultiplicity/Composition.lean      -- composition law; precomposition with charts; mult = 1 ↔ local homeo; eventually mult = 1
```

Import spine (targeted, per spike): `Mathlib.Analysis.Analytic.Order`,
`Mathlib.Analysis.Meromorphic.Order`, `Mathlib.Analysis.Analytic.IsolatedZeros`,
`Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic`,
`Mathlib.Analysis.SpecialFunctions.Complex.Analytic`,
`Mathlib.Analysis.SpecialFunctions.ExpDeriv`; manifold files add
`Mathlib.Geometry.Manifold.ContMDiff.Atlas`, `Mathlib.Geometry.Manifold.ContMDiff.NormedSpace`.

---

## 4. Exports (exact signatures)

### 4.1 Planar layer — `KthRoot.lean`

```lean
/-- Local analytic k-th root of a non-vanishing analytic function. -/
theorem AnalyticAt.exists_pow_eq {u : ℂ → ℂ} {z₀ : ℂ} (hu : AnalyticAt ℂ u z₀)
    (hu₀ : u z₀ ≠ 0) {k : ℕ} (hk : k ≠ 0) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r z₀ ∧ r z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, r z ^ k = u z
```

### 4.2 Planar layer — `PlanarNormalForm.lean`

```lean
/-- Packaged planar analytic IFT: analytic + `deriv ≠ 0` gives an `OpenPartialHomeomorph`
agreeing with `f` near `z₀`, analytic with analytic inverse. (Both this unit and
surfaces-and-charts consume mathlib's `AnalyticAt.analyticAt_localInverse` here.) -/
theorem AnalyticAt.exists_openPartialHomeomorph {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hf' : deriv f z₀ ≠ 0) :
    ∃ φ : OpenPartialHomeomorph ℂ ℂ, z₀ ∈ φ.source ∧ (∀ z ∈ φ.source, φ z = f z) ∧
      AnalyticOnNhd ℂ φ φ.source ∧ AnalyticOnNhd ℂ φ.symm φ.target

/-- Local normal form (Forster 2.1, planar half): finite recentered order `k ≥ 1` means
`f = f z₀ + φ ^ k` with `φ` an analytic local coordinate at `z₀`. -/
theorem AnalyticAt.exists_normal_form {f : ℂ → ℂ} {z₀ : ℂ} {k : ℕ}
    (hf : AnalyticAt ℂ f z₀) (hk : analyticOrderAt (f · - f z₀) z₀ = k) (hk₀ : k ≠ 0) :
    ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ z₀ ∧ φ z₀ = 0 ∧ deriv φ z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝 z₀, f z = f z₀ + φ z ^ k

/-- Normal form, packaged as an analytic-with-analytic-inverse partial homeomorphism. -/
theorem AnalyticAt.exists_normal_form_openPartialHomeomorph {f : ℂ → ℂ} {z₀ : ℂ} {k : ℕ}
    (hf : AnalyticAt ℂ f z₀) (hk : analyticOrderAt (f · - f z₀) z₀ = k) (hk₀ : k ≠ 0) :
    ∃ φ : OpenPartialHomeomorph ℂ ℂ, z₀ ∈ φ.source ∧ φ z₀ = 0 ∧
      AnalyticOnNhd ℂ φ φ.source ∧ AnalyticOnNhd ℂ φ.symm φ.target ∧
      ∀ z ∈ φ.source, f z = f z₀ + φ z ^ k

/-- Recentered order is invariant under postcomposition with a bi-analytic germ.
(Mathlib has the precomposition version `analyticOrderAt_comp_of_deriv_ne_zero`;
this is its left twin, and is upstreamable.) -/
theorem analyticOrderAt_left_comp_sub {h f : ℂ → ℂ} {z₀ : ℂ}
    (hh : AnalyticAt ℂ h (f z₀)) (hh' : deriv h (f z₀) ≠ 0) (hf : AnalyticAt ℂ f z₀) :
    analyticOrderAt (fun z ↦ h (f z) - h (f z₀)) z₀ = analyticOrderAt (f · - f z₀) z₀

/-- `z ↦ z ^ k` maps balls onto balls (fibre-counting geometry for mapping-degree). -/
theorem image_pow_ball {k : ℕ} (hk : k ≠ 0) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (· ^ k) '' Metric.ball (0 : ℂ) ρ = Metric.ball 0 (ρ ^ k)
```

### 4.3 Manifold bridge — `ChartBridge.lean`

`inChartAt` as in §2, plus (the iff is CC7 material owned by surfaces-and-charts; we prove it in
a clearly marked `section Compat` for later upstreaming — request filed in
`docs/requests/surfaces-and-charts.md`):

```lean
theorem contMDiffAt_iff_analyticAt_inChartAt {F : X → Y} {x : X} :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x ↔
      ContinuousAt F x ∧ AnalyticAt ℂ (inChartAt F x) (chartAt ℂ x x)

theorem eventuallyConst_inChartAt (h : EventuallyConst F (𝓝 x)) :
    EventuallyConst (inChartAt F x) (𝓝 (chartAt ℂ x x))
theorem eventuallyConst_inChartAt_iff (hFc : ContinuousAt F x) :
    EventuallyConst (inChartAt F x) (𝓝 (chartAt ℂ x x)) ↔ EventuallyConst F (𝓝 x)

/-- Transitions between maximal-atlas charts are analytic with nonvanishing derivative. -/
theorem analyticAt_transition {e e' : OpenPartialHomeomorph X ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    {x : X} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    AnalyticAt ℂ (e' ∘ e.symm) (e x) ∧ deriv (e' ∘ e.symm) (e x) ≠ 0

/-- Trans with a groupoid element stays in the maximal atlas (upstreamable helper). -/
theorem trans_mem_maximalAtlas {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) {Φ : OpenPartialHomeomorph ℂ ℂ}
    (hΦ : Φ ∈ contDiffGroupoid ω 𝓘(ℂ)) :
    e ≫ₕ Φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X
```

### 4.4 Surface layer — `Multiplicity.lean`

```lean
theorem multiplicityENat_def (F : X → Y) (x : X) :
    multiplicityENat F x = analyticOrderAt (inChartAt F x) (chartAt ℂ x x) := rfl

/-- Planar specialization: on `ℂ` the charts are `refl`, so this is (near-)`rfl`. -/
@[simp] theorem multiplicityENat_planar (f : ℂ → ℂ) (z₀ : ℂ) :
    multiplicityENat f z₀ = analyticOrderAt (f · - f z₀) z₀

-- Junk conventions (no hypotheses beyond what is stated):
theorem multiplicityENat_eq_top_of_eventuallyConst {F : X → Y} {x : X}
    (h : EventuallyConst F (𝓝 x)) : multiplicityENat F x = ⊤
@[simp] theorem multiplicity_of_eventuallyConst (h : EventuallyConst F (𝓝 x)) :
    multiplicity F x = 0

-- Honest statements, guarded by holomorphy and nonconstancy:
theorem multiplicityENat_ne_zero (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x) :
    multiplicityENat F x ≠ 0
theorem multiplicityENat_eq_top_iff (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x) :
    multiplicityENat F x = ⊤ ↔ EventuallyConst F (𝓝 x)
theorem natCast_multiplicity (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x)
    (hnc : ¬ EventuallyConst F (𝓝 x)) :
    (multiplicity F x : ℕ∞) = multiplicityENat F x
theorem one_le_multiplicity (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x)
    (hnc : ¬ EventuallyConst F (𝓝 x)) : 1 ≤ multiplicity F x

/-- CHART INVARIANCE: the defining order is the same in any admissible chart pair. -/
theorem analyticOrderAt_charts_eq_multiplicityENat
    {F : X → Y} {x : X} (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x)
    {e : OpenPartialHomeomorph X ℂ} {e' : OpenPartialHomeomorph Y ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hxe : x ∈ e.source)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Y) (hxe' : F x ∈ e'.source) :
    analyticOrderAt (fun z ↦ e' (F (e.symm z)) - e' (F x)) (e x) = multiplicityENat F x

/-- Isolated points of the fibre. -/
theorem eventually_ne (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x)
    (hnc : ¬ EventuallyConst F (𝓝 x)) : ∀ᶠ y in 𝓝[≠] x, F y ≠ F x
theorem exists_nhds_fiber_eq_singleton (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x)
    (hnc : ¬ EventuallyConst F (𝓝 x)) :
    ∃ U ∈ 𝓝 x, ∀ y ∈ U, F y = F x → y = x

/-- CC3 COMPATIBILITY: our multiplicity vs `meromorphicOrderAt` in the chart at `x`
(for target `ℂ` the target chart is `refl`). `meromorphic-and-divisors` will read the RHS as
`ordAtX (f · - f x) x`. -/
theorem meromorphicOrderAt_chart_sub {f : X → ℂ} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) :
    meromorphicOrderAt (fun z ↦ f ((chartAt ℂ x).symm z) - f x) (chartAt ℂ x x)
      = (multiplicityENat f x).map (Nat.cast : ℕ → ℤ)
theorem meromorphicOrderAt_chart_of_eq_zero {f : X → ℂ} {x : X}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) (h0 : f x = 0) :
    meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)
      = (multiplicityENat f x).map (Nat.cast : ℕ → ℤ)   -- literally CC3's `ordAtX f x`
```

### 4.5 THE atom — `AdaptedCharts.lean`

```lean
/-- Adapted chart pair at `x` exhibiting `F` as `z ↦ z ^ k` (Forster Thm 2.1).
Both charts belong to the analytic maximal atlases (so all holomorphy transports), both are
centered, targets are round balls, and `F` is exactly `(·^k)` in these coordinates. -/
structure AdaptedChartsAt (F : X → Y) (x : X) (k : ℕ) where
  e : OpenPartialHomeomorph X ℂ
  e' : OpenPartialHomeomorph Y ℂ
  mem_maximalAtlas : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X
  mem_maximalAtlas' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Y
  radius : ℝ
  radius_pos : 0 < radius
  mem_source : x ∈ e.source
  mem_source' : F x ∈ e'.source
  map_eq_zero : e x = 0
  map_eq_zero' : e' (F x) = 0
  target_eq : e.target = Metric.ball 0 radius
  target_eq' : e'.target = Metric.ball 0 (radius ^ k)
  mapsTo : Set.MapsTo F e.source e'.source
  eqOn_pow : ∀ z ∈ e.source, e' (F z) = e z ^ k

namespace AdaptedChartsAt  -- derived API (all proved from the fields + §4.2 helpers)
theorem eqOn_symm (A : AdaptedChartsAt F x k) : ∀ z ∈ A.e.source, F z = A.e'.symm (A.e z ^ k)
theorem image_source (hk : k ≠ 0) (A : AdaptedChartsAt F x k) : F '' A.e.source = A.e'.source
theorem contMDiffOn_e (A) : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω A.e A.e.source          -- + symm, e', e'.symm
theorem multiplicity_eq (hk : k ≠ 0) (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x)
    (A : AdaptedChartsAt F x k) : multiplicity F x = k
end AdaptedChartsAt

/-- Existence, with source shrinkable into any given neighborhood. `k = multiplicity F x ≥ 1`. -/
theorem exists_adaptedChartsAt {F : X → Y} {x : X}
    (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x) (hnc : ¬ EventuallyConst F (𝓝 x))
    {U : Set X} (hU : U ∈ 𝓝 x) :
    ∃ A : AdaptedChartsAt F x (multiplicity F x), A.e.source ⊆ U
```

### 4.6 `Composition.lean`

```lean
/-- Multiplicities multiply under composition (ℕ∞ version; honest, no junk interference). -/
theorem multiplicityENat_comp {G : Y → Z} {F : X → Y} {x : X}
    (hG : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω G (F x)) (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x) :
    multiplicityENat (G ∘ F) x = multiplicityENat G (F x) * multiplicityENat F x

/-- ℕ version; junk-robust thanks to `ENat.toNat_mul`. -/
theorem multiplicity_comp (hG : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω G (F x))
    (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x) :
    multiplicity (G ∘ F) x = multiplicity G (F x) * multiplicity F x

/-- Behavior under precomposition with charts: reading a map through any admissible chart
does not change the multiplicity. (`F ∘ e.symm : ℂ → Y`, multiplicity at a planar point.) -/
theorem multiplicityENat_comp_chart_symm {F : X → Y}
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    {z : ℂ} (hz : z ∈ e.target) (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F (e.symm z)) :
    multiplicityENat (F ∘ e.symm) z = multiplicityENat F (e.symm z)

/-- `multiplicity = 1` ↔ local injectivity. -/
theorem multiplicity_eq_one_iff_injOn (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x)
    (hnc : ¬ EventuallyConst F (𝓝 x)) :
    multiplicity F x = 1 ↔ ∃ U ∈ 𝓝 x, Set.InjOn F U

/-- `multiplicity = 1` gives a local homeomorphism agreeing with `F` (Forster 2.5 germ). -/
theorem exists_openPartialHomeomorph_of_multiplicity_eq_one
    (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x) (hnc : ¬ EventuallyConst F (𝓝 x))
    (h1 : multiplicity F x = 1) :
    ∃ h : OpenPartialHomeomorph X Y, x ∈ h.source ∧ ∀ z ∈ h.source, h z = F z

theorem isRamifiedAt_iff_not_injOn (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x)
    (hnc : ¬ EventuallyConst F (𝓝 x)) :
    IsRamifiedAt F x ↔ ¬ ∃ U ∈ 𝓝 x, Set.InjOn F U

/-- Ramification is isolated: nearby points are unramified (mapping-degree's
"critical values are discrete" seed). -/
theorem eventually_multiplicity_eq_one (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x)
    (hnc : ¬ EventuallyConst F (𝓝 x)) : ∀ᶠ y in 𝓝[≠] x, multiplicity F y = 1
```

---

## 5. Proof plans

### 5.1 k-th root (log route)

Set `a := u z₀ ≠ 0` and define `r z := exp (log a / k) * exp (log (u z / a) / k)`.
- **Analyticity at `z₀`**: `u z / a` is analytic (`hu.div analyticAt_const` / `fun_prop`) with
  value `1 ∈ slitPlane` (`one_mem_slitPlane`), so `AnalyticAt.clog` applies; divide by the
  constant `k`, compose with `analyticAt_cexp`, multiply by the constant `exp (log a / k)`.
- **`r z₀ ≠ 0`**: `r z₀ = exp (log a / k) * exp (log 1 / k) = exp (log a / k)` (`Complex.log_one`),
  nonzero by `Complex.exp_ne_zero`.
- **`r ^ k = u` eventually**: `u z ≠ 0` eventually (`hu.continuousAt.eventually_ne hu₀`);
  pointwise, `r z ^ k = exp (k * (log a / k)) * exp (k * (log (u z / a) / k))`
  (`Complex.exp_nat_mul`, `mul_pow`) `= exp (log a) * exp (log (u z / a)) = a * (u z / a) = u z`
  (`mul_div_cancel₀` with `(k : ℂ) ≠ 0`, `Complex.exp_log` twice, using `u z / a ≠ 0`).
- **The `u z₀ ∈ ℝ<0` case** costs nothing on this route: we never take `log` of `u` itself, only
  of `u/a` (≈ 1) and of the constant `a` — and `Complex.exp_log` is valid for ALL nonzero
  constants (only *analyticity* of `log` needs the slit plane, and it is only ever invoked at
  values near `1`). This replaces the suggested "rotate so `u z₀ ∉ ℝ≤0`" case split; the
  division by `a` IS the rotation.

### 5.2 Packaged planar IFT (`exists_openPartialHomeomorph`)

1. `Φ₀ := (hf.hasStrictDerivAt.hasStrictFDerivAt_equiv hf').toOpenPartialHomeomorph f`; then
   `Φ₀ = f` as functions (`toOpenPartialHomeomorph_coe`, defeq) and
   `z₀ ∈ Φ₀.source` (`mem_toOpenPartialHomeomorph_source`).
2. Analyticity spreads: `hf.eventually_analyticAt` and `deriv f` is analytic hence continuous
   (`AnalyticAt.deriv`), so `∀ᶠ z, AnalyticAt ℂ f z ∧ deriv f z ≠ 0`. Choose open
   `s ⊆ Φ₀.source` with `z₀ ∈ s` inside this event; set `φ := Φ₀.restrOpen s hs`.
3. `AnalyticOnNhd φ φ.source`: pointwise from step 2 (`φ = f` on source).
4. `AnalyticOnNhd φ.symm φ.target`: for `w = f z`, `z ∈ φ.source`: mathlib's
   `AnalyticAt.analyticAt_localInverse` (at `z`) gives an analytic local inverse; it agrees with
   `φ.symm` near `w` (`eventually_right_inverse` + injectivity of `φ` on source /
   `localInverse_unique`), conclude by `AnalyticAt.congr`.

### 5.3 Normal form (Forster 2.1 proof, planar half)

1. `hfa : AnalyticAt ℂ (f · - f z₀) z₀` (fun_prop). `hfa.analyticOrderAt_eq_natCast.mp hk`
   gives `g` analytic, `g z₀ ≠ 0`, `∀ᶠ z, f z - f z₀ = (z - z₀) ^ k • g z`.
2. §5.1 root: `r` with `r ^ k = g` eventually, `r z₀ ≠ 0`.
3. `φ := fun z ↦ (z - z₀) * r z`: analytic; `φ z₀ = 0`; `HasDerivAt φ (r z₀) z₀` by the product
   rule (`HasDerivAt.mul`, the `(z - z₀)` factor kills the second term), so
   `deriv φ z₀ = r z₀ ≠ 0` (`HasDerivAt.deriv`).
4. Eventually `f z = f z₀ + ((z - z₀) * r z) ^ k` by `mul_pow`, `smul_eq_mul` and steps 1-2.
5. Packaged version: apply §5.2 to `φ`, then `restrOpen` into the set where step 4's eventual
   equality holds.

### 5.4 Chart invariance (and `analyticOrderAt_left_comp_sub`)

`analyticOrderAt_left_comp_sub`: apply `AnalyticAt.analyticOrderAt_comp` with outer function
`(h · - h (f z₀))` (vanishes at `f z₀`, order `1` by
`analyticOrderAt_sub_eq_one_of_deriv_ne_zero`), inner `f`; conclude with `one_mul`.

Chart invariance: let `ĉ := inChartAt F x`, `z₀ := chartAt ℂ x x`, and let
`τ := (chartAt ℂ x) ∘ e.symm` (X-side transition, from `e` to the standard chart) and
`σ := e' ∘ (chartAt ℂ (F x)).symm` (Y-side transition). By `analyticAt_transition`
(via `IsManifold.compatible_of_mem_maximalAtlas` + `mem_groupoid_of_pregroupoid` →
`ContDiffOn ω` → `AnalyticAt` via `ContDiffAt.analyticAt`; `deriv ≠ 0` because the transition
has a differentiable two-sided local inverse — differentiate `τ⁻¹ ∘ τ = id` with `deriv_comp`),
both are analytic with nonvanishing derivative at the relevant points. Then on a neighborhood of
`e x` (chart sources overlap; `analyticOrderAt_congr` handles the junk-value discrepancies):

```
fun z ↦ e' (F (e.symm z)) - e' (F x)  =ᶠ  (σ · - σ w₀) ∘ (ĉ' ∘ τ)        -- ĉ' the uncentered composite, w₀ := ĉ' z₀
order = order (σ · - σ w₀) w₀ * order ((ĉ' ∘ τ) · - w₀) (e x)            -- AnalyticAt.analyticOrderAt_comp
      = 1 * order ((ĉ' · - w₀) ∘ τ) (e x)                                 -- sub_eq_one_of_deriv_ne_zero
      = order (ĉ' · - w₀) z₀ = multiplicityENat F x                       -- analyticOrderAt_comp_of_deriv_ne_zero
```

### 5.5 Adapted charts existence

1. Bridge `hF` to `hĉ : AnalyticAt ℂ ĉ z₀` (`ĉ := inChartAt F x`), `hnc` to
   `¬ EventuallyConst ĉ (𝓝 z₀)` (`eventuallyConst_inChartAt_iff`, chart is a homeo near `x` via
   `OpenPartialHomeomorph.map_nhds_eq`). So `k := multiplicity F x` has
   `(k : ℕ∞) = analyticOrderAt ĉ z₀`, `k ≥ 1`.
2. §5.3 packaged normal form for the uncentered composite: `Φ` with
   `chart' (F (chart.symm z)) = chart' (F x) + Φ z ^ k` on `Φ.source`.
3. Pick `ρ > 0` such that: `Metric.ball 0 ρ ⊆ Φ.target`; `Φ.symm '' ball 0 ρ` sits inside
   `chartAt x`.target ∩ (chart-image of `U`) ∩ (the eventual-equality set); and
   `Metric.ball (0:ℂ) (ρ^k) ⊆ (chartAt ℂ (F x)).target - chart' (F x)` (all are neighborhoods of
   the base points; use `Metric.nhds_basis_ball`).
4. `e := ((chartAt ℂ x) ≫ₕ Φ).restrOpen (preimage of ball 0 ρ)` — target computes to
   `Metric.ball 0 ρ` by step 3; `e x = Φ z₀ = 0`.
   `e' := ((chartAt ℂ (F x)) ≫ₕ T).restrOpen (preimage of ball 0 (ρ^k))` where
   `T := Homeomorph.toOpenPartialHomeomorph (Homeomorph.subRight (chart' (F x)))`
   (translation; in `contDiffGroupoid ω 𝓘(ℂ)` trivially).
5. Atlas membership: `trans_mem_maximalAtlas` with `Φ ∈ contDiffGroupoid ω 𝓘(ℂ)`
   (`mem_groupoid_of_pregroupoid`: `ContDiffOn` both ways from `AnalyticOnNhd` via
   `AnalyticAt.contDiffAt`); restriction stays in the maximal atlas
   (`ofSet_mem_contDiffGroupoid` + `mem_maximalAtlas_of_eqOnSource`).
6. `eqOn_pow` is step 2 rewritten (`e' (F z) = chart' (F z) - chart' (F x) = Φ (chart z) ^ k =
   e z ^ k`); `mapsTo` from `eqOn_pow` + `target_eq'` (`|e z ^ k| < ρ ^ k`); derived
   `image_source` from `eqOn_pow` + `image_pow_ball` + bijectivity of `e, e'` onto the balls.

### 5.6 Composition law

With `f̂ := chart_{F x} ∘ F ∘ chart_x.symm` (so `inChartAt F x = f̂ · - f̂ z₀`), the composite in
charts satisfies `inChartAt (G ∘ F) x =ᶠ[𝓝 z₀] (inChartAt G (F x)) ∘ f̂` — the middle charts
cancel on a neighborhood (continuity of `F` in charts keeps values in `chart_{F x}.source`;
`analyticOrderAt_congr`). Now `AnalyticAt.analyticOrderAt_comp` applies **verbatim** (outer
`inChartAt G (F x)` is analytic at `f̂ z₀ = chart_{F x} (F x)` and vanishes there; inner factor is
`analyticOrderAt (f̂ · - f̂ z₀) z₀ = multiplicityENat F x`). ℕ version: `ENat.toNat_mul`.
Precomposition-with-chart corollary: `multiplicityENat_comp_chart_symm` is chart invariance §5.4
read as a statement about the planar-source map `F ∘ e.symm` (on `ℂ` the source chart is `refl`).

### 5.7 mult = 1 ↔ local injectivity; eventually mult = 1; isolated fibres

- (⇒) `k = 1` adapted charts: `F = e'.symm ∘ e` on `e.source` (`eqOn_symm`, `pow_one`), injective.
  For the partial-homeo version: `h := A.e ≫ₕ A.e'.symm` has `h.source = A.e.source` (targets
  match: `ρ ^ 1 = ρ`) and `h = F` there.
- (⇐) Contrapose. `k ≥ 2` (finite, `≥ 1`): with `ζ := exp (2 * π * I / k)` we have `ζ ^ k = 1`
  (`Complex.exp_nat_mul`, `Complex.exp_two_pi_mul_I`) and `ζ ≠ 1` (`Complex.exp_eq_one_iff`:
  `1/k ∉ ℤ` for `k ≥ 2`). Inside any `U`, shrink adapted charts into `U`; for small `δ > 0`,
  `z₁ := e.symm δ ≠ z₂ := e.symm (δζ)` but `F z₁ = F z₂` by `eqOn_symm` and `(δζ)^k = δ^k`.
- `eventually_multiplicity_eq_one`: for `y ∈ A.e.source`, `y ≠ x`: near `y`,
  `F = e'.symm ∘ (·^k) ∘ e` with `e y ≠ 0`, and `deriv (·^k) (e y) = k (e y)^{k-1} ≠ 0`; so by
  chart invariance + `analyticOrderAt_left_comp_sub`/`analyticOrderAt_comp_of_deriv_ne_zero`
  the order at `y` is that of a deriv-nonzero map, i.e. `1`
  (`analyticOrderAt_sub_eq_one_of_deriv_ne_zero`).
- `eventually_ne`: `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` on `inChartAt F x`
  (right branch by `hnc`); pull `𝓝[≠] z₀` back through the chart
  (`OpenPartialHomeomorph.map_nhdsWithin_eq` / `map_nhds_eq` + injectivity on source), and
  translate `inChartAt F x (chart y) ≠ 0` into `F y ≠ F x` (chart' injective on its source,
  `F y ∈ source` eventually by continuity).

### 5.8 CC3 compatibility

`multiplicityENat_planar`: `chartAt_self_eq` is `rfl`; expect `rfl` or a one-line `simp`.
`meromorphicOrderAt_chart_sub`: for target `ℂ`, `inChartAt f x = fun z ↦ f ((chartAt ℂ x).symm z)
- f x` definitionally; the function is analytic at `z₀` (bridge), apply
`AnalyticAt.meromorphicOrderAt_eq` and unfold `multiplicityENat`. The `f x = 0` corollary
rewrites the subtraction away. **Convention check (no off-by-one/sign):** CC3's
`ordAtX f x := meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)`; our lemma says
`ordAtX (f - f x) x = (multiplicityENat f x).map Nat.cast` — both count the vanishing order of
the recentered function, both use `(z - z₀)^n • g` normal forms, `⊤` ↔ locally ≡ 0 on both
sides. Additionally, CC3's chart-invariance of `ordAtX` is mathlib-direct via
`meromorphicOrderAt_comp_of_deriv_ne_zero` (verified, spiked).

---

## 6. Spike record

`scratch_localmult.lean` (project root, gitignored via `scratch_*.lean`), **60 lines**, compiled
with `lake env lean scratch_localmult.lean`: **success on first attempt, 5.8 s wall** (warm
mathlib cache). Verifies by re-typing exact statements:
(a) `AnalyticAt.analyticOrderAt_eq_natCast` (the `(z-z₀)^n • unit` factorization),
`AnalyticAt.analyticOrderAt_comp`, `analyticOrderAt_comp_of_deriv_ne_zero`,
`AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero`, `AnalyticAt.meromorphicOrderAt_eq`,
`meromorphicOrderAt_comp_of_deriv_ne_zero`;
(b) `AnalyticAt.analyticAt_localInverse`, `HasStrictDerivAt.eventually_left_inverse` (through
`AnalyticAt.hasStrictDerivAt`), `analyticAt_comp_iff_of_deriv_ne_zero`;
(c) `analyticAt_clog`, `AnalyticAt.clog`, `analyticAt_cexp`, `Complex.exp_log`,
`Complex.exp_nat_mul`, `one_mem_slitPlane`.
Minimal imports: `Mathlib.Analysis.Analytic.Order`, `Mathlib.Analysis.Meromorphic.Order`,
`Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic`,
`Mathlib.Analysis.SpecialFunctions.Complex.Analytic`,
`Mathlib.Analysis.SpecialFunctions.ExpDeriv`.

---

## 7. Risks & fallbacks

1. **Exact-ball targets in `AdaptedChartsAt`** (medium). The `restrOpen`/`trans` set algebra to
   make `e.target = Metric.ball 0 ρ` on the nose may fight `PartialEquiv` source/target
   normal forms. Fallback: weaken `target_eq`/`target_eq'` to `Metric.ball 0 ρ ⊆ e.target` plus
   an explicit field `image_source : F '' e.source = e'.source` (promote the derived lemma to a
   field); mapping-degree's fibre counting survives unchanged.
2. **`trans_mem_maximalAtlas` helper** (low-medium): no ready-made mathlib lemma; the proof via
   `mem_maximalAtlas_iff` + groupoid closure + `mem_maximalAtlas_of_eqOnSource` is ~20 lines.
   Fallback: drop the atlas fields and carry the four `ContMDiffOn` facts as structure fields
   (they are what downstream actually uses); chart invariance then takes `ContMDiffOn`-charts
   hypotheses instead of maximal-atlas ones.
3. **CC7 bridge duplication** (coordination): `contMDiffAt_iff_analyticAt_inChartAt` is owned by
   surfaces-and-charts (CC7). We prove it in a marked `Compat` section; request filed in
   `docs/requests/surfaces-and-charts.md` with the exact statement so both units state it
   identically. Risk: their final spelling differs (e.g. via `extChartAt`) — mitigation: ours is
   stated with `chartAt` only, and `extChartAt 𝓘(ℂ) x = chartAt ℂ x` is `rfl`-level (CC7 pins it).
4. **Unverified-by-spike auxiliary names** (low): `AnalyticAt.deriv`,
   `AnalyticAt.eventually_analyticAt`, `AnalyticAt.congr`, `ContinuousAt.eventually_ne`,
   `Complex.exp_two_pi_mul_I`, `Complex.exp_eq_one_iff`, `Homeomorph.subRight`,
   `HasStrictDerivAt.hasStrictFDerivAt_equiv` (this one read directly in source at
   `InverseFunctionTheorem/Deriv.lean`). All standard; builder re-greps before use; none is
   load-bearing for the design shape.
5. **Eta/`fun`-literal mismatches** in order lemmas (`(g · - g z₀)` vs our recentered
   composites): always pass through `analyticOrderAt_congr`; never rely on syntactic equality.
6. **`𝓝[≠]` transport through charts** (low): compose `OpenPartialHomeomorph.map_nhdsWithin_eq`
   with source-injectivity; if fiddly, prove the tiny lemma
   `map (𝓝[≠] x) e = 𝓝[≠] (e x)` for `x ∈ e.source` once in `ChartBridge.lean`.

## 8. Downstream consumers (contracts)

- **mapping-degree**: `exists_adaptedChartsAt` (with the `⊆ U` shrinking) + `image_source` +
  round-ball targets = fibre counting over regular values (`z^k : B(0,ρ) → B(0,ρ^k)` is exactly
  `k`-to-1 away from 0 — root counting of `z^k` itself lives in mapping-degree; `image_pow_ball`
  is provided here); `eventually_ne`/`exists_nhds_fiber_eq_singleton` = fibre discreteness;
  `eventually_multiplicity_eq_one` = discreteness of the ramification locus (finiteness of
  critical values on compact `X`); `multiplicity_eq_one_iff_injOn` +
  `exists_openPartialHomeomorph_of_multiplicity_eq_one` = unbranched ⇔ local homeo (Forster 4.4).
- **proper-map-degree**: multiplicities sum over fibres via adapted charts; `multiplicity_comp`
  for sheet bookkeeping; degree-1 ⇒ injective uses `multiplicity_eq_one_iff_injOn`.
- **meromorphic-and-divisors (CC3)**: `meromorphicOrderAt_chart_sub` /
  `meromorphicOrderAt_chart_of_eq_zero` tie `multiplicity` to `ordAtX`; CC3 chart invariance
  should be proved from mathlib's `meromorphicOrderAt_comp_of_deriv_ne_zero` (+ our
  `analyticAt_transition`), not re-derived.
- **surfaces-and-charts**: shared planar IFT contract = mathlib names in §1 (IFT block); our
  `Compat` bridge lemma is theirs to own (request filed); `trans_mem_maximalAtlas` and
  `analyticAt_transition` are candidates for upstreaming into their unit.
- **genus-zero-headline**: degree-1 map ⇒ homeomorphism ultimately reduces to
  `exists_openPartialHomeomorph_of_multiplicity_eq_one`.
