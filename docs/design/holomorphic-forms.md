# Design: holomorphic-forms (`Jacobian/Forms/`)

Owner unit of **CC1** (frozen in `docs/design/core-choices.md`). Defines `Form1 X`, the
chart-coefficient API `coeffIn`, the constructor `Form1.ofCoeffs`, `mdifferential`, planar
**Montel**, `FiniteDimensional ℂ (Form1 X)` on compact `X`, and **`genus`** — the most
load-bearing definition of the project. References: Forster §9–10 (PDF 65–87).

**Spike status (compiled truth).** `scratch_forms.lean` (79 lines) compiles clean in ~12 s with
`lake env lean scratch_forms.lean` at the pinned mathlib. Verified: CC1's `Form1` spelling
elaborates; `AddCommGroup`/`Module ℂ` instances found by TC; `Finset.sum` of forms works
(blueprint hazard cleared); `ContMDiffVectorBundle ω` instance found for the Hom bundle;
evaluation `η x v : ℂ` and the `mfderiv`-transport `coeffIn` typecheck; `contMDiffAt_hom_bundle`
applies to `Form1` sections; the `c • mfderiv`-covector needed by `ofCoeffs` crosses the
`TangentSpace ↦ Bundle.Trivial` defeq; `coeffIn` additivity closes by `simp [coeffIn]`.
**CC1 stands as frozen — no re-freeze needed.**

One important pin-specific fact: at commit `5483982…` there is **no `Bundle.ContinuousLinearMap`
type** — it is only a *namespace* (`Mathlib/Topology/VectorBundle/Hom.lean`). The hom bundle is
always spelled as the lambda `fun x => E₁ x →SL[σ] E₂ x`, and **all** instances
(`Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace` :214, `.fiberBundle` :219,
`.vectorBundle` :224, `ContMDiffVectorBundle.continuousLinearMap`
`Geometry/Manifold/VectorBundle/Hom.lean:129`) are stated for that lambda with
`σ = RingHom.id 𝕜` (`→L[ℂ]` unfolds to `→SL[RingHom.id ℂ]`, so unification succeeds).
CC1's lambda spelling is the only workable one; the
`Bundle.ContinuousLinearMap (RingHom.id ℂ) … ` spelling would not even parse as a type.

Also pin-specific: charts are `OpenPartialHomeomorph X ℂ` (not `PartialHomeomorph`;
`ChartedSpace.atlas : Set (OpenPartialHomeomorph M H)`), so `e.target`/`e.source` are open and
`e.open_target` exists. Sections use the new `Cₛ^n⟮I; F, V⟯` / `T%` / `CMDiff` notation from
`Mathlib.Geometry.Manifold.Notation` (scoped `Manifold`).

**Naming convention for this unit**: `open scoped ContDiff` makes `ω` the smoothness exponent;
forms are therefore named `η`, `η'`, `θ` in Lean code (never `ω`).

---

## 1. File plan

```
Jacobian/Forms.lean            -- unit root: imports all, 5–15 line API docstring
Jacobian/Forms/Basic.lean      -- Form1 def, instances sanity, evaluation, ext via coeffAt
Jacobian/Forms/Coeffs.lean     -- coeffIn/coeffAt, transition rule, analyticity characterization
Jacobian/Forms/OfCoeffs.lean   -- Form1CoeffData, Form1.ofCoeffs, coeffIn_ofCoeffs
Jacobian/Forms/MDifferential.lean -- mdifferential f, coeffIn formula, linearity in f
Jacobian/Forms/Montel.lean     -- PLANAR Montel (no manifold imports; reused by finiteness-and-chi)
Jacobian/Forms/Finiteness.lean -- good covers, coefficient embedding J, Riesz, the instance
Jacobian/Forms/Genus.lean      -- genus (root-level, exact challenge signature), genus lemmas
```

Import skeleton (verified by the spike, ~12 s elaboration):
`Basic`: `Mathlib.Analysis.Complex.Basic`, `Mathlib.Geometry.Manifold.VectorBundle.Hom`,
`Mathlib.Geometry.Manifold.VectorBundle.Tangent`,
`Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection`.
`Coeffs` adds `Mathlib.Geometry.Manifold.MFDeriv.Atlas`, `Mathlib.Geometry.Manifold.MFDeriv.Tangent`,
`Mathlib.Geometry.Manifold.ContMDiff.Atlas`.
`MDifferential` adds `Mathlib.Geometry.Manifold.ContMDiffMFDeriv`.
`Montel` (planar only): `Mathlib.Analysis.Complex.LocallyUniformLimit`,
`Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli`, `Mathlib.Topology.ContinuousMap.Compact`,
`Mathlib.Analysis.Calculus.MeanValue`, `Mathlib.Topology.MetricSpace.Thickening`.
`Finiteness` adds `Mathlib.Analysis.Normed.Module.FiniteDimension`,
`Mathlib.Analysis.Normed.Group.Submodule`.
`Genus` adds `Mathlib.LinearAlgebra.Dimension.Finrank`.

Standing variables (every file):

```lean
open scoped ContDiff Manifold Bundle
open ContinuousLinearMap (inCoordinates)   -- inCoordinates is ContinuousLinearMap.inCoordinates

namespace RS
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
```

`T2Space`/`CompactSpace` are added only where needed (Finiteness, Genus); `ConnectedSpace` is
**never** needed in this unit (finiteness holds on any compact `X`); `genus` carries it only to
match the challenge signature.

---

## 2. Signatures

### 2.1 `Form1` and `genus` (CC1, spelled exactly as spiked)

```lean
-- Jacobian/Forms/Basic.lean
variable (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The space of global holomorphic 1-forms on `X`: bundled `C^ω` sections of the bundle of
`ℂ`-linear maps from the (holomorphic) tangent bundle to the trivial line bundle. -/
abbrev Form1 : Type _ :=
  Cₛ^ω⟮𝓘(ℂ); ℂ →L[ℂ] ℂ, fun x : X => TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial X ℂ x⟯
```

Instances (all found by TC inference, spike-verified):
`AddCommGroup (Form1 X)`, `Module ℂ (Form1 X)`
(`ContMDiffSection.instAddCommGroup`/`instModule`, `ContMDiffSection.lean:377/397` — they need
only `[∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)] [VectorBundle ℂ (ℂ →L[ℂ] ℂ) V]`, all
supplied by `Bundle.ContinuousLinearMap.*` + `TangentSpace` deriving + reducible
`Bundle.Trivial`), and
`ContMDiffVectorBundle ω (ℂ →L[ℂ] ℂ) (fun x : X => TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial X ℂ x) 𝓘(ℂ)`
(from `Hom.lean:129` + tangent `ω`-instance `Tangent.lean:336` + trivial-bundle instance
`Geometry/Manifold/VectorBundle/Basic.lean:586`). `Finset.sum`, `smul`, `sub` of forms all work.

Evaluation: for `η : Form1 X`, `x : X`, `v : TangentSpace 𝓘(ℂ) x`, the term `η x v : ℂ`
typechecks (`Bundle.Trivial X ℂ x` is `@[reducible]` ℂ). `DFunLike` gives `⇑η : ∀ x, …` and
`ContMDiffSection.ext`.

```lean
-- Jacobian/Forms/Genus.lean  (root level, EXACT challenge signature)
/-- The genus of a compact Riemann surface: the dimension of the space of global
holomorphic 1-forms. -/
def genus (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : ℕ :=
  Module.finrank ℂ (RS.Form1 X)

theorem genus_eq_zero_iff_subsingleton : genus X = 0 ↔ Subsingleton (RS.Form1 X)
  -- Module.finrank_zero_iff (needs the FiniteDimensional instance of §2.6) + rank/subsingleton API
```

### 2.2 The chart-coefficient API (`Coeffs.lean`) — the project workhorse

The transport of `1 ∈ ℂ` into `TangentSpace 𝓘(ℂ) p` is the `mfderiv` of the chart inverse; this
is the honest definition and it typechecks as-is (spiked):

```lean
/-- The coefficient function of a 1-form in the chart `e`: for `z ∈ e.target`,
`coeffIn e η z = η (e.symm z) (d(e.symm)_z 1)`, i.e. "η = (coeffIn e η) dz" in the chart.
Junk (unspecified; in practice `0`) off `e.target`. -/
noncomputable def coeffIn (e : OpenPartialHomeomorph X ℂ) (η : Form1 X) (z : ℂ) : ℂ :=
  η (e.symm z) (mfderiv 𝓘(ℂ) 𝓘(ℂ) e.symm z (1 : ℂ))

/-- Coefficient in the preferred chart, at the image of the base point. -/
noncomputable def coeffAt (x : X) (η : Form1 X) : ℂ := coeffIn (chartAt ℂ x) η (chartAt ℂ x x)
```

(If a raw-section version is needed before bundling — it is, in `OfCoeffs`/`Coeffs` — define
`coeffInFun e (σ : Π x, TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial X ℂ x) : ℂ → ℂ` identically and
set `coeffIn e η = coeffInFun e ⇑η := rfl`.)

**The canonical identification** (verified name): for the preferred chart at the base point the
transport is the identity —
`mfderivWithin_range_extChartAt_symm : mfderivWithin 𝓘(ℂ,ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) x).symm (Set.range 𝓘(ℂ)) (extChartAt 𝓘(ℂ) x x) = ContinuousLinearMap.id ℂ _`
(`MFDeriv/Atlas.lean`). Over `𝓘(ℂ)`, `Set.range 𝓘(ℂ) = univ` and `mfderivWithin_univ` collapses
this to `mfderiv`; `⇑(extChartAt 𝓘(ℂ) x).symm = ⇑(chartAt ℂ x).symm` by `mfld_simps`. Hence

```lean
theorem coeffAt_eq_apply_one (η : Form1 X) (x : X) :
    coeffAt x η = η x (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x).symm (chartAt ℂ x x) (1 : ℂ))  -- rfl-ish
theorem apply_eq_smul_coeffAt (η : Form1 X) (x : X) (v : TangentSpace 𝓘(ℂ) x) :
    η x v = (v : ℂ) * coeffAt x η
  -- 1-dim fiber: v = (v:ℂ) • (canonical vector); canonical vector = 1 under the identification
  -- above; CLM linearity. Concentrated defeq-abuse; prove once with `show`/`mfld_simps`,
  -- `set_option backward.isDefEq.respectTransparency false in` if unification balks.

@[ext] theorem Form1.ext_coeffAt {η η' : Form1 X} (h : ∀ x, coeffAt x η = coeffAt x η') : η = η'
```

Linearity (spiked: closes by `simp [coeffIn]`):

```lean
@[simp] theorem coeffIn_add  (e) (η η') (z) : coeffIn e (η + η') z = coeffIn e η z + coeffIn e η' z
@[simp] theorem coeffIn_smul (e) (c : ℂ) (η) (z) : coeffIn e (c • η) z = c * coeffIn e η z
@[simp] theorem coeffIn_zero (e) (z) : coeffIn e (0 : Form1 X) z = 0
-- same triple for coeffAt
```

**Transition rule** (CC1 orientation, checked by hand against `mfderiv_comp`):

```lean
open IsManifold in
theorem coeffIn_trans {e e' : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω X)
    (η : Form1 X) {z : ℂ} (hz : z ∈ e' '' (e.source ∩ e'.source)) :
    coeffIn e' η z = deriv (↑e ∘ ↑e'.symm) z * coeffIn e η (e (e'.symm z))
```

Proof plan: on the open set `W := e' '' (e.source ∩ e'.source)` (open: image of an open subset of
the source under an `OpenPartialHomeomorph`), `⇑e'.symm =ᶠ[𝓝 z] ⇑e.symm ∘ (⇑e ∘ ⇑e'.symm)`.
Apply `Filter.EventuallyEq.mfderiv_eq`, then the chain rule `mfderiv_comp` with:
`e.symm` MDifferentiable at `e (e'.symm z)` (`contMDiffOn_symm_of_mem_maximalAtlas` from
`ContMDiff/Atlas.lean:70` + `.mdifferentiableOn`/`.contMDiffAt`), and the planar transition
`τ := ⇑e ∘ ⇑e'.symm` differentiable at `z` (τ is a `contDiffGroupoid ω 𝓘(ℂ)` element on `W` by
`StructureGroupoid.compatible_of_mem_maximalAtlas he' he`; `ContDiffOn ℂ ω ↔ AnalyticOn` on the
open `W` via `contDiffOn_omega_iff_analyticOn`, `ContDiff/Defs.lean:763`). Finally on the model
`mfderiv 𝓘(ℂ) 𝓘(ℂ) τ z = fderiv ℂ τ z` (`mfderiv_eq_fderiv`, `MFDeriv/FDeriv.lean:113`),
`fderiv ℂ τ z 1 = deriv τ z` (`fderiv_deriv`/defn of `deriv`), and pull the scalar out of the CLM
composition.

**Analyticity, both directions.** Local planar bridge (self-contained; see "CC7 interaction"
below), for any complex Banach `F`:

```lean
theorem contMDiffAt_iff_analyticAt_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (f : X → F) (x : X) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, F) ω f x ↔ AnalyticAt ℂ (f ∘ ↑(chartAt ℂ x).symm) (chartAt ℂ x x)
  -- contMDiffAt_iff; extChartAt over the model = id; range 𝓘(ℂ) = univ;
  -- contDiffWithinAt_omega_iff_analyticWithinAt (ContDiff/Defs.lean:157) + analyticWithinAt_univ;
  -- ContinuousAt f x recovered from the analytic rep composed with the chart homeo.
```

The **section characterization** (the CC1 "coeffIn analytic iff η is ω-smooth"):

```lean
theorem contMDiffAt_section_iff_analyticAt_coeffInFun
    (σ : Π x : X, TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial X ℂ x) (x : X) :
    ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun p => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) p (σ p)) x ↔
    AnalyticAt ℂ (coeffInFun (chartAt ℂ x) σ) (chartAt ℂ x x)

theorem Form1.analyticAt_coeffAt (η : Form1 X) (x : X) :
    AnalyticAt ℂ (coeffIn (chartAt ℂ x) η) (chartAt ℂ x x)   -- ← of the above + η.contMDiff

open IsManifold in
theorem Form1.analyticOnNhd_coeffIn (η : Form1 X) {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) : AnalyticOnNhd ℂ (coeffIn e η) e.target
```

Proof plan for the characterization (all ingredient names verified at the pin):
1. `Bundle.contMDiffAt_section` (`Geometry/Manifold/VectorBundle/Basic.lean:210`): smoothness of
   the section at `x` ↔ smoothness of `rep := fun p => (trivializationAt (ℂ →L[ℂ] ℂ) V x ⟨p, σ p⟩).2`
   into `𝓘(ℂ, ℂ →L[ℂ] ℂ)`.
2. `hom_trivializationAt_apply` (`Topology/VectorBundle/Hom.lean:261`): `rep p =
   inCoordinates ℂ (TangentSpace 𝓘(ℂ)) ℂ (Bundle.Trivial X ℂ) x p x p (σ p)`.
3. For `p ∈ (chartAt ℂ x).source`, unfold `inCoordinates` (`inCoordinates_eq`): the codomain
   factor is the trivial bundle's `continuousLinearMapAt = id` (tiny `rfl`-level lemma), the
   domain factor is `(trivializationAt ℂ (TangentSpace 𝓘(ℂ)) x).symmL ℂ p =
   mfderivWithin (extChartAt 𝓘(ℂ) x).symm (range 𝓘(ℂ)) (extChartAt 𝓘(ℂ) x p)`
   (`TangentBundle.symmL_trivializationAt`, `MFDeriv/Atlas.lean:373`). Hence, evaluated at `1`,
   `rep p 1 = coeffInFun (chartAt ℂ x) σ (chartAt ℂ x p)` — bridging lemma
   `rep_apply_one_eq_coeffIn` proved once with `mfld_simps`.
4. A CLM `ℂ →L[ℂ] ℂ` is determined by its value at `1`: conjugate by the two continuous linear
   maps `ContinuousLinearMap.apply ℂ ℂ 1 : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ` and `c ↦ c • (.id ℂ ℂ)` (both
   directions preserve `AnalyticAt` via `ContinuousLinearMap.analyticAt` + `AnalyticAt.comp`).
5. Compose with `contMDiffAt_iff_analyticAt_comp` for the map `rep : X → (ℂ →L[ℂ] ℂ)` and rewrite
   `rep ∘ (chartAt ℂ x).symm` to `coeffInFun (chartAt ℂ x) σ` near the chart point
   (`EventuallyEq` on the open target; `AnalyticAt.congr`).

`analyticOnNhd_coeffIn`: at `z ∈ e.target`, put `p := e.symm z`; `coeffIn e η` agrees near `z`
with `deriv (↑(chartAt ℂ p) ∘ ↑e.symm) · * coeffIn (chartAt ℂ p) η (chartAt ℂ p (e.symm ·))`
(`coeffIn_trans` with `e := chartAt ℂ p`, `e' := e`; `chartAt ∈ maximalAtlas` via
`subset_maximalAtlas (chart_mem_atlas _ _)`); the transition and its `deriv` are analytic on the
open overlap image, and the preferred-chart coefficient is `AnalyticAt` at
`chartAt ℂ p p = (↑(chartAt ℂ p) ∘ ↑e.symm) z` by `Form1.analyticAt_coeffAt`. Product/composition
of `AnalyticAt`.

### 2.3 Constructor from compatible coefficient families (`OfCoeffs.lean`)

Design decision: the family is indexed by an **arbitrary chart family from the ω-maximal atlas
covering `X`** (not `chartAt`-charts only). Rationale: (i) the finiteness proof needs to
assemble a form from limits defined only on *shrunk* charts (`e.restr V` stays in the maximal
atlas: `StructureGroupoid.restr_mem_maximalAtlas`, `HasGroupoid.lean:185`,
`contDiffGroupoid` is `ClosedUnderRestriction`); (ii) dbar/canonical-forms build data on chart
disks, not on preferred charts. The `chartAt`-family is the instantiation `ι := X`,
`chart := chartAt ℂ`.

```lean
open IsManifold in
/-- Compatible analytic coefficient data for a holomorphic 1-form, over a covering family of
analytic charts. -/
structure Form1CoeffData (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (ι : Type*) where
  chart : ι → OpenPartialHomeomorph X ℂ
  mem_maximalAtlas : ∀ i, chart i ∈ maximalAtlas 𝓘(ℂ) ω X
  exists_mem : ∀ x : X, ∃ i, x ∈ (chart i).source
  coeff : ι → ℂ → ℂ
  analyticOnNhd : ∀ i, AnalyticOnNhd ℂ (coeff i) (chart i).target
  compat : ∀ i j, ∀ x ∈ (chart i).source ∩ (chart j).source,
    coeff j (chart j x) = deriv (↑(chart i) ∘ ↑(chart j).symm) (chart j x) * coeff i (chart i x)

noncomputable def Form1.ofCoeffs {ι : Type*} (D : Form1CoeffData X ι) : Form1 X

theorem Form1.coeffIn_ofCoeffs {ι} (D : Form1CoeffData X ι) (i : ι) :
    Set.EqOn (coeffIn (D.chart i) (Form1.ofCoeffs D)) (D.coeff i) (D.chart i).target

theorem Form1.ofCoeffs_coeffAt {ι} (D : Form1CoeffData X ι) {x : X} {i : ι}
    (hx : x ∈ (D.chart i).source) :
    coeffAt x (Form1.ofCoeffs D) =
      deriv (↑(D.chart i) ∘ ↑(chartAt ℂ x).symm) (chartAt ℂ x x) ⁻¹ * ...  -- or the transported
      -- form via coeffIn_trans; state whichever the finiteness proof consumes (see below)
```

Underlying section (spiked shape — the `c • mfderiv` covector crosses the `Trivial` defeq):
`σ x := D.coeff i₀ (D.chart i₀ x) • (mfderiv 𝓘(ℂ) 𝓘(ℂ) (D.chart i₀) x : …)` where
`i₀ := (D.exists_mem x).choose`. Smoothness at `x₀`: pick `i` with `x₀ ∈ source i`;
show `coeffInFun (chartAt ℂ x₀) σ` agrees near the chart point with
`deriv (↑(D.chart i) ∘ ↑(chartAt ℂ x₀).symm) · * D.coeff i ((D.chart i) ((chartAt ℂ x₀).symm ·))`
— pointwise from the definition of `σ` by the chain rule
(`mfderiv (D.chart i₀) p ∘L mfderiv (chartAt ℂ x₀).symm z = mfderiv (↑(D.chart i₀) ∘ ↑(chartAt ℂ x₀).symm)‑style
composition collapsing to a `deriv` factor, as in `coeffIn_trans`), with `compat` collapsing the
pointwise choice `i₀ = i₀(p)` to the fixed `i`; this function is `AnalyticAt` at the chart point
(product/composition, `D.analyticOnNhd`), so `contMDiffAt_section_iff_analyticAt_coeffInFun`
applies. `coeffIn_ofCoeffs` is the same computation read at a general `z ∈ target`.
Uniqueness/ext against any other form with the same coefficients: `Form1.ext_coeffAt` +
`coeffIn_trans`.

### 2.4 `mdifferential` (`MDifferential.lean`)

Holomorphic 1-forms only — no meromorphic machinery here (meromorphic 1-forms are later `f • η`
pairs in canonical-forms/meromorphic-trace). Downstream (canonical-forms seeds `K` from `d` of a
holomorphic representative in charts; paths-and-integrals wants `∫γ (mdifferential f) = f∘γ|₀¹`).

```lean
/-- The differential of a holomorphic function, as a holomorphic 1-form. -/
noncomputable def mdifferential (f : X → ℂ) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : Form1 X :=
  ⟨fun x => (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x :
      TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial X ℂ x), smoothness_proof⟩

open IsManifold in
theorem coeffIn_mdifferential {e : OpenPartialHomeomorph X ℂ} (he : e ∈ maximalAtlas 𝓘(ℂ) ω X)
    {f : X → ℂ} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Set.EqOn (coeffIn e (mdifferential f hf)) (deriv (f ∘ ↑e.symm)) e.target

@[simp] theorem mdifferential_add / mdifferential_smul / mdifferential_const  -- cheap; d is ℂ-linear
```

Smoothness proof: `ContMDiffAt.mfderiv (f := fun _ y => f y) (g := id)`
(`ContMDiffMFDeriv.lean:225`; `hmn : ω + 1 ≤ ω` holds since `ω + 1 = ω` in `WithTop ℕ∞`) gives
`CMDiffAt ω (inTangentCoordinates 𝓘(ℂ) 𝓘(ℂ) id f (fun x => mfderiv 𝓘(ℂ) 𝓘(ℂ) f x) x₀) x₀`; align
with the hom-bundle rep required by `contMDiffAt_section`: both unfold to
`(codomain triv CLM) ∘L mfderiv f p ∘L (tangent symmL)`, and the codomain factors are the
identity on both sides — trivial bundle by `rfl`, tangent-over-model-ℂ by
`Trivialization.continuousLinearMapAt_model_space`/`inCoordinates_tangent_bundle_core_model_space`
(`Tangent.lean:501`). One bridging lemma, `mfld_simps`. The `coeffIn` formula is the chain rule
again: `mfderiv f p ∘L mfderiv e.symm z = mfderiv (f ∘ ↑e.symm) z = fderiv ℂ (f ∘ ↑e.symm) z`,
evaluated at 1 (`fderiv_deriv`).

Also provided here (cheap, used by canonical-forms to build `h·η` with holomorphic `h`, and by
finiteness-and-chi test elements):

```lean
noncomputable def Form1.smulFun (f : X → ℂ) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (η : Form1 X) :
    Form1 X := ⟨fun x => f x • η x, hf.smul_section η.contMDiff⟩   -- ContMDiff.smul_section
@[simp] theorem coeffIn_smulFun : coeffIn e (Form1.smulFun f hf η) z = f (e.symm z) * coeffIn e η z
```

### 2.5 Planar Montel (`Montel.lean` — reusable, no manifold imports)

Stated for restriction families in `C(K, ℂ)` — the exact currency of both this unit's finiteness
proof and finiteness-and-chi's compact-operator argument
(via `isCompactOperator_iff_isCompact_closure_image_closedBall`).

```lean
namespace RS
/-- The set of restrictions to a compact `K` of functions holomorphic on an open `Ω ⊇ K` and
bounded by `C` there. -/
def montelFamily (Ω : Set ℂ) (K : Set ℂ) (C : ℝ) : Set C(K, ℂ) :=
  {f | ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ (∀ z ∈ Ω, ‖g z‖ ≤ C) ∧ ∀ z : K, f z = g z}

/-- **Montel's theorem**, compactness form. -/
theorem isCompact_closure_montelFamily {Ω K : Set ℂ} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (C : ℝ) : IsCompact (closure (montelFamily Ω K C))
```

(The statement needs only the compact-open topology on `C(K,ℂ)`, which always exists; inside the
proof `haveI := isCompact_iff_compactSpace.mp hK` unlocks the sup-norm instances of
`Topology/ContinuousMap/Compact.lean`, whose topology is the compact-open one.)

Proof plan:
1. **Cauchy estimate** (helper, exported for reuse):
   `theorem norm_deriv_le_of_bounded {g : ℂ → ℂ} (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω)
   (hC : ∀ w ∈ Ω, ‖g w‖ ≤ C) {z r} (hr : 0 < r) (hball : Metric.closedBall z r ⊆ Ω) :
   ‖deriv g z‖ ≤ C / r` — from `Complex.cderiv_eq_deriv` + `Complex.norm_cderiv_le`
   (`Analysis/Complex/LocallyUniformLimit.lean:46/:50`; these ARE mathlib's usable Cauchy
   estimates — there is no `Complex.norm_deriv_le_*`).
2. `IsCompact.exists_cthickening_subset_open hK hΩ hKΩ` (`Thickening.lean:443`): get `δ > 0`,
   `Metric.cthickening δ K ⊆ Ω`.
3. **Equicontinuity**: for `f = g|_K` in the family and `z w ∈ K` with `‖z - w‖ < δ/2`: every
   `y ∈ segment ℝ z w` has `Metric.closedBall y (δ/2) ⊆ cthickening δ K`, so `‖deriv g y‖ ≤ 2C/δ`
   by step 1; `Convex.norm_image_sub_le_of_norm_deriv_le` on `Metric.ball z (δ/2)`-type convex
   sets (or `norm_image_sub_le_of_norm_deriv_le_segment`) gives `‖g z - g w‖ ≤ (2C/δ)‖z - w‖`.
   Uniform Lipschitz ⇒ `Equicontinuous ((↑) : montelFamily … → K → ℂ)` (`Metric.equicontinuous`
   ε-δ unfold).
4. Transport through `ContinuousMap.linearIsometryBoundedOfCompact`
   (`Topology/ContinuousMap/Compact.lean:298`) and apply
   `BoundedContinuousFunction.arzela_ascoli` (`Bounded/ArzelaAscoli.lean`, third version:
   `(s := Metric.closedBall 0 C)` compact in ℂ, pointwise range containment from the bound,
   equicontinuity from step 3) ⇒ `IsCompact (closure …)`; pull back along the isometric
   homeomorphism.

(A sequential-extraction corollary `montel_seq` on an open Ω via compact exhaustion is a
possible later add for finiteness-and-chi, derivable from this + `IsCompact.isSeqCompact`;
NOT built now — the set form is the atom that unit needs for `IsCompactOperator`.)

### 2.6 Finiteness (`Finiteness.lean`) — detailed plan

Goal: `instance [T2Space X] [CompactSpace X] : FiniteDimensional ℂ (Form1 X)`.
`ConnectedSpace` is not used. Full route (numbers refer to steps below):
compact `X` ⇒ finite nested chart cover (1) ⇒ linear coefficient embedding `J` into a finite
product of `C(K_i, ℂ)` (2,3) ⇒ unit ball of `range J` is closed (5) inside a product of Montel
compacta (4) hence compact ⇒ Riesz on the submodule (6) ⇒ transfer along `J` (6).

1. **Good covers** (where `CompactSpace` + `T2Space` enter, and nowhere else).
   `lemma exists_goodCover [T2Space X] [CompactSpace X] : ∃ (n : ℕ) (c : Fin n → X)
   (V W : Fin n → Set X), (∀ i, IsOpen (V i)) ∧ (∀ i, IsOpen (W i)) ∧
   (∀ i, closure (V i) ⊆ W i) ∧ (∀ i, closure (W i) ⊆ (chartAt ℂ (c i)).source) ∧
   ⋃ i, V i = Set.univ`.
   Proof: compact+T2 ⇒ `LocallyCompactSpace X` (instance chain: `CompactSpace ⇒
   WeaklyLocallyCompactSpace` (`LocallyCompact.lean:36`) + T2 upgrade in
   `Separation/Hausdorff.lean`); apply `exists_compact_subset`
   (`Topology/Compactness/LocallyCompact.lean:148`) twice per point (interiors of the two nested
   compacts give `V_x ⊆ closure V_x ⊆ W_x ⊆ closure W_x ⊆ source`; closures inside compacts are
   automatic since compacts are closed in T2); finish with
   `isCompact_univ.elim_finite_subcover` on `{V_x}` and reindex by `Fin n`.
   Notation below: `e i := chartAt ℂ (c i)`, `O i := e i '' V i` (open,
   `OpenPartialHomeomorph` image of open subset of source), `K i := e i '' closure (V i)`
   (compact ⊆ target), `Ω i := e i '' W i` (open), `L i := e i '' closure (W i)` (compact
   ⊆ target). Facts: `K i ⊆ Ω i ⊆ L i ⊆ (e i).target`, and `K i = closure (O i)` (chart is a
   homeo of `source → target`; two-line inclusion argument), so `O i` is dense in `K i`.

2. **The coefficient embedding.** With a fixed good cover (obtained by `choose` at the top of a
   `section`), `haveI` the `CompactSpace (K i)` instances, and set `P := Π i, C(K i, ℂ)`
   (`Fintype (Fin n)` ⇒ `Pi.normedAddCommGroup`/`Pi.normedSpace`; each factor by
   `Topology/ContinuousMap/Compact.lean:179`). Define
   `J : Form1 X →ₗ[ℂ] P`, `J η i := ⟨fun z => coeffIn (e i) η z, continuity⟩`
   (continuity: `Form1.analyticOnNhd_coeffIn` + `AnalyticOnNhd.continuousOn` + restrict;
   linearity: `coeffIn_add`, `coeffIn_smul` + `ContinuousMap.ext`).
   The norm `‖J η‖ = max_i sup_{K i} ‖coeffIn (e i) η‖` is exactly CC1's prescribed norm — it
   lives on `P`, never as an instance on `Form1 X` (no pollution).

3. **`J` is injective**: if `J η = 0` then for any `x` pick `i` with `x ∈ V i`; the transition
   rule `coeffIn_trans` transports `coeffIn (e i) η = 0` near `e i x ∈ K i` to
   `coeffAt x η = deriv (…) (…) * 0 = 0`; conclude `η = 0` by `Form1.ext_coeffAt`.

4. **Uniform bound transfer** (the Montel feed): `lemma exists_montel_bound : ∃ C : ℝ, ∀ η,
   ‖J η‖ ≤ 1 → ∀ i, ∀ z ∈ Ω i, ‖coeffIn (e i) η z‖ ≤ C`.
   Proof: `C := 1 + max_{i,j} D i j`, `D i j := sSup of ‖deriv (↑(e j) ∘ ↑(e i).symm)‖` over the
   compact `e i '' (closure (W i) ∩ closure (V j))` (⊆ the open overlap image where the
   transition is analytic, so `deriv` is continuous there: `IsCompact.exists_forall_ge` /
   `sSup`-boundedness; empty pieces contribute `0`). For `z ∈ Ω i`, `p := (e i).symm z ∈ W i`
   lies in some `V j`; `coeffIn_trans` (with `e := e j`, `e' := e i`) gives
   `‖coeffIn (e i) η z‖ ≤ D i j * ‖coeffIn (e j) η (e j p)‖ ≤ D i j * 1 ≤ C` since
   `e j p ∈ K j`. Consequently the `i`-th component of `J` maps the unit ball of `range J` into
   `montelFamily (Ω i) (K i) C` (witness `g := coeffIn (e i) η`, holomorphic on `Ω i` by
   `analyticOnNhd_coeffIn`, bounded by step 4). Let `M i := closure (montelFamily (Ω i) (K i) C)`
   — compact by `isCompact_closure_montelFamily`; `T := Set.univ.pi M` is compact in `P`
   (`isCompact_univ_pi`).

5. **The unit ball of `range J` is closed in `P`.**
   `B := (Metric.closedBall (0 : P) 1) ∩ Set.range J`; show `IsClosed B` sequentially (`P` is a
   metric space): take `η m` with `J (η m) → f`. For each `i`, uniform convergence on `K i`
   (`⊇ O i`) gives `TendstoLocallyUniformlyOn` on the open `O i`
   (`TendstoUniformlyOn.tendstoLocallyUniformlyOn`, `LocallyUniformConvergence.lean:86`);
   **Weierstrass** `TendstoLocallyUniformlyOn.differentiableOn`
   (`Analysis/Complex/LocallyUniformLimit.lean:135`) makes the limit `g i := f i ∘ (incl)`
   holomorphic on `O i`, hence `AnalyticOnNhd` (`DifferentiableOn.analyticOnNhd`,
   `CauchyIntegral.lean:632`). The pointwise `compat` identities for the shrunk charts
   `(e i).restr (V i)` (in the maximal atlas by `StructureGroupoid.restr_mem_maximalAtlas`)
   pass to the limit (equalities of convergent sequences). Assemble
   `D : Form1CoeffData X (Fin n)` and `η∞ := Form1.ofCoeffs D`. Then `J η∞ = f`: on `O i` by
   `Form1.coeffIn_ofCoeffs` (+ `coeffIn` of a chart vs its restriction agree on the restricted
   target — small lemma, both are the same `mfderiv` formula), and on all of `K i = closure (O i)`
   by `Continuous.ext_on` (both sides continuous, agree on the dense `O i`). `‖f‖ ≤ 1` since
   the closed ball is closed. Hence `f ∈ B`.

6. **Riesz and transfer.** `S := LinearMap.range J` with the induced norm
   (`Submodule.normedAddCommGroup`, `Submodule.normedSpace` — instances on the subtype, no
   pollution). The subtype coe is an isometric embedding, so
   `IsCompact (Metric.closedBall (0 : S) 1)` ⟺ `IsCompact B` (`Topology.IsEmbedding.isCompact_iff`;
   the coe-image of the ball is exactly `B`). `B` is closed (5) inside compact `T` (4):
   `IsCompact.of_isClosed_subset`. Riesz:
   `FiniteDimensional.of_isCompact_closedBall₀ ℂ one_pos …`
   (`Analysis/Normed/Module/FiniteDimension.lean:457`) gives `FiniteDimensional ℂ S`; transfer
   along `(LinearEquiv.ofInjective J hJ).symm` via `LinearEquiv.finiteDimensional`
   (`FiniteDimensional/Defs.lean:252`):

```lean
instance [T2Space X] [CompactSpace X] : FiniteDimensional ℂ (Form1 X)
```

---

## 3. Spike report (`scratch_forms.lean`, kept at project root)

- Compiles clean: `lake env lean scratch_forms.lean`, ~11–12 s wall, 79 lines.
- Imports needed beyond the obvious: `Mathlib.Analysis.Complex.Basic` (the bundle files do NOT
  pull in `ℂ`!), `Mathlib.Geometry.Manifold.MFDeriv.Atlas` (for
  `mfderivWithin_range_extChartAt_symm`); `inCoordinates` must be opened from
  `ContinuousLinearMap`.
- `(1 : ℂ)` is accepted where `TangentSpace 𝓘(ℂ) z` is expected (defeq unification), and the
  codomain defeq `TangentSpace 𝓘(ℂ) (e p) ↦ Bundle.Trivial X ℂ p` is accepted in a `def` with an
  expected type ascription — both load-bearing for `coeffIn`/`ofCoeffs`.
- `contMDiffAt_hom_bundle` rewrites on a Form1 section goal (needs the `TotalSpace.mk'` spelling
  of the section, as in `Bundle.contMDiffAt_section`).

## 4. Risks & fallbacks

- **Defeq-abuse concentration.** All `TangentSpace ≡ ℂ ≡ Bundle.Trivial` crossings are confined
  to `Basic.lean`/`Coeffs.lean` (`apply_eq_smul_coeffAt`, `rep_apply_one_eq_coeffIn`,
  `coeffAt_eq_apply_one`). Mathlib's own bundle files repeatedly need
  `set_option backward.isDefEq.respectTransparency false in` for exactly these moves — expect to
  use it locally; do not spread it.
- **`inCoordinates`-unfolding friction** (step 3 of the characterization): mitigated by proving
  ONE bridging lemma with `mfld_simps` and never unfolding elsewhere. If
  `TangentBundle.symmL_trivializationAt` resists rewriting under `𝓘(ℂ)`, the fallback is
  `symmL_trivializationAt_eq_core` + `tangentBundleCore_coordChange_achart` (pure
  `fderivWithin`-level, same content).
- **CC7 interaction.** The `ContMDiffAt ↔ AnalyticAt` bridge is implemented *locally* for maps
  `X → F` (planar source only, no ℝ-structure needed), keeping holomorphic-forms a foundation
  unit with no dependence on surfaces-and-charts. If that unit ships an equivalent bridge, ours
  moves to a marked `Compat` section for later reconciliation (filed in
  `docs/requests/surfaces-and-charts.md` as a non-blocking note).
- **Mean-value inequality over ℂ** (Montel step 3): if
  `Convex.norm_image_sub_le_of_norm_deriv_le` has 𝕜-generality friction, restrict scalars to ℝ
  (`DifferentiableAt.restrictScalars`) and use the real-segment version — planar, harmless.
- **Montel-closedness relies on `ofCoeffs`** with *restricted* charts; the needed
  `restr_mem_maximalAtlas` and `ClosedUnderRestriction (contDiffGroupoid ω 𝓘(ℂ))` are verified
  present. If the `coeffIn (e.restr V) = coeffIn e on (e.restr V).target` lemma turns fiddly,
  note both sides are literally the same `mfderiv` expression (`(e.restr V).symm` agrees with
  `e.symm` on the restricted target eventually) — an `EventuallyEq.mfderiv_eq` one-liner.
- **FALLBACK (if the bundle route had failed — it did NOT):** hand-rolled
  `structure Form1Raw X := (cov : Π x, TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ) (analytic : ∀ x, AnalyticAt ℂ (chart-coeff) …)`
  with a hand-written `Module ℂ` instance. Cost: ~+800 lines (module structure, ext, all
  smoothness API by hand), loses `ContMDiffAt.mfderiv` (mdifferential smoothness manual), loses
  the mathlib hom-bundle lemma ecosystem, and reintroduces the blueprint's section-sum hazard.
  Downstream API (`coeffIn` etc.) would be unchanged — consumers are insulated either way, since
  ALL downstream units use `coeffIn`, never bundle internals (CC1 rule).
- **Compile time**: manifold+bundle imports cost ~12 s per file at elaboration start — acceptable;
  keep `Montel.lean` free of manifold imports so finiteness-and-chi can import it cheaply.

## 5. Downstream consumers (what they may rely on)

- **paths-and-integrals (CC6)**: `coeffIn`, `coeffAt`, `Form1.analyticOnNhd_coeffIn` (local
  primitives of analytic coefficients on chart disks), `coeffIn_trans`, ℂ-linearity of `coeffIn`,
  `coeffIn_mdifferential` (for `∫γ dF`).
- **jacobian-construction (CC9)**: `FiniteDimensional ℂ (Form1 X)` (hence `Module.finBasis`),
  `genus`, the `Module ℂ (Form1 X)` structure for period functionals `Form1 X →ₗ[ℂ] ℂ`.
- **residue-calculus / canonical-forms / meromorphic-trace**: `Form1` stays HOLOMORPHIC;
  meromorphic 1-forms are later pairs `(f, η)` ~ `f • η` — only `Form1.smulFun` and `coeffIn`
  transition data are consumed from here. Do not add meromorphic sections to this unit.
- **finiteness-and-chi**: `RS.montelFamily`, `RS.isCompact_closure_montelFamily`,
  `RS.norm_deriv_le_of_bounded` (Cauchy estimate) — via `Jacobian/Forms/Montel.lean` only.
- **sphere-topology / cech-h1-genus / riemann-roch / headline**: `genus`,
  `genus_eq_zero_iff_subsingleton`, `Form1.ext_coeffAt`.
- **dbar**: the `(0,1)`-analogue is NOT here (its `restrictScalars`-J-structure is a different
  bundle); dbar builds its own, reusing only the `coeffIn` design pattern.
