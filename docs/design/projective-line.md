# Design: projective-line (`Jacobian/ProjectiveLine/`)

Owner of **CC5** (frozen in `docs/design/core-choices.md`). Blueprint entry:
`clean_room_blueprint.md` §projective-line. Reference: Forster §5 (book 22–26 = PDF 28–32; only
Forster 5.4 "P¹ compact Riemann surface" is formalized here — the ℳ(ℙ¹) = rational functions
part belongs to later units). `ℙ¹ := OnePoint ℂ`.

All mathlib names below were verified in `.lake/packages/mathlib` source at the pin
(`548398201`); items marked **[spiked]** were verified by compilation (`scratch_p1.lean`,
project root, gitignored; compiles clean in 6.5 s — see §7).

**Headline recon result (changes the plan of record).** Mathlib at the pin ALREADY contains the
topological homeomorphism to the 2-sphere:
`onePointEquivSphereOfFinrankEq` (`Topology/Compactification/OnePoint/Sphere.lean:34`)
specializes **[spiked]** in one line to
`OnePoint ℂ ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1` — the exact type in the
challenge's `genus_eq_zero_iff_homeo`. The hand-built stereographic route from the task brief is
NOT needed (kept in §6 as fallback). Likewise all point-set topology instances
(`CompactSpace`, `T2Space`, `ConnectedSpace`, no isolated points) are **automatic** from mathlib
instances **[spiked]**. What this unit genuinely builds: the two-chart complex-manifold
structure, the inversion involution, the holomorphy transfer kit, and the genus-0 theorem.

---

## 1. Mathlib inventory for this unit (verified at the pin)

`Topology/Compactification/OnePoint/Basic.lean` (649 lines, mature):

- Type & points: `OnePoint X := Option X`; `OnePoint.infty` with scoped notation `∞`;
  coercion `some : X → OnePoint X`; `coe_injective` (`:98`), `coe_eq_coe` (`:102`),
  `coe_ne_infty` (`:106`), `infty_ne_coe` (`:110`), `ne_infty_iff_exists` (`:150`),
  recursor `OnePoint.rec` (cases_eliminator, `:115`), `OnePoint.elim` (= `Option.elim`, `:121`),
  `OnePoint.map`, `compl_infty : {∞}ᶜ = range (↑)` (`:144`), `compl_range_coe` (`:141`).
- Topology: `isOpen_def` (`:220`), `isOpenEmbedding_coe` (`:271`), `isOpen_range_coe`,
  `isClosed_infty` (`:277`), `nhds_coe_eq (x) : 𝓝 ↑x = map (↑) (𝓝 x)` (`:281`),
  `comap_coe_nhds` (`:291`).
- **The `𝓝 ∞` characterization** (task's "verify `OnePoint.nhds_infty_eq`" — verified, exact
  names): `nhdsNE_infty_eq : 𝓝[≠] (∞ : OnePoint X) = map (↑) (coclosedCompact X)` (`:299`),
  `nhds_infty_eq : 𝓝 ∞ = map (↑) (coclosedCompact X) ⊔ pure ∞` (`:317`),
  `tendsto_coe_infty : Tendsto (↑) (coclosedCompact X) (𝓝 ∞)` (`:320`),
  `hasBasis_nhds_infty` (`:324`), `continuousAt_infty'` (`:354`),
  `continuousAt_coe : ContinuousAt f ↑x ↔ ContinuousAt (f ∘ (↑)) x` (`:363`),
  `continuous_iff` (`:367`), `nhdsNE_sup_pure : 𝓝[≠] a ⊔ pure a = 𝓝 a`
  (`Topology/NhdsWithin.lean:289`).
- Instances: `CompactSpace (OnePoint X)` unconditional (`:499`); `T1Space` (`:514`);
  `NormalSpace (OnePoint X)` for `[WeaklyLocallyCompactSpace X] [R1Space X]` (`:523`) — the
  file's own `example` (`:539`) confirms `T4Space (OnePoint X)` (hence `T2Space`) synthesizes
  for locally compact T2 `X`; `ConnectedSpace (OnePoint X)` for
  `[PreconnectedSpace X] [NoncompactSpace X]` (`:542`); `nhdsNE_coe_neBot`/`nhdsNE_infty_neBot`/
  `nhdsNE_neBot` (`:296/:309/:313`) — no isolated points.
  For `X := ℂ` the hypotheses are instances: `ProperSpace ℂ` (⇒ locally compact),
  `NormedField.noncompactSpace` (`Analysis/Normed/Module/Basic.lean:248`),
  `NormedSpace.instPathConnectedSpace` (`Analysis/Normed/Module/Convex.lean:168`), so
  **`CompactSpace`, `T2Space`, `ConnectedSpace (OnePoint ℂ)`, and `∀ x, (𝓝[≠] x).NeBot` are all
  `inferInstance`** [spiked]. Do NOT re-prove connectedness — the dense-coe-image route in the
  task brief is already exactly mathlib's proof.
- Uniqueness of compactifications: `equivOfIsEmbeddingOfRangeEq` (`:579`) — used by mathlib's
  sphere file; `Homeomorph.onePointCongr` (`:628`).
- `OnePoint/Sphere.lean`: `onePointHyperplaneHomeoUnitSphere` (`:25`),
  `onePointEquivSphereOfFinrankEq {ι V} [Fintype ι] [AddCommGroup V] [Module ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
  [T2Space V] (h : finrank ℝ V + 1 = Fintype.card ι) :
  OnePoint V ≃ₜ sphere (0 : EuclideanSpace ℝ ι) 1` (`:34`).
- `OnePoint/ProjectiveLine.lean`: set-theoretic `equivProjectivization : OnePoint K ≃ ℙ K (Fin 2 → K)`
  and a set-theoretic Möbius `MulAction (GL (Fin 2) K) (OnePoint K)` (`:127`) — available extras,
  consumed by nothing in our plan.
- **No** `ChartedSpace`/`IsManifold`/`ContMDiff` for any `OnePoint X` anywhere (re-verified).

Planar/filter atoms: `Filter.tendsto_inv₀_nhdsNE_zero : Tendsto Inv.inv (𝓝[≠] 0) (cobounded α)`
and `Filter.tendsto_inv₀_cobounded : Tendsto Inv.inv (cobounded α) (𝓝 0)`
(`Analysis/Normed/Field/Lemmas.lean:95/:92`, normed division ring);
`Metric.cobounded_eq_cocompact` (proper spaces, `Topology/MetricSpace/Bounded.lean`);
`Filter.coclosedCompact_eq_cocompact` (R₁ spaces, `Topology/Separation/Basic.lean:1104`);
`continuousAt_inv₀` (`Topology/Algebra/GroupWithZero.lean:83`);
`analyticAt_inv {z : 𝕝} (hz : z ≠ 0) : AnalyticAt 𝕜 Inv.inv z`, `analyticOnNhd_inv`,
`AnalyticAt.inv` (`Analysis/Analytic/Constructions.lean:876/:881/:897`);
`analyticAt_id`/`analyticOnNhd_id` (`Analysis/Analytic/Linear.lean:156/:163`);
`deriv_inv : deriv (fun x => x⁻¹) x = -(x ^ 2)⁻¹` (`Analysis/Calculus/Deriv/Inv.lean:66`);
Liouville `Differentiable.eq_const_of_tendsto_cocompact [Nontrivial E]
(hf : Differentiable ℂ f) (hb : Tendsto f (cocompact E) (𝓝 c)) : f = Function.const E c`
(`Analysis/Complex/Liouville.lean:135`); `tendsto_norm_cobounded_atTop`
(`Analysis/Normed/Group/Bounded.lean:50`); `squeeze_zero_norm'`
(`Analysis/Normed/Group/Continuity.lean`); `IsCompact.exists_bound_of_continuousOn`;
`Complex.finrank_real_complex : finrank ℝ ℂ = 2`
(`LinearAlgebra/Complex/FiniteDimensional.lean:31`);
`Module.finrank_zero_of_subsingleton` (`LinearAlgebra/Dimension/Finite.lean:352`);
`Diffeomorph I J M N n` with fields `contMDiff_toFun`/`contMDiff_invFun` and scoped notation
`M ≃ₘ^n⟮I, J⟯ N` (`Geometry/Manifold/Diffeomorph.lean:81`);
`Topology.IsOpenEmbedding.toOpenPartialHomeomorph` (`Topology/OpenPartialHomeomorph/Basic.lean:244`;
NOT used — see §3.2 junk-value discussion); `Homeomorph.toOpenPartialHomeomorph` (+ `_source`,
`_target`, `_apply` mfld_simps, `Topology/OpenPartialHomeomorph/Defs.lean:194`);
`OpenPartialHomeomorph` fields = `PartialEquiv` + `open_source/open_target/
continuousOn_toFun/continuousOn_invFun` (`Defs.lean:54`).

From our own units: `RS.chartedSpaceOfFamily` / `RS.isManifold_of_family` (+ `@[simp]`
`chartedSpaceOfFamily_chartAt`/`_atlas`) from `Jacobian/Surface/ChartedSpaceKit.lean` (BUILT);
`RS.contMDiffAt_iff_analyticAt_writtenInExtChartAt`, `RS.contMDiffAt_iff_analyticAt`
from `Jacobian/Surface/Bridges.lean` (BUILT); `RS.Form1`, `RS.coeffIn`, `RS.coeffAt`,
`RS.coeffIn_trans` (orientation confirmed in the BUILT `Jacobian/Forms/Coeffs.lean:233`),
`RS.Form1.ext_coeffAt` (BUILT, `Coeffs.lean:201`), `coeffIn_zero` (BUILT),
`RS.Form1.analyticOnNhd_coeffIn` and `genus` (frozen in `docs/design/holomorphic-forms.md`
§2.2/§2.1; Forms unit in flight — see risk R1).

**Notation gotcha.** Both `open scoped ContDiff` (`∞ = ((⊤:ℕ∞) : ℕ∞ω)`) and
`open scoped OnePoint` (`∞ = OnePoint.infty`) define scoped `∞`. Files opening both (all our
manifold files) must disambiguate by expected type; write `(∞ : OnePoint ℂ)` in statements and
prefer `OnePoint.infty` in `def` bodies if elaboration balks.

---

## 2. File plan (build order)

| # | File | Content | Est. lines | Key imports (beyond earlier files) |
|---|------|---------|-----------|-------------------------------------|
| 1 | `Jacobian/ProjectiveLine/Inversion.lean` | `inversion`, involutivity, continuity (the `𝓝 ∞` filter work), `inversionHomeomorph` | ~160 | `Mathlib.Topology.Compactification.OnePoint.Basic`, `Mathlib.Analysis.Normed.Field.Lemmas`, `Mathlib.Analysis.Complex.Basic` |
| 2 | `Jacobian/ProjectiveLine/Charts.lean` | `coeChart`, `invChart`, `ChartedSpace` + `IsManifold` instances, `chartAt`/atlas simp lemmas, maximal-atlas membership, `Nontrivial`, instance smoke `example`s | ~260 | `Jacobian.Surface`, `Mathlib.Analysis.Analytic.Constructions` |
| 3 | `Jacobian/ProjectiveLine/Holomorphy.lean` | transfer kit: `contMDiff_coe`, the two `contMDiffAt_iff`s, pole constructor, meromorphy converse, `contMDiff_inversion`, `inversionDiffeomorph` | ~300 | `Mathlib.Analysis.Meromorphic.Order`, `Mathlib.Geometry.Manifold.Diffeomorph` |
| 4 | `Jacobian/ProjectiveLine/Sphere.lean` | `homeoSphere` (challenge bridge) | ~30 | `Mathlib.Topology.Compactification.OnePoint.Sphere`, `Mathlib.LinearAlgebra.Complex.FiniteDimensional` |
| 5 | `Jacobian/ProjectiveLine/GenusZero.lean` | `Form1 (OnePoint ℂ)` is trivial; `genus (OnePoint ℂ) = 0` | ~220 | `Jacobian.Forms` (needs Coeffs + Genus, see R1), `Mathlib.Analysis.Complex.Liouville` |
| 6 | `Jacobian/ProjectiveLine.lean` | unit root, API docstring, register in `Jacobian.lean` | ~30 | — |

Files 1–4 are buildable **now** (Surface is complete); file 5 additionally needs the in-flight
Forms deliverables `Form1.analyticOnNhd_coeffIn` and `genus` (both frozen in that unit's design).
Blueprint lists a dependency on paths-and-integrals; in fact **nothing from `Path/` is
consumed** — the real dependencies are Surface (built) and Forms (for file 5 only). Everything
lives in `namespace RS.P1` (declarations referenced below without prefix), except `RS.genus_onePoint`.
Standing opens per file: `open scoped ContDiff Manifold OnePoint` and `open Set Filter Topology OnePoint`.
Scoped notation, declared in the root file:
`scoped[RS.P1] notation "ℙ¹" => OnePoint ℂ` (doc-comment it; challenge statements never need it).

---

## 3. Exported signatures

### 3.1 `Inversion.lean`

```lean
namespace RS.P1

/-- Inversion `z ↦ z⁻¹` on the Riemann sphere, with `∞ ↦ 0` and `0 ↦ ∞`. -/
def inversion : OnePoint ℂ → OnePoint ℂ :=
  fun p => p.elim ((0 : ℂ) : OnePoint ℂ)
    fun z => if z = 0 then (∞ : OnePoint ℂ) else ((z⁻¹ : ℂ) : OnePoint ℂ)

@[simp] theorem inversion_infty : inversion ∞ = ((0 : ℂ) : OnePoint ℂ)
@[simp] theorem inversion_coe_zero : inversion ((0 : ℂ) : OnePoint ℂ) = ∞
theorem inversion_coe {z : ℂ} (hz : z ≠ 0) : inversion z = ((z⁻¹ : ℂ) : OnePoint ℂ)
theorem inversion_involutive : Function.Involutive inversion
@[simp] theorem inversion_inversion (p : OnePoint ℂ) : inversion (inversion p) = p
theorem inversion_eq_infty_iff {p : OnePoint ℂ} : inversion p = ∞ ↔ p = ((0 : ℂ) : OnePoint ℂ)

/-- `(↑)` sends `cocompact ℂ` to `𝓝 ∞` (mathlib's `tendsto_coe_infty` re-based off
`coclosedCompact` for downstream convenience). -/
theorem tendsto_coe_cocompact : Tendsto ((↑) : ℂ → OnePoint ℂ) (cocompact ℂ) (𝓝 ∞)

/-- The `𝓝 ∞` filter work, packaged: `z ↦ ↑(z⁻¹)` blows up at `0`. [spiked, full proof] -/
theorem tendsto_coe_inv_nhdsNE_zero :
    Tendsto (fun z : ℂ => ((z⁻¹ : ℂ) : OnePoint ℂ)) (𝓝[≠] (0 : ℂ)) (𝓝 (∞ : OnePoint ℂ))

theorem continuous_inversion : Continuous inversion

/-- Inversion as a self-inverse homeomorphism of the Riemann sphere. -/
def inversionHomeomorph : OnePoint ℂ ≃ₜ OnePoint ℂ
@[simp] theorem inversionHomeomorph_apply : ⇑inversionHomeomorph = inversion
@[simp] theorem inversionHomeomorph_symm : inversionHomeomorph.symm = inversionHomeomorph

end RS.P1
```

### 3.2 `Charts.lean`

Junk-value policy (load-bearing): `coeChart` is hand-rolled with `toFun p := p.elim 0 id`, NOT
built from `isOpenEmbedding_coe.toOpenPartialHomeomorph` — the latter's inverse goes through
`Function.invFunOn` and leaves `coeChart ∞` opaque; hand-rolling pins `coeChart ∞ = 0 (rfl)`,
which makes all four transition maps below literally `id`/`Inv.inv` and makes `⇑coeChart ∘ f`
the standard "value 0 at poles" planar representative downstream.

```lean
namespace RS.P1

/-- The identity chart on the finite part of `ℙ¹`: source `{∞}ᶜ`, target `univ`,
`↑z ↦ z`, junk value `coeChart ∞ = 0`. [spiked, compiles with full proof] -/
noncomputable def coeChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ
@[simp] theorem coeChart_apply_coe (z : ℂ) : coeChart (z : OnePoint ℂ) = z          -- rfl
@[simp] theorem coeChart_apply_infty : coeChart (∞ : OnePoint ℂ) = 0                -- rfl
@[simp] theorem coeChart_symm_apply (z : ℂ) : coeChart.symm z = (z : OnePoint ℂ)    -- rfl
@[simp] theorem coeChart_source : coeChart.source = {(∞ : OnePoint ℂ)}ᶜ
@[simp] theorem coeChart_target : coeChart.target = Set.univ

/-- The chart at infinity: source `{(0:ℂ)}ᶜ`, target `univ`, `↑z ↦ z⁻¹`, `∞ ↦ 0`.
Defined as `inversionHomeomorph.toOpenPartialHomeomorph.trans coeChart`. -/
noncomputable def invChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ
/-- Unconditional (`z = 0` gives junk `= 0 = 0⁻¹` on both sides). -/
@[simp] theorem invChart_apply_coe (z : ℂ) : invChart (z : OnePoint ℂ) = z⁻¹
@[simp] theorem invChart_apply_infty : invChart (∞ : OnePoint ℂ) = 0
@[simp] theorem invChart_symm_apply (w : ℂ) : invChart.symm w = inversion (w : OnePoint ℂ)
@[simp] theorem invChart_source : invChart.source = {((0 : ℂ) : OnePoint ℂ)}ᶜ
@[simp] theorem invChart_target : invChart.target = Set.univ
theorem invChart_comp_coe : ⇑invChart ∘ ((↑) : ℂ → OnePoint ℂ) = Inv.inv   -- funext, if-split

/-- The generating chart family (`false ↦ coeChart`, `true ↦ invChart`) and index map
(`∞ ↦ true`, `↑z ↦ false`). -/
noncomputable def chartFamily : Bool → OpenPartialHomeomorph (OnePoint ℂ) ℂ
def chartIndex : OnePoint ℂ → Bool
theorem mem_chartFamily_source (p : OnePoint ℂ) : p ∈ (chartFamily (chartIndex p)).source

instance instChartedSpace : ChartedSpace ℂ (OnePoint ℂ) :=
  RS.chartedSpaceOfFamily chartFamily chartIndex mem_chartFamily_source
@[simp] theorem chartAt_coe (z : ℂ) : chartAt ℂ ((z : ℂ) : OnePoint ℂ) = coeChart   -- rfl
@[simp] theorem chartAt_infty : chartAt ℂ (∞ : OnePoint ℂ) = invChart               -- rfl
theorem atlas_eq : atlas ℂ (OnePoint ℂ) = {coeChart, invChart}

instance instIsManifold : IsManifold 𝓘(ℂ) ω (OnePoint ℂ)   -- via RS.isManifold_of_family, §4.P3

open IsManifold in
theorem coeChart_mem_maximalAtlas : coeChart ∈ maximalAtlas 𝓘(ℂ) ω (OnePoint ℂ)
open IsManifold in
theorem invChart_mem_maximalAtlas : invChart ∈ maximalAtlas 𝓘(ℂ) ω (OnePoint ℂ)

/-- `Classical.arbitrary`-free basepoints: `∞`, `↑0`, `↑1` (distinctness is mathlib's
`coe_ne_infty` / `coe_eq_coe`). -/
instance : Nontrivial (OnePoint ℂ)   -- ⟨⟨((0:ℂ) : OnePoint ℂ), ∞, coe_ne_infty 0⟩⟩

-- smoke tests (all inferInstance [spiked]; keep as `example`s, they guard regressions):
-- example : CompactSpace (OnePoint ℂ) / T2Space / ConnectedSpace / ∀ x, (𝓝[≠] x).NeBot

end RS.P1
```

### 3.3 `Holomorphy.lean` — the transfer kit

Standing variables: `{Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]`
— **no compactness/connectedness anywhere** (per CONVENTIONS; `Z := ℂ` and `Z := X` both
instantiate).

```lean
namespace RS.P1

/-- The coercion `ℂ → ℙ¹` is holomorphic. -/
theorem contMDiff_coe : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ((↑) : ℂ → OnePoint ℂ)

/-- Holomorphic lift of a holomorphic function (the "no poles" constructor). -/
theorem ContMDiffAt.onePointCoe {g : Z → ℂ} {x : Z} (hg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g x) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun z => ((g z : ℂ) : OnePoint ℂ)) x
theorem ContMDiff.onePointCoe {g : Z → ℂ} (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => ((g z : ℂ) : OnePoint ℂ))

/-- Holomorphy at a finite value, read in the `coeChart`. -/
theorem contMDiffAt_iff_analyticAt_of_ne_infty {f : Z → OnePoint ℂ} {x : Z}
    (h : f x ≠ ∞) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x ↔ ContinuousAt f x ∧
      AnalyticAt ℂ (⇑coeChart ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)

/-- Holomorphy at `∞`, read in the `invChart` ("`1/f` is analytic"). -/
theorem contMDiffAt_iff_analyticAt_of_eq_infty {f : Z → OnePoint ℂ} {x : Z}
    (h : f x = ∞) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x ↔ ContinuousAt f x ∧
      AnalyticAt ℂ (⇑invChart ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)

/-- **Pole constructor** (planar; the pre-`ℳ X` layer). A function agreeing near `z₀` with a
meromorphic `g` having a genuine pole, and sent to `∞` at `z₀`, is holomorphic into `ℙ¹`. -/
theorem contMDiffAt_of_pole {g : ℂ → ℂ} {z₀ : ℂ} (hg : MeromorphicAt g z₀)
    (hord : meromorphicOrderAt g z₀ < 0) {F : ℂ → OnePoint ℂ} (hF∞ : F z₀ = ∞)
    (hF : ∀ᶠ z in 𝓝[≠] z₀, F z = ((g z : ℂ) : OnePoint ℂ)) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F z₀

/-- Converse atom: a holomorphic map to `ℙ¹` is chart-locally meromorphic (CC3's currency). -/
theorem meromorphicAt_coeChart_comp {f : Z → OnePoint ℂ} {x : Z}
    (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) :
    MeromorphicAt (⇑coeChart ∘ f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x)

/-- The inversion is holomorphic, hence a biholomorphic involution of `ℙ¹`. -/
theorem contMDiff_inversion : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω inversion
noncomputable def inversionDiffeomorph : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (OnePoint ℂ) (OnePoint ℂ) ω
@[simp] theorem inversionDiffeomorph_apply : ⇑inversionDiffeomorph = inversion

end RS.P1
```

**Deliverable-for-later** (recorded, NOT built here; lives in meromorphic-and-divisors or the
headline unit, after CC3's `ℳ X` exists — its proof is `contMDiffAt_of_pole` +
`ContMDiffAt.onePointCoe` applied in `chartAt ℂ x`):

```lean
-- intended signature, future unit:
noncomputable def ℳ.toP1 (f : ℳ X) : X → OnePoint ℂ        -- ∞ at poles, germ value elsewhere
theorem ℳ.contMDiff_toP1 (f : ℳ X) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (ℳ.toP1 f)
theorem ℳ.toP1_eq_coe_of_nonneg_order ...                    -- coeChart ∘ toP1 f =ᶠ[codiscrete] f-rep
```

### 3.4 `Sphere.lean` — the challenge bridge

```lean
namespace RS.P1
/-- `ℙ¹` is homeomorphic to the unit 2-sphere — the sphere model used verbatim by the
challenge's `genus_eq_zero_iff_homeo`. [spiked, compiles as a one-liner] -/
noncomputable def homeoSphere :
    OnePoint ℂ ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  onePointEquivSphereOfFinrankEq (by simp [Complex.finrank_real_complex])
end RS.P1
```

Note: mathlib's construction selects a `ContinuousLinearEquiv` via `Nonempty.some`, so
`homeoSphere` has no closed-form pointwise description (`homeoSphere ∞` is not a named pole).
No downstream consumer needs one: genus-zero-headline only needs
`Nonempty (X ≃ₜ sphere)` (composing its degree-1 homeo `X ≃ₜ ℙ¹` with `homeoSphere`), and
sphere-topology works on the sphere side and transfers along an abstract homeomorphism. If a
pointwise description ever becomes necessary, see fallback F4.

### 3.5 `GenusZero.lean`

```lean
namespace RS.P1

/-- There are no nonzero holomorphic 1-forms on `ℙ¹` (Forster 5-adjacent; "the sphere has
genus 0"). -/
theorem form1_eq_zero (η : RS.Form1 (OnePoint ℂ)) : η = 0

instance : Subsingleton (RS.Form1 (OnePoint ℂ))
theorem finrank_form1 : Module.finrank ℂ (RS.Form1 (OnePoint ℂ)) = 0

end RS.P1

/-- `genus ℙ¹ = 0`. -/
theorem RS.genus_onePoint : genus (OnePoint ℂ) = 0
```

(`genus` is the root-level challenge definition from Forms/Genus; `RS.genus_onePoint` is a
one-line unfold + `Module.finrank_zero_of_subsingleton`, kept in this file so exactly one
declaration depends on the Forms/Genus landing.)

---

## 4. Proof plans

**P1. `inversion` continuity** (the filter work at `∞` and at `0`). Three `ContinuousAt` cases
via `continuous_iff_continuousAt` + `OnePoint.rec`:

- At `↑z`, `z ≠ 0`: `continuousAt_coe` reduces to `ContinuousAt (inversion ∘ (↑)) z`;
  on the open `{0}ᶜ ∋ z`, `inversion ∘ (↑) = (↑) ∘ Inv.inv` (by `inversion_coe`), so
  `ContinuousAt.congr` + `continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)`.
- At `↑0`: value is `∞`. Split `𝓝 0 = 𝓝[≠] 0 ⊔ pure 0` (`nhdsNE_sup_pure`); the `pure` leg is
  the value; the punctured leg is `tendsto_coe_inv_nhdsNE_zero` (after `EventuallyEq`-congr with
  `(↑) ∘ Inv.inv` on `𝓝[≠] 0`), which is **[spiked]**:
  `tendsto_inv₀_nhdsNE_zero : Tendsto Inv.inv (𝓝[≠] 0) (cobounded ℂ)`, then
  `Metric.cobounded_eq_cocompact ▸`, then `tendsto_coe_cocompact` (=`tendsto_coe_infty`
  rewritten by `coclosedCompact_eq_cocompact`). Composition closes it.
- At `∞`: `continuousAt_infty'` reduces to
  `Tendsto (inversion ∘ (↑)) (coclosedCompact ℂ) (𝓝 (↑(0:ℂ)))`. Rewrite
  `coclosedCompact = cocompact = cobounded`; `{0}ᶜ ∈ cobounded ℂ` (complement of a bounded set),
  so congr to `(↑) ∘ Inv.inv`; `tendsto_inv₀_cobounded : Tendsto Inv.inv (cobounded ℂ) (𝓝 0)`
  composed with `continuous_coe.continuousAt`.

`inversionHomeomorph`: `Homeomorph.mk (inversion_involutive.toPerm _)`-style Equiv (or explicit
`⟨inversion, inversion, involutive, involutive⟩`), both continuity fields `continuous_inversion`.

**P2. `coeChart`** — compiled in the spike verbatim (all 10 fields; see `scratch_p1.lean`):
`left_inv'` by `ne_infty_iff_exists` + `rfl`; `open_source := isClosed_infty.isOpen_compl`;
`continuousOn_toFun` pointwise via `continuousAt_coe` (`(toFun ∘ (↑)) = id` definitionally);
`continuousOn_invFun := continuous_coe.continuousOn`. `invChart := inversionHomeomorph.
toOpenPartialHomeomorph.trans coeChart`; its source/target/apply lemmas fall to
`Homeomorph.toOpenPartialHomeomorph_source/_target/_apply` + `OpenPartialHomeomorph.trans_source`
(`= univ ∩ inversion ⁻¹' {∞}ᶜ`, then `inversion_eq_infty_iff` gives `{↑0}ᶜ`) and `coe_trans`.
`invChart_apply_coe` is unconditional by `by_cases z = 0` (`z = 0`: both sides `0` — junk aligned
by design; `z ≠ 0`: `inversion_coe` + `coeChart_apply_coe`).

**P3. `IsManifold 𝓘(ℂ) ω (OnePoint ℂ)`** via `RS.isManifold_of_family`. The four transition
functions are *definitionally pleasant*:

| `i` | `j` | `((chartFamily i).symm ≫ₕ chartFamily j)` as a function | source |
|-----|-----|---------------------------------------------------------|--------|
| `false` | `false` | `fun z => coeChart ↑z = z` — `id` (pointwise `rfl`) | `univ` |
| `false` | `true` | `fun z => invChart ↑z = z⁻¹` — `Inv.inv` (`invChart_comp_coe`) | `{0}ᶜ` |
| `true` | `false` | `fun z => coeChart (inversion ↑z)` — `= Inv.inv` (case `z = 0`: `coeChart ∞ = 0 = 0⁻¹`) | `{0}ᶜ` |
| `true` | `true` | `fun z => invChart (inversion ↑z)` — `= id` (involutivity; case `z = 0`: `invChart ∞ = 0`) | `univ` |

Sources by `trans_source` + the simp lemmas (`{0}ᶜ` cases: `coe⁻¹' {↑0}ᶜ = {0}ᶜ` via
`coe_eq_coe`; `true`-row: `{z | inversion ↑z ∈ …}` unfolds by `inversion_eq_infty_iff` /
involutivity). Analyticity: `analyticOnNhd_id`, and `analyticOnNhd_inv` (source ⊆ `{z | z ≠ 0}`)
transported through the function equalities (`AnalyticOnNhd.congr`, or pointwise
`AnalyticAt.congr` with the open source; the equalities hold on ALL of ℂ, so `Filter.EventuallyEq`
is free). Then `maximalAtlas` memberships:
`IsManifold.subset_maximalAtlas` (`IsManifold/Basic.lean:883`) on
`atlas_eq`-membership (`chartedSpaceOfFamily_atlas` + `Set.range` of a `Bool`-family is the pair
set).

**P4. `contMDiff_coe` and the two iff lemmas.** All three are instantiations of the BUILT
Surface bridge `RS.contMDiffAt_iff_analyticAt_writtenInExtChartAt` (`f : X → Y` version). Over
`𝓘(ℂ)`, `⇑(extChartAt 𝓘(ℂ) p) = ⇑(chartAt ℂ p)` (mfld_simps), so
`writtenInExtChartAt 𝓘(ℂ) 𝓘(ℂ) x f = ⇑(chartAt ℂ (f x)) ∘ f ∘ ⇑(chartAt ℂ x).symm`; rewrite
`chartAt ℂ (f x)` by `chartAt_coe` (using `ne_infty_iff_exists.mp h` to expose `f x = ↑w`) or
`chartAt_infty`. For `contMDiff_coe` at `z : ℂ`: source chart is `chartAt ℂ (z:ℂ)` on the model
(`chartAt_self_eq`, i.e. `refl`), target chart is `coeChart`; the composite is `id` near `z`
(`coeChart_apply_coe`), `ContinuousAt` is `continuous_coe.continuousAt`, `analyticAt_id` closes.
`ContMDiffAt.onePointCoe := (contMDiff_coe _).comp x hg` (`ContMDiffAt.comp`).

**P5. `contMDiffAt_of_pole`.** Let `c := z₀`. From `hord` and
`meromorphicOrderAt_eq_int_iff` (`Analysis/Meromorphic/Order.lean:94`): get `m : ℤ`, `m < 0`,
`h` analytic at `c`, `h c ≠ 0`, with `g =ᶠ[𝓝[≠] c] fun z => (z - c) ^ m • h z`. Set
`n := (-m).toNat ≥ 1` and `φ : ℂ → ℂ := fun z => (z - c) ^ n * (h z)⁻¹`:
`AnalyticAt ℂ φ c` (`analyticAt_id.sub analyticAt_const |>.pow`, `hh.inv (h c ≠ 0)`, product),
`φ c = 0` (since `n ≥ 1`). Facts on `𝓝[≠] c`: `h ≠ 0` (continuity at `h c ≠ 0`),
`(z - c) ^ m ≠ 0`, so `g ≠ 0` and `φ = g⁻¹` eventually (zpow/pow algebra:
`(z-c)^m • h z` inverted is `(z-c)^(-m) * (h z)⁻¹`).
1. `AnalyticAt ℂ (⇑invChart ∘ F) c`: `invChart (F z) = invChart ↑(g z) = (g z)⁻¹ = φ z`
   eventually on `𝓝[≠] c` (`invChart_apply_coe` — unconditional, so no `g z ≠ 0` needed even);
   at `c` itself `invChart ∞ = 0 = φ c`. So `⇑invChart ∘ F =ᶠ[𝓝 c] φ`
   (`eventually_nhds` from punctured + value, e.g. via `Filter.EventuallyEq` on
   `𝓝[≠]` + `nhdsNE_sup_pure`), and `AnalyticAt.congr` closes.
2. `ContinuousAt F c`: `F =ᶠ[𝓝 c] inversion ∘ (↑) ∘ φ`: at `c`, `inversion ↑(φ c) =
   inversion ↑(0:ℂ) = ∞ = F c`; on `𝓝[≠] c` where `g ≠ 0`: `φ = g⁻¹ ≠ 0`, so
   `inversion ↑(φ z) = ↑(φ z)⁻¹ = ↑(g z) = F z`. RHS is continuous at `c`
   (`continuous_inversion`, `continuous_coe`, `φ` analytic ⇒ continuous); congr.
3. Apply `contMDiffAt_iff_analyticAt_of_eq_infty` (with `Z := ℂ`; `chartAt ℂ c = refl` on the
   model, so the composite is `⇑invChart ∘ F` up to `chartAt_self_eq` simp).

**P6. `meromorphicAt_coeChart_comp`.** Write `c := chartAt ℂ x x`,
`G := ⇑coeChart ∘ f ∘ ⇑(chartAt ℂ x).symm`. Case `f x ≠ ∞`: the iff lemma gives
`AnalyticAt ℂ G c`; `AnalyticAt.meromorphicAt`. Case `f x = ∞`: let
`ψ := ⇑invChart ∘ f ∘ ⇑(chartAt ℂ x).symm`, analytic at `c` with `ψ c = 0`. Dichotomy
`AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` (`IsolatedZeros.lean:125`):
  - `ψ =ᶠ[𝓝 c] 0`: then `f = ∞` near `x` — careful, `ψ p' = 0` iff `f p' ∈ {∞, ↑0}`; refine:
    `ψ ≡ 0` near means `invChart (f ·) ≡ 0`. Instead argue directly on `G`: `f p' ∈ {∞, ↑0}`
    near, so `G ∈ {coeChart ∞, coeChart ↑0} = {0}` near, i.e. `G =ᶠ[𝓝 c] 0`?? — NO: `{∞, ↑0}`
    is not locally constant a priori. Correct route: `f` is continuous at `x` with `f x = ∞`, so
    `f ≠ ↑0` eventually near `x` (`{↑0}ᶜ` open ∋ ∞ — `isClosed_singleton.isOpen_compl`,
    T1 ✓); on that neighborhood `ψ p' = 0 ↔ f p' = ∞ ↔ G p' = 0` hmm `G p' = coeChart ∞ = 0`.
    So in this branch `f =ᶠ ∞`, hence `G =ᶠ[𝓝 c] 0` — analytic, meromorphic. ✓
  - `ψ ≠ 0` on `𝓝[≠] c`: combined with `f ≠ ↑0` eventually (previous bullet), on `𝓝[≠] c`
    eventually `f p' ∉ {∞, ↑0}`, where `G = ψ⁻¹` (`coeChart ↑w = w = (w⁻¹)⁻¹ = (invChart ↑w)⁻¹`
    for `w ≠ 0`). So `G =ᶠ[𝓝[≠] c] ψ⁻¹`, and `MeromorphicAt ψ⁻¹ c`
    (`hψ.meromorphicAt.inv`, `Meromorphic/Basic.lean` closure under `inv`); conclude by
    `MeromorphicAt.congr` (`Basic.lean:250`, `𝓝[≠]`-germ property). ✓
  (Chart transport: `𝓝[≠] c`-facts about `f ∘ (chartAt ℂ x).symm` come from `𝓝[≠] x`-facts via
  the chart homeomorphism; Surface's `map_extChartAt_nhdsNE` (BUILT, `Identity.lean`) is the
  ready-made mover.)

**P7. `contMDiff_inversion` / `inversionDiffeomorph`.** Pointwise by `OnePoint.rec` + the iff
lemmas (`ContinuousAt` is `continuous_inversion.continuousAt` everywhere):
- at `↑z`, `z ≠ 0`: `inversion ↑z = ↑(z⁻¹) ≠ ∞`; composite
  `⇑coeChart ∘ inversion ∘ ⇑coeChart.symm = fun w => coeChart (inversion ↑w)` `= Inv.inv`
  (P3 row 3) — `analyticAt_inv hz`.
- at `↑0`: `inversion ↑0 = ∞`; composite `⇑invChart ∘ inversion ∘ ⇑coeChart.symm =
  fun w => invChart (inversion ↑w) = id` (P3 row 4) — `analyticAt_id`.
- at `∞`: `inversion ∞ = ↑0 ≠ ∞`; composite `⇑coeChart ∘ inversion ∘ ⇑invChart.symm =
  fun w => coeChart (inversion (inversion ↑w)) = fun w => coeChart ↑w = id` — `analyticAt_id`.
`inversionDiffeomorph := ⟨inversion_involutive.toPerm-Equiv, contMDiff_inversion,
contMDiff_inversion⟩` (fields `contMDiff_toFun/contMDiff_invFun`; the `Equiv` is the same as
`inversionHomeomorph.toEquiv`).

**P8. Genus 0** (the coefficient-decay Liouville argument, in Forms' actual API). Let
`η : Form1 (OnePoint ℂ)`, `f := coeffIn coeChart η`, `g := coeffIn invChart η`.
1. **Both coefficients are entire**: `Form1.analyticOnNhd_coeffIn η coeChart_mem_maximalAtlas`
   on `coeChart.target = univ` (same for `g`); hence `Differentiable ℂ f`, `Differentiable ℂ g`
   (`AnalyticAt.differentiableAt` pointwise) and both continuous.
2. **Decay identity**: for `z ≠ 0`, apply the BUILT `coeffIn_trans` (orientation
   `coeffIn e' η z = deriv (⇑e ∘ ⇑e'.symm) z * coeffIn e η (e (e'.symm z))`) with
   `e := invChart`, `e' := coeChart`, at
   `z ∈ ⇑coeChart '' (invChart.source ∩ coeChart.source) = {0}ᶜ` (witness `↑z`; membership by
   `coe_eq_coe`/`coe_ne_infty`):
   `f z = deriv (⇑invChart ∘ ⇑coeChart.symm) z * g (invChart ↑z)`. Now
   `⇑invChart ∘ ⇑coeChart.symm = Inv.inv` (`invChart_comp_coe` — exact equality of functions, no
   congr needed), `deriv_inv`, `invChart_apply_coe`:
   **`f z = -(z ^ 2)⁻¹ * g z⁻¹` for all `z ≠ 0`.**
3. **`f → 0` at `cocompact`**: `M := ` bound of `‖g‖` on `Metric.closedBall 0 1`
   (`IsCompact.exists_bound_of_continuousOn`). For `‖z‖ ≥ 1`: `‖z⁻¹‖ ≤ 1` so
   `‖f z‖ ≤ M * (‖z‖ ^ 2)⁻¹`. This eventual bound holds along `cobounded ℂ`
   (`{z | 1 ≤ ‖z‖}` is cobounded-eventual); `(‖z‖ ^ 2)⁻¹ → 0` along `cobounded`
   (`tendsto_norm_cobounded_atTop`, `Tendsto.pow`/`atTop` composition, `tendsto_inv_atTop_zero`);
   `squeeze_zero_norm'` gives `Tendsto f (cobounded ℂ) (𝓝 0)`; rewrite
   `Metric.cobounded_eq_cocompact`.
4. **Liouville**: `Differentiable.eq_const_of_tendsto_cocompact` (`Nontrivial ℂ` ✓) ⇒
   `f = Function.const ℂ 0`, i.e. `f ≡ 0`. (The decay forcing the constant to be `0` is built
   into this lemma — no separate step.)
5. **`g ≡ 0`**: for `w ≠ 0`, `coeffIn_trans` with roles swapped (`e := coeChart`,
   `e' := invChart`, `w ∈ ⇑invChart '' (coeChart.source ∩ invChart.source) = {0}ᶜ`):
   `g w = deriv (…) w * f (…) = … * 0 = 0`. At `w = 0`: `g` continuous at `0` and
   `g =ᶠ[𝓝[≠] 0] 0` ⇒ `g 0 = 0` (`tendsto_nhds_unique` with `(𝓝[≠] 0).NeBot`).
6. **`η = 0`**: `Form1.ext_coeffAt` (BUILT): for `x = ↑z`, `coeffAt x η =
   coeffIn coeChart η (coeChart ↑z) = f z = 0` (`chartAt_coe`); for `x = ∞`,
   `= coeffIn invChart η (invChart ∞) = g 0 = 0` (`chartAt_infty`); and `coeffAt x 0 = 0`
   (`coeffIn_zero`). Then `Subsingleton` (all elements equal `0`),
   `finrank_form1` by `Module.finrank_zero_of_subsingleton`, and
   `RS.genus_onePoint : genus (OnePoint ℂ) = 0` by unfolding `genus`.

**P9. `homeoSphere`** — done, one line **[spiked]** (§3.4). The hypothesis
`finrank ℝ ℂ + 1 = Fintype.card (Fin 3)` closes by `simp [Complex.finrank_real_complex]`.

---

## 5. Downstream map (what each consumer may rely on)

- **genus-zero-headline**: `RS.P1.homeoSphere` (compose with the degree-1 homeo `X ≃ₜ ℙ¹` for
  the forward direction; exact challenge sphere type), `RS.genus_onePoint`, the
  `ChartedSpace`/`IsManifold`/topology instances (so `ℙ¹` satisfies the standing surface
  variables), `ne_infty` point API.
- **sphere-topology** (builds on us): `homeoSphere` (transfer simple-connectivity between the
  sphere and any `X ≃ₜ S²`; they own `SimplyConnectedSpace (sphere …)`).
- **mapping-degree / proper-map-degree / meromorphic-trace / form-trace-tower**: `ℙ¹` as a
  target surface with computable charts: `chartAt_coe`, `chartAt_infty`, `coeChart_*`,
  `invChart_*` simp sets, `*_mem_maximalAtlas`, `contMDiffAt_iff_analyticAt_of_ne_infty/_eq_infty`,
  `meromorphicAt_coeChart_comp`, `inversionDiffeomorph` (to move `∞` to `0` in fibre
  arguments), basepoints `∞`, `↑0`, `↑1` (no `Classical.arbitrary`).
- **meromorphic-and-divisors (CC3)**: `contMDiffAt_of_pole` + `ContMDiffAt.onePointCoe` are the
  two atoms for the future `ℳ.toP1` bridge (§3.3 deliverable-for-later); junk-value contract
  `coeChart ∞ = 0` matches CC3's planar representatives.
- **jacobian-construction**: nothing (uses the same `ChartedSpaceKit`, not this unit).
- **cech / dbar**: `ℙ¹`'s two-chart good cover (`coeChart`, `invChart`) is the canonical Leray
  cover example; no additional exports needed now.

Freeze policy: names and statement shapes in §3 are the interface. `invChart`'s *values*
(`↑z ↦ z⁻¹` unconditional, `∞ ↦ 0`, junk `coeChart ∞ = 0`) are load-bearing for downstream
simp proofs — do not re-plumb junk values without orchestrator sign-off.

---

## 6. Risks & fallbacks

- **R1 (scheduling): Forms unit in flight.** `GenusZero.lean` consumes
  `Form1.analyticOnNhd_coeffIn` and `genus` (frozen in the Forms design; `coeffIn_trans`,
  `ext_coeffAt`, `coeffIn_zero` are already BUILT and were re-read — orientation of
  `coeffIn_trans` matches P8 exactly). Files 1–4 build now; file 5 last. If Forms lands
  `analyticAt_coeffAt` but not the `analyticOnNhd_coeffIn` variant, derive entirety of `f`
  pointwise from `coeffIn_trans` + `analyticAt_coeffAt` at the preferred chart of `↑z` — ~10
  extra lines, no interface change (add to `docs/requests/holomorphic-forms.md` if hit).
- **R2: `invChart`-via-`trans` simp friction** (source/target algebra of
  `Homeomorph.toOpenPartialHomeomorph.trans`). Fallback: hand-roll `invChart`'s ten fields like
  `coeChart` (`toFun p := coeChart (inversion p)`, `invFun w := inversion ↑w`) — continuity
  fields from `continuous_inversion`; ~30 lines, same simp lemmas.
- **R3: `∞` notation clash** (`ContDiff` vs `OnePoint` scopes, §1). Mitigation: type-ascribe
  `(∞ : OnePoint ℂ)` in every statement (done in §3); if a file still fights, `open OnePoint in`
  locally instead of at file top.
- **R4: `chartedSpaceOfFamily` instance shape.** `instChartedSpace` is a `@[reducible] def`
  applied to `chartFamily`; `chartAt_coe`/`chartAt_infty` should be `rfl` via
  `chartedSpaceOfFamily_chartAt`. If `Bool.rec`/`bif` blocks `rfl`, switch `chartFamily` to a
  `match`-def or add `@[simp]` unfolding lemmas for `chartFamily false/true` — cosmetic.
- **R5: P6's punctured-filter chart transport.** Needs `𝓝[≠] x`-to-`𝓝[≠] c` movement;
  Surface's `map_extChartAt_nhdsNE` (BUILT) is designed for this. If its exact shape mismatches,
  hand-roll via `OpenPartialHomeomorph.map_nhds_eq` + injectivity (the Surface design's own
  sanctioned fallback, ~8 lines).
- **R6: zpow bookkeeping in P5** (`(z-c)^m • h` with `m < 0` inverted to `(z-c)^(-m).toNat * h⁻¹`).
  Mechanical `zpow_neg`/`zpow_natCast` algebra on the punctured filter; if `smul` vs `mul`
  friction appears (`E := ℂ`), rewrite `smul_eq_mul` first. Contained in one proof.
- **F4 (explicit sphere map, NOT planned).** If some later consumer needs
  `homeoSphere ∞ = northPole`-style values: rebuild via
  `OnePoint.equivOfIsEmbeddingOfRangeEq` applied to
  `(stereographic' 2 v).symm ∘ (chosen explicit ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2))` with
  `v := EuclideanSpace.single 2 1`, using mathlib's `isOpenEmbedding_stereographic_symm` /
  `range_stereographic_symm` (`Instances/Sphere.lean`) exactly as
  `onePointHyperplaneHomeoUnitSphere` does, plus an explicit isometry
  `ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)` (e.g. via `Complex.basisOneI` orthonormalization or
  `LinearIsometryEquiv` from `Complex.isometryOfOrthonormal`-adjacent API). Costs ~150 lines;
  no current consumer justifies it.

---

## 7. Spike record (`scratch_p1.lean`, project root, gitignored)

Gate respected (0 concurrent `lean` processes at run time). `lake env lean scratch_p1.lean`:
**compiles clean, 6.5 s wall** (imports: `Topology.Compactification.OnePoint.Sphere`,
`Analysis.Normed.Field.Lemmas`, `Analysis.Analytic.Constructions`,
`Analysis.Calculus.Deriv.Inv`). Verified by full proof:

1. `onePointEquivSphereOfFinrankEq (by simp [Complex.finrank_real_complex]) :
   OnePoint ℂ ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1` — the challenge bridge is a
   ONE-LINER at the pin.
2. `CompactSpace`/`T2Space`/`ConnectedSpace (OnePoint ℂ)` and `∀ x, (𝓝[≠] x).NeBot` — all
   `inferInstance`.
3. `coeChart` (all fields, hand-rolled) with `coeChart ↑z = z` and `coeChart ∞ = 0` both `rfl`.
4. The `∞`-filter composite `Tendsto (fun z : ℂ => (↑(z⁻¹) : OnePoint ℂ)) (𝓝[≠] 0) (𝓝 ∞)` via
   `tendsto_inv₀_nhdsNE_zero` + `Metric.cobounded_eq_cocompact` +
   `coclosedCompact_eq_cocompact` + `tendsto_coe_infty`.
5. `analyticAt_inv`, `deriv_inv` name/shape checks.
