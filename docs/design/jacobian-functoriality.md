# Design: jacobian-functoriality (`Jacobian/JacobianFunctoriality/`)

Task **#33**, a blueprint-gap unit (not in `clean_room_blueprint.md`'s 30-unit list; flagged by
`jacobian-construction`'s `Functorial.lean` §9.4/R4 and `form-trace-tower`'s own docstring, both
naming this unit explicitly as the intended consumer of their unfinished business). Deliverable:
`Jacobian.pushforward`, `Jacobian.pullback`, `_root_.ContMDiff.degree`'s companion
`pushforward_pullback`, and the four functoriality laws, exactly as demanded by
`docs/Jacobian_challenge.lean:104-153`.

**Verdict up front.** The construction is fully worked out below and sits *entirely* on already-
built units — `holomorphic-forms` (`Jacobian/Forms/`), `paths-and-integrals` (`Jacobian/Path/`),
`meromorphic-trace` (`Jacobian/MeromorphicTrace/`), `form-trace-tower` (`Jacobian/FormTrace/`),
`mapping-degree`/`proper-map-degree` (`Jacobian/MappingDegree/`, `Jacobian/ProperDegree/`), and
`jacobian-construction` (`Jacobian/JacobianConstruction/`). **No gate on `canonical-forms`,
`laurent-tails`, or `serre-duality-tails`** — confirmed by exhaustively tracing every ingredient
used below to one of the six units just named (§12). The two genuinely new, hard pieces are (a)
**pullback of a holomorphic 1-form along *any* holomorphic `f : X → Y`** (easy mathematics, does
not exist in Lean yet — chain rule via `mfderiv`, no branch-point subtlety) and (b) **trace
(fibrewise "norm") of a holomorphic 1-form along a *nonconstant* holomorphic `f`** (the
classically hard direction: the naive unweighted fibre-sum trace object already built
(`RS.MTrace.trace`) is *proven discontinuous* at branch points — see `form-trace-tower`'s own
diagnosed defect, §0 below — so a genuinely different, per-branch-averaged (`traceZk`/
`traceZkForm`) construction plus a removable-singularity argument is needed to land in `Form1 Y`
at all). Both then transpose (via `LinearMap.dualMap` + a `Module.Basis.dualBasis` coordinate
identification, **spiked, compiles clean** — §16) into the `T`/`hT` shape
`Jacobian.inducedHom` (`jacobian-construction`'s `Functorial.lean`) already consumes.

Reference: Forster §16-17 (residues/trace precursors already used by `form-trace-tower`), Miranda
§II.3 (trace of a 1-form, Lemma 3.2 and its projection-formula corollary) for the mathematics;
`docs/refs/forster-map.md`/`docs/refs/miranda-map.md` for page numbers. No Griffiths–Harris route
(no Hodge theory, per the blueprint routing warning).

---

## 0. Why the earlier attempt failed, and why this design avoids the same trap

`form-trace-tower`'s own module docstring (`Jacobian/FormTrace.lean:25-38`) and `docs/build-log.md`
(`[ftt]` entry) record, in detail, that its centerpiece `trace_eq_zero_of_holomorphic` is **false**,
not merely hard: `RS.MTrace.trace F h` (`Jacobian/MeromorphicTrace/FunctionTrace.lean:59-63`) is
defined as

```lean
noncomputable def trace (F : X → Y) (h : X → ℂ) (y₀ : Y) : ℂ :=
  if hS : Nonempty (RS.FiberStack F y₀) then
    have S := hS.some
    ∑ i, traceZk (h ∘ (S.A i).e.symm) (RS.multiplicity F (S.pt i)) ((S.A i).e' y₀)
  else 0
```

and reduces unconditionally (`trace_eq_finsum'`) to the **naive, unweighted set-theoretic fibre
sum** `∑ᶠ x ∈ F⁻¹{y}, h x`. Take `h ≡ 1` (a genuinely holomorphic, non-degenerate hypothesis on
compact `X` — constant by the maximum-modulus principle, but that's exactly the point: `h`
*is* holomorphic) and any nonconstant `F : X → ℙ¹`: `trace F h = degree F` at every **regular**
value but only the strictly smaller **fibre cardinality** at a **branch** value — not even
continuous there. The concrete counterexample recorded for the twin claim
`trace_pullback_eq_degree_smul` is `F := (·)^2`, `h := 1`: `trace F h 0 = 1` (one preimage, `0`
itself) but `degree F = 2`. What survived: `trace_const_mul_pullback` (unconditional) and
`trace_pullback_eq_degree_smul_of_regular` (regular values only) — both in
`Jacobian/FormTrace/ResidueTraceCompat.lean:269-292`, and both **function**-level (a bare
`h : X → ℂ`), not **form**-level.

**Root cause, precisely.** `MTrace.trace` sums pointwise fibre CARDINALITY — at a branch point of
local degree `k`, the `k` nearby distinct preimages collapse into `1` literal preimage point, and
the naive sum "loses" a factor of `k` exactly there. The fix classically used (Miranda §II.3,
Forster's trace of a differential) is **not** "sum function values over the fibre" but "sum the
1-FORM'S coefficient over the fibre, expressed via the LOCAL BRANCH's own coordinate, using the
correct Jacobian-weighted (`z^k`-root-sum) local formula" — this is exactly what
`RS.MTrace.traceZk`/`Jacobian/FormTrace/TraceZkForm.lean`'s `traceZkForm` already compute
(`traceZkForm h k w := traceZk (fun v => h v * ((k:ℂ)*v^(k-1))⁻¹) k w`, i.e. divide by the
branch's Jacobian factor `k·v^{k-1}` *before* root-summing) — and, crucially, **this
per-branch object is analytic (removable singularity) across the branch value once the input is
analytic and locally bounded**, unlike the naive fibre-sum, which is a different function
entirely and is *provably* not removable (see the `h≡1` counterexample above — no repair of
`MTrace.trace` at branch points can make it continuous, because it disagrees with the correct
limit by a computable nonzero amount, not by an indeterminate/removable gap).

So: **`Form1.trace` in this design is built from `traceZkForm`'s per-branch, Jacobian-divided
local formula, glued via `Form1.ofCoeffs`, with a genuine removable-singularity theorem
established for the *glued object* — never through `MTrace.trace` itself.** This is why the
earlier unit's defect does not block this one: it was a defect of a specific (unweighted)
object, not of the underlying mathematics, and the correctly-weighted object
(`traceZkForm`-based) was *already built*, just never assembled into a `Form1`.

---

## 1. File plan

```
Jacobian/JacobianFunctoriality/Pullback.lean         -- Form1.pullback (f^*), analyticity/compat,
                                                      --   coeffIn_pullback (chart-independence),
                                                      --   algebra (add/smul), pullback_id/pullback_comp
                                                      --   (as Form1-level LinearMap identities)
Jacobian/JacobianFunctoriality/PullbackIntegral.lean  -- IsPrimitiveAlongMap.comp_map (general reusable
                                                      --   lemma), pathIntegral_pullback (naturality)
Jacobian/JacobianFunctoriality/Density.lean           -- Form1.continuous_coeffAt (new, small),
                                                      --   Form1.eq_of_eqOn_regularValues ("Lemma A":
                                                      --   two Form1's agreeing on a dense/cofinite
                                                      --   set of chart-coefficients are equal) —
                                                      --   the single reusable closing move for
                                                      --   Trace.lean's compat, the projection
                                                      --   formula, and both comp-functoriality laws
Jacobian/JacobianFunctoriality/Trace.lean             -- Form1.trace (Tr_f), regular-value case
                                                      --   (elementary) + branch-value case
                                                      --   (traceZkForm + removable singularity),
                                                      --   compat via Density.lean's Lemma A,
                                                      --   algebra, trace_id, junk-zero for constant f
Jacobian/JacobianFunctoriality/TraceIntegral.lean     -- FiberChain (chart-chain of FiberStacks along
                                                      --   a branch-avoiding loop), lifted sheets +
                                                      --   monodromy-cycle bookkeeping,
                                                      --   pathIntegral_trace (the hard relation)
Jacobian/JacobianFunctoriality/PeriodMaps.lean        -- dualMap + Basis.dualBasis.equivFun
                                                      --   coordinatization (T_pushforward/T_pullback),
                                                      --   hT proofs (lattice-mapping) via
                                                      --   pathIntegral_pullback/pathIntegral_trace +
                                                      --   periodVector_mem_periodSubgroup + the
                                                      --   monodromy-cycle argument; assembles
                                                      --   Jacobian.pushforward/pullback via
                                                      --   Jacobian.inducedHom
Jacobian/JacobianFunctoriality/Challenge.lean         -- pushforward_contMDiff/pullback_contMDiff
                                                      --   (free, from jaccon's contMDiff_inducedHom),
                                                      --   pushforward_id_apply/comp_apply,
                                                      --   pullback_id_apply/comp_apply,
                                                      --   pushforward_pullback (projection formula
                                                      --   lifted through dualMap + inducedHom)
Jacobian/JacobianFunctoriality.lean                   -- unit root, API docstring
```

Six substantive files (`Pullback` easy-direction pair, `Density` small shared utility, `Trace`
hard-direction pair, `PeriodMaps`+`Challenge` assembly) + root, matching the "4-6 files" budget.
Dependency order: `Pullback` → `PullbackIntegral`; `Density` independent (only needs `Forms`+
`MappingDegree.Ramification`); `Trace` needs `Density`; `TraceIntegral` needs `Trace` +
`PullbackIntegral` (reuses the same `IsPrimitiveAlongMap` machinery for the per-sheet pieces) +
`Path.Perturb`/`Path.Chain`; `PeriodMaps` needs everything above plus `JacobianConstruction`;
`Challenge` needs `PeriodMaps` plus `ProperDegree.ChallengeDegree` and `MappingDegree.Degree`.

---

## 2. Mathematical strategy (one paragraph)

`Jacobian X`'s ambient period space `V_X := Fin (genus X) → ℂ` is *already*, via the fixed basis
`RS.basis X : Basis (Fin (genus X)) ℂ (Form1 X)`, a coordinatization of `Module.Dual ℂ (Form1 X)`
(a period vector `periodVector (basis X) γ = fun i => pathIntegral γ (basis X i)` is literally
"the functional `pathIntegral γ` read in `(basis X)`'s dual-basis coordinates" —
`(basis X).dualBasis.repr (pathIntegralₗ γ) = periodVector (basis X) γ`, confirmed by mathlib's
`Basis.dualBasis_repr : b.dualBasis.repr l i = l (b i)`). `Jacobian.inducedHom`
(`JacobianConstruction/Functorial.lean:60-69`) already builds `Jacobian X →ₜ+ Jacobian Y` from any
`T : V_X →ₗ[ℂ] V_Y` respecting the period subgroups (`hT`). So the whole task reduces to:
build `T_pushforward := dualMap(Form1.pullback f hf) `, `T_pullback := dualMap(Form1.trace f hf hne)`
(both correctly variance-matched — `dualMap` of `Form1 Y →ₗ Form1 X` is `Dual(Form1 X) →ₗ
Dual(Form1 Y)`, exactly the pushforward direction, and dually for pullback), transport them
through the `(basis X).dualBasis.equivFun`/`(basis Y).dualBasis.equivFun` coordinate identification
(spiked, §16) to get genuine elements of `V_X →ₗ[ℂ] V_Y` / `V_Y →ₗ[ℂ] V_X`, prove `hT` for each
(§9), and feed to `Jacobian.inducedHom`. `ContMDiff` of the result is then **free**
(`contMDiff_inducedHom`, already proved by `jacobian-construction`, gated only on
`[DiscreteTopology (periodSubgroup _).topologicalClosure]` — someone else's problem, already
wired for `ofCurve_contMDiff` too). Functoriality laws and the projection formula reduce, via
`dualMap`'s own contravariant functoriality (`(f.comp g).dualMap = g.dualMap.comp f.dualMap`,
`LinearMap.dualMap_id`) and `Jacobian.inducedHom`'s representative-level unfolding
(`QuotientAddGroup.map_mk`, `rfl`), to two `Form1`-level identities: `Form1.pullback id
contMDiff_id = LinearMap.id`, `Form1.pullback (g∘f) = (Form1.pullback f).comp (Form1.pullback g)`
(and the dual pair for `trace`), plus the projection formula `Form1.trace f hf hne
(Form1.pullback f hf η) = (ContMDiff.degree f hf : ℂ) • η`.

---

## 3. `Form1.pullback` — the easy direction (`Pullback.lean`)

### 3.1 Target signature

```lean
namespace RS

noncomputable def Form1.pullback (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Form1 Y →ₗ[ℂ] Form1 X where
  toFun η := Form1.ofCoeffs (pullbackCoeffData f hf η)
  map_add' η η' := by ...   -- Form1.ext_coeffAt + coeffAt_ofCoeffs + Form1.coeffAt_add
  map_smul' c η := by ...
```

where the private helper builds the chart data (chart family = `X`'s own preferred charts,
`ι := X`):

```lean
private def pullbackCoeffData (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (η : Form1 X → ... )
    -- (schematically) : Form1CoeffData X X where
  chart x := chartAt ℂ x
  mem_maximalAtlas x := chart_mem_maximalAtlas 𝓘(ℂ) ω x
  exists_mem x := ⟨x, mem_chart_source ℂ x⟩
  coeff x z := deriv (chartAt ℂ (f x) ∘ f ∘ (chartAt ℂ x).symm) z *
                 coeffIn (chartAt ℂ (f x)) η ((chartAt ℂ (f x) ∘ f ∘ (chartAt ℂ x).symm) z)
  analyticOnNhd x := ...   -- composition of AnalyticOnNhd pieces (§3.2)
  compat x x' z hz := ...  -- chain-rule cocycle check (§3.2)
```

### 3.2 Proof plan (moderate — this is `mdifferential`'s exact template, one differential-form
degree up)

`Jacobian/Forms/MDifferential.lean`'s `mdifferential f hf : Form1 X` is *literally* the special
case `η := "dz"` on `ℂ` (the fixed target coordinate 1-form), built the same way: chart-local
coefficient `deriv (f ∘ e.symm)`, glued via the analogous `ofSectionAnalytic`/`ofCoeffs` route.
`Form1.pullback f hf η`'s coefficient is the same chain-rule formula with `deriv(f∘e.symm)`
replaced by `deriv(φ) · (coeffIn e' η) ∘ φ` where `φ := chartAt ℂ (f x) ∘ f ∘ (chartAt ℂ x).symm`
(the "`f` read in charts" map, `AnalyticOnNhd` since `hf : ContMDiff … ω` — bridged via
`contMDiffOn_iff_analyticOnNhd_of_subset_source`, already used by every unit that needs to read a
`ContMDiff ω` hypothesis as analyticity in charts). Analyticity of `coeff x` near
`(chartAt ℂ x) x`: composition of (a) `φ` analytic (chart-transport of `hf`), (b) `coeffIn
(chartAt ℂ (f x)) η` analytic on the whole target of `chartAt ℂ (f x)` (`Form1.analyticOnNhd_coeffIn`,
no restriction needed — this is the payoff of `coeffIn`'s *global*-on-target analyticity, no
branch-point case split anywhere in this file), (c) `deriv φ` analytic (derivative of an analytic
function is analytic, standard). ~20 lines per point, all `AnalyticAt.mul`/`.comp` composition,
zero new proof techniques.

`compat` (the CC1 transition check between two `X`-charts `chartAt ℂ x`, `chartAt ℂ x'`): a pure
chain-rule identity — `deriv(chart x ∘ (chart x').symm)(z) * coeff(chart x')(z) = coeff(chart
x)(chart x ∘ (chart x').symm z)`. Expand both `coeff`s via their defining formula; the two
`φ`-factors compose via `deriv (φ_x ∘ (chart x' ∘ (chart x).symm))` = `deriv φ_{x'} · deriv(chart
x-transition)` (standard chain rule, `HasDerivAt.comp`/`deriv_comp` at the analytic points
involved — all points here are literal chart-overlap points, no branch locus at all since this
whole file never invokes `MappingDegree`), and the `coeffIn e' η`-factor is **chart-independent**
by construction (same target chart `chartAt ℂ (f x)` used in both — actually needs one more step
if `f x ≠ f x'`, i.e. relating `chartAt ℂ (f x)` and `chartAt ℂ (f x')` when both source charts
overlap and map to different target charts; resolved via `Form1`'s own transition law, i.e.
`η`'s own well-formedness as a `Form1 Y` supplies exactly this, so the "target chart" ambiguity is
absorbed for free by `η`'s own compat, already proved when `η` was constructed — this is the same
"any chart works, coeffIn is chart-independent up to the transition-derivative factor" fact stated
generally as `Form1.coeffIn_eq_of_mem_source`-style lemma, likely already present in
`Jacobian/Forms/Coeffs.lean` or provable in three lines from `analyticOnNhd_coeffIn` +
`Form1.apply_eq_smul_coeffAt`). ~25 lines total. **No removable singularity, no branch locus,
no `hne` hypothesis anywhere in this file** — `f` constant is not excluded (and gives `φ` locally
constant, `deriv φ = 0`, `coeff x ≡ 0`, i.e. `Form1.pullback f hf η = 0` automatically for
constant `f` — matches the task mandate's observation that this is exactly what makes
`Jacobian.pushforward` land on the zero map for constant `f`, with **no case split** needed).

### 3.3 `coeffIn_pullback` — the reusable "any chart" lemma

```lean
theorem coeffIn_pullback {e : OpenPartialHomeomorph X ℂ} (he : e ∈ maximalAtlas 𝓘(ℂ) ω X)
    {e' : OpenPartialHomeomorph Y ℂ} (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω Y)
    (η : Form1 Y) {x : X} (hx : x ∈ e.source) (hx' : f x ∈ e'.source) {z : ℂ} (hz : e x = z) :
    coeffIn e (Form1.pullback f hf η) z =
      deriv (⇑e' ∘ f ∘ ⇑e.symm) z * coeffIn e' η ((⇑e' ∘ f ∘ ⇑e.symm) z)
```
proved once (via `Form1.coeffIn_ofCoeffs` at the defining chart + a rechart step, mirroring
`coeffIn_mdifferential`'s own generalization from the defining chart family to an arbitrary
maximal-atlas chart) and used everywhere downstream (naturality §4, projection formula §10) instead
of re-deriving the chain rule each time.

### 3.4 `pullback_id`/`pullback_comp` (Form1-level, feeds §9's functoriality laws)

```lean
theorem Form1.pullback_id : Form1.pullback (id : X → X) contMDiff_id = LinearMap.id
theorem Form1.pullback_comp {Z} [...] (f : X → Y) (hf) (g : Y → Z) (hg) :
    Form1.pullback (g ∘ f) (hg.comp hf) = (Form1.pullback f hf).comp (Form1.pullback g hg)
```
Both are `Form1.ext_coeffAt` + `coeffIn_pullback` chain-rule bookkeeping (`deriv_id'`,
`deriv.comp` for the composite chart-read map) — ~15-20 lines each, no new ideas.

---

## 4. Path-integral naturality (`PullbackIntegral.lean`)

### 4.1 Target statement

```lean
theorem pathIntegral_pullback {x y : X} (γ : Path x y) (η : Form1 Y) :
    pathIntegral γ (Form1.pullback f hf η) = pathIntegral (γ.map hf.continuous) η
```
(`γ.map hf.continuous : Path (f x) (f y)` — mathlib's `Path.map`,
`.lake/packages/mathlib/Mathlib/Topology/Path.lean:338-376`, with `map_symm`/`map_trans`/`map_id`/
`map_map` free — `f` implicit, determined by the continuity proof's type; already used elsewhere
in the project, `Jacobian/Path/Perturb.lean:61`.)

### 4.2 Proof plan, via one general reusable lemma

```lean
theorem IsPrimitiveAlongMap.pullback_comp {K : α → X} {η : Form1 Y} {F : α → ℂ} {s : Set α}
    (h : IsPrimitiveAlongMap (f ∘ K) η F s) :
    IsPrimitiveAlongMap K (Form1.pullback f hf η) F s
```
*Proof.* Unfold `IsPrimitiveAlongMap` at `a ∈ s`: `h` gives a `Y`-chart `e' ∈ maximalAtlas … Y` at
`f (K a)` and a local primitive `g` of `coeffIn e' η` there, with `F` eventually `g ∘ e' ∘ f ∘ K`
near `a` (within `s`). Pick the `X`-chart `e := chartAt ℂ (K a)` (any maximal-atlas chart at `K a`
works, e.g. the preferred one). Set `G := g ∘ (⇑e' ∘ f ∘ ⇑e.symm)`, a composition of the two
analytic functions `g` (primitive, hence `AnalyticAt`/`DifferentiableAt`) and `e' ∘ f ∘ e.symm`
(analytic, chart-read of `hf`). By `coeffIn_pullback` (§3.3), `HasDerivAt G (coeffIn e
(Form1.pullback f hf η) (e (K a))) (e (K a))` follows from the chain rule
`(HasDerivAt g _ _).comp _ (HasDerivAt (⇑e'∘f∘⇑e.symm) _ _)`, matching `coeffIn_pullback`'s RHS
literally. And `F` eventually equals `g ∘ e' ∘ f ∘ K = G ∘ e ∘ K` (rewrite `e' ∘ f = (e' ∘ f ∘
e.symm) ∘ e` pointwise on `e.source`, using `e.symm (e ·) = id` on source) — exactly the shape
`IsPrimitiveAlongMap K (pullback f hf η) F s` needs, with `(e, G)` as the witnessing chart+
primitive. ~35 lines (mostly `Filter.Eventually`/`eventuallyEq` bookkeeping to convert "`F`
eventually equals `g∘e'∘f∘K`" into "`F` eventually equals `G∘e∘K`", the exact same congr-lemma
shape `.rechart`'s own proof already uses).

Apply to `K := γ.extend`, `s := Set.univ`: from `exists_isPrimitiveAlong (γ.map hf.continuous) η`
(giving some primitive `F` of `η` along `f ∘ γ.extend` — noting `(γ.map hf.continuous).extend =
f ∘ γ.extend` pointwise, a one-line `Path.extend`/`IccExtend` unfolding since `Path.map`'s
underlying function is definitionally `f ∘ γ` composed with the same `IccExtend`, `Path.map_coe`
confirms `⇑(γ.map hf.continuous) = f ∘ γ`), get `IsPrimitiveAlong γ (Form1.pullback f hf η) F` via
`.pullback_comp`. Two applications of `IsPrimitiveAlong.pathIntegral_eq` with the *same* `F`:
```
pathIntegral γ (pullback f hf η) = F 1 - F 0 = pathIntegral (γ.map hf.continuous) η
```
~10 more lines. **Total ~50-60 lines, low risk** (chain-rule/`eventuallyEq` bookkeeping identical
in shape to code already compiling in `LocalPrimitive.lean`/`MDifferential.lean`).

### 4.3 Corollary: period-vector naturality

```lean
theorem periodVector_pullback {x : X} (γ : Path x x) :
    periodVector (basis Y) (γ.map hf.continuous) =
      fun j => (basis X).dualBasis.equivFun ... -- pointwise via pathIntegral_pullback at (basis Y j)
```
Not literally needed as a named lemma (§9 uses `pathIntegral_pullback` directly at each `basis Y
j`), but recorded here since it is the qualitative content used for `hT`'s **pushforward** case:
`f`-image loops' periods are *exactly* (not just up to closure) periods of `X`-loops pushed
through `f`.

---

## 5. `Density.lean` — the one reusable closing lemma

Two small, self-contained facts, used by §6 (`Trace`'s `compat`), §10 (projection formula), and
§9's comp-functoriality laws (Challenge.lean):

```lean
/-- `coeffAt` is continuous as a function of the base point (new, ~15 lines: `Form1`, as a
`ContMDiffSection`, is continuous as a section; `coeffAt x η = η x 1` after the canonical
`tangentCoord`/section-evaluation identification, and evaluation-at-a-continuously-varying-point
of a continuous section composed with the continuously-varying canonical tangent vector
`mfderiv (chartAt ℂ x) x 1`-ish is continuous — mirrors `Form1.continuousOn_coeffIn`'s existing
proof one level up, from "on a fixed chart target" to "as the base point moves"). -/
theorem Form1.continuous_coeffAt (η : Form1 X) : Continuous (fun x => coeffAt x η)

/-- **Lemma A.** Two holomorphic 1-forms whose `coeffAt`s agree on a dense set (in particular,
on the cofinite complement of a *finite* set, e.g. a branch/critical locus) are equal. -/
theorem Form1.eq_of_eqOn_dense {η η' : Form1 Y} {s : Set Y} (hs : Dense s)
    (h : Set.EqOn (fun y => coeffAt y η) (fun y => coeffAt y η') s) : η = η' := by
  have := Continuous.ext_on hs (Form1.continuous_coeffAt η) (Form1.continuous_coeffAt η') h
  exact Form1.ext_coeffAt (congrFun this)
```
(`Continuous.ext_on : Dense s → Continuous f → Continuous g → EqOn f g s → f = g` — a standard
mathlib fact for continuous functions into a `T2Space`/Hausdorff codomain, here `ℂ`; to be
confirmed by exact name at build time, trivial ~5-line fallback via `IsClosed.closure_subset`/
`Set.EqOn.closure` + `Dense.closure_eq` if the precise name differs). Combined with
`RS.dense_setOf_isRegularValue`/`RS.setOf_isRegularValue_mem_cofinite`
(`MappingDegree/Ramification.lean:116-128`, already proved: the regular-value locus of a
nonconstant `ContMDiff ω` map is cofinite, hence dense), this is the **single move** that upgrades
every "holds at regular values" fact below into "holds everywhere on `Y`" — exactly the upgrade
that `MTrace.trace`-based objects (§0) could *never* get, because they are provably discontinuous,
not merely "not yet shown continuous."

---

## 6. `Form1.trace` — the hard direction (`Trace.lean`)

### 6.1 Target signature

```lean
noncomputable def Form1.trace (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Form1 X →ₗ[ℂ] Form1 Y :=
  if hne : ¬ ∃ c, ∀ x, f x = c then
    { toFun := fun η => Form1.ofCoeffs (traceCoeffData f hf hne η), map_add' := ..., map_smul' := ... }
  else 0
```
(total, `dite`-dispatched exactly like `RS.MTrace.trace`'s own convention — junk `0` for constant
`f`, matching the challenge's `pullback`... "Equal to the zero map if the map on curves is
constant" *precisely*, since `Jacobian.pullback`'s underlying `T` is `dualMap (Form1.trace f hf)`
and `dualMap 0 = 0`.)

### 6.2 The chart data, for nonconstant `f` (`hne`)

Chart family `ι := Y`, `chart := fun y => chartAt ℂ y` (`Y`'s own preferred charts — trivially
covering/`mem_maximalAtlas`/`exists_mem`). For each `y : Y`, using `exists_fiberStack hf hne y :
Nonempty (FiberStack f y)` (`MappingDegree/LocalStructure.lean:102`), fix `S := (exists_fiberStack
hf hne y).some`, and define (schematically, in `chart y`'s target coordinate `w`, near `chartAt ℂ
y y`):
```lean
coeff y w := ∑ i : Fin S.n,
  deriv (⇑(chartAt ℂ y) ∘ (S.A i).e'.symm) ((S.A i).e' ((chartAt ℂ y).symm w)) *
    traceZkForm (coeffIn (S.A i).e η) (multiplicity f (S.pt i)) ((S.A i).e' ((chartAt ℂ y).symm w))
```
i.e.: (1) evaluate `traceZkForm` — the Jacobian-divided, per-branch `traceZk` object already built
in `Jacobian/FormTrace/TraceZkForm.lean:44-45` — of `η`'s own source-chart coefficient
`coeffIn (S.A i).e η`, at the branch's own target-chart coordinate (`(S.A i).e' ((chartAt ℂ
y).symm w)`); (2) transport that branch's contribution from `(S.A i).e'`'s coordinate back to the
reference chart `chartAt ℂ y` via the (always-analytic, since both are maximal-atlas charts of the
*same* manifold `Y`) transition derivative — this is *exactly* `resAtP1_trace_eq_sum`'s `hcal`
reconciliation pattern (`FormTrace/ResidueTraceCompat.lean:142-147`) generalized from a residue
identity to a full coefficient formula, and (3) sum over the (finite) fibre index `i`.

**Regular case is a strict specialization**: at a regular `y` every `multiplicity f (S.pt i) = 1`
(`multiplicity_eq_one_of_isRegularValue`), and `traceZkForm h 1 w = h w` trivially (`k=1`: the
Jacobian factor `1·v^0 = 1` and the root set `{z | z = w} = {w}`) — so `coeff y` there is *literally*
`∑_i (transported coeffIn (S.A i).e η)`, an elementary finite sum of honest local sections'
coefficients, transported by analytic chart transitions — analytic by inspection (composition/sum
of finitely many analytic pieces), **no `traceZk` machinery needed at all in this case**. This
matches the classical fact that tracing is trivial away from branching.

### 6.3 Proof plan: analyticity across branch points (the unit's hardest analytic content,
~45 lines)

Fix a branch value `y₀ ∈ branchLocus f` (finitely many, `branchLocus_finite hf hne`,
`MappingDegree/Ramification.lean:101-103`). Need: `coeff y₀` is `AnalyticAt` at `(chartAt ℂ y₀)
y₀ = 0`-ish (WLOG translate). Fix the `FiberStack S` at `y₀` used to define it; each branch `i`
has `k_i := multiplicity f (S.pt i) ≥ 1`. **Per-branch step**: show
```lean
AnalyticAt ℂ (traceZkForm (coeffIn (S.A i).e η) k_i) ((S.A i).e' y₀)
```
via the removable-singularity route already half-built by `meromorphic-trace`:
1. `h := coeffIn (S.A i).e η` is `AnalyticOnNhd ℂ` on the whole target of `(S.A i).e`
   (`Form1.analyticOnNhd_coeffIn`, no restriction), in particular analytic (hence **locally
   bounded**, `AnalyticAt.continuousAt`/`ContinuousAt.norm.exists_lt` on a compact sub-closed-ball)
   on a punctured neighborhood of the branch point's own coordinate `0` in `(S.A i).e`'s target.
2. `h v / (k_i · v^{k_i - 1})`, the Jacobian-divided integrand feeding `traceZkForm` (recall
   `traceZkForm h k w := traceZk (fun v => h v * (k·v^{k-1})⁻¹) k w`), is analytic *and bounded*
   on that same punctured neighborhood **only away from `v = 0`** if `k_i > 1` (division by
   `v^{k_i-1}` blows up at `v=0` — but `v=0` is *excluded* from the punctured neighborhood by
   definition, and the boundedness we need is on the domain `traceZk`'s root-sum actually visits,
   which is exactly `{v : v^{k_i} = w}` for `w` near (not equal to) `0` — so as `w → 0`, the roots
   `v → 0` too, and we need boundedness of `h(v)/(k_i v^{k_i-1})` as `v → 0` **not** as a
   standalone function, but multiplied against the `traceZk` root-sum structure). The clean way to
   package this (avoiding a spurious `v=0` singularity worry) is to work one level down, directly
   with **`RS.laurentCoeffAt_traceZkForm`** (`FormTrace/TraceZkForm.lean:80-81`, already proved):
   `laurentCoeffAt (traceZkForm h k) 0 j = laurentCoeffAt h 0 (k·j + (k-1))` for `h`
   `MeromorphicAt 0`. Since `h := coeffIn (S.A i).e η` is **analytic** (not just meromorphic) at
   `0` (branch point's source coordinate), `laurentCoeffAt h 0 m = 0` for all `m < 0`
   (`residue-calculus`'s standard analytic-vanishing fact, already used throughout
   `MeromorphicTrace`/`FormTrace`). Then `laurentCoeffAt (traceZkForm h k) 0 j = 0` whenever
   `k·j + (k-1) < 0`, i.e. whenever `j < 0` (since `k ≥ 1 ⟹ k·j ≤ -k < 0 ⟹ k·j + (k-1) < 0` for
   `j ≤ -1` — check: `j=-1`: `k(-1)+(k-1) = -1 <0` ✓; induction downward for `j<-1` similarly) —
   i.e. **`traceZkForm h k` has NO negative Laurent coefficients at `0`, hence
   `MeromorphicAt.of_laurentCoeffAt_eventually_eq_zero`-style upgrade (a standard
   `residue-calculus`/`Laurent-tails`-*free* fact: a meromorphic function with no negative-order
   Laurent coefficients is analytic — provable directly from the Laurent series definition already
   in `residue-calculus`, not gated on `laurent-tails`'s tail-space machinery)** gives `AnalyticAt
   ℂ (traceZkForm h k) 0` **directly**, entirely by the Laurent-coefficient route, sidestepping
   the boundedness/removable-singularity argument (`exists_analyticAt_traceZk`) altogether. This
   is the **cleaner of two available routes** (see Risk R2, §13) — it reuses
   `laurentCoeffAt_traceZkForm` (already public) instead of needing `PlanarTrace.lean`'s private
   `exists_analyticAt_traceZk` made public, at the cost of needing the small
   "no-negative-Laurent-coefficients ⟹ analytic" bridge lemma (should already exist somewhere in
   `residue-calculus`/`Meromorphic`, since it is the standard characterization of a removable
   singularity via Laurent series — to be confirmed at build time; fallback: reprove it in ~10
   lines from `MeromorphicAt`'s own definition, a completely standard complex-analysis fact).
3. Compose with the (always-analytic, chart-transition) reconciliation factor from `(S.A i).e'`'s
   coordinate to `chartAt ℂ y₀`'s coordinate (`AnalyticAt.mul`/`.comp`, standard, ~5 lines).
4. **Sum over `i : Fin S.n`** (finite sum of `AnalyticAt`, `AnalyticAt.sum`/`Finset.sum`
   induction, trivial) gives `AnalyticAt ℂ (coeff y₀) 0` (in the translated chart coordinate).

~45 lines total for this analyticity argument (steps 1-4), matching the task's request for
40+ lines here — this is genuinely the hardest single analytic fact in the unit, but it is a
**direct reuse** of `laurentCoeffAt_traceZkForm` (already proved, zero sorries, in
`FormTrace/TraceZkForm.lean`), needing only the (expected-easy, to-confirm) Laurent-vanishing
bridge as new content.

### 6.4 Proof plan: `compat` (chart-transition law), via Density.lean's Lemma A

`compat y y'` (between `chart y = chartAt ℂ y` and `chart y' = chartAt ℂ y'`, both members of the
`ι := Y` chart family) needs to hold **on the whole overlap** `(chartAt ℂ y).source ∩ (chartAt ℂ
y').source`, including through any branch points the overlap might contain. Key move: **the
regular-value locus is dense** (`dense_setOf_isRegularValue`) and **on the (dense, open) subset of
the overlap consisting of regular values `z`, `compat` is an elementary, manifestly-transition-
correct identity** (§6.2's regular case: both `coeff y` and `coeff y'` restricted to regular `z`
are honest finite sums of transported local sections of `η`, and any two charts' coefficients of
the SAME finite sum of genuine 1-form sections transition correctly by definition — no
`FiberStack`-choice-dependence survives at a regular point since the fibre there is canonical, one
point per sheet, transported unambiguously). Both sides of the `compat` equation (`coeff y'
(chart y' x)` and `deriv(...) * coeff y (chart y x)`) are, by §6.3, **analytic** functions of `x`
on the overlap (composition of the already-established per-chart analyticity with the fixed
analytic chart transition). Two analytic (hence continuous) functions of `x` that agree on a dense
subset of the (open, connected-component-wise — work one connected component of the overlap at a
time, or just use density directly since `Form1.eq_of_eqOn_dense` only needs density, not
connectedness) overlap **agree everywhere on it**, by `Density.lean`'s `Continuous.ext_on`-based
argument applied locally (a direct corollary of Lemma A's proof, or literally reuse `Continuous.
ext_on` in-line rather than through the packaged `Form1.eq_of_eqOn_dense`, since here we want
pointwise/local equality of two chart-coefficient functions, not global `Form1` equality — a
~10-line specialization). **~15-20 lines total** given §6.3 and Density.lean are already in place.

### 6.5 Assembly and basic algebra

`Form1.ofCoeffs (traceCoeffData ...)` (via §6.3's analyticity + §6.4's compat), `map_add'`/
`map_smul'` (linearity of the whole construction in `η`, since `traceZkForm`/`traceZk` are
ℂ-linear in their function argument — `traceZk_add`/`traceZk_smul`-style facts, likely already
present or trivial one-liners from the `finsum` definition), `Form1.trace_id` (`f = id`: every
fibre is a single unramified point, `S.n=1`, `traceZkForm(h)(1)(w)=h(w)`, matching `id` exactly —
~10 lines), `Form1.trace_of_forall_eq (c : Y) : Form1.trace (fun _ => c) hf = 0` (the `dite`'s
`else` branch, `rfl`-level).

---

## 7. Trace–path-integral relation (`TraceIntegral.lean`) — the unit's hardest content

### 7.1 Target statement

```lean
theorem pathIntegral_trace {y : Y} (γ : Path y y) (hy : y ∉ branchLocus f) (η : Form1 X) :
    ∃ (lifts : Fin (RS.multiplicity ... ) → ...),  -- schematic, see §7.3 for the precise shape
    pathIntegral γ (Form1.trace f hf hne η) =
      ∑ x ∈ (f ⁻¹' {y}).toFinset, pathIntegral (liftedSheet f hf hne γ hy x) η
```
where `liftedSheet f hf hne γ hy x : Path x (monodromy γ x)` is, for each preimage `x ∈ f ⁻¹' {y}`,
the path obtained by "following `γ` starting at `x`" through the local trivialization off
`branchLocus f` (`monodromy γ : (f ⁻¹' {y}) → (f ⁻¹' {y})` the resulting permutation of the fibre).

### 7.2 Why a from-scratch construction, not mathlib's abstract covering-space lifting

`Mathlib.Topology.Homotopy.Lifting`'s `IsCoveringMap.liftPath`/`IsCoveringMapOn.
existsUnique_continuousMap_lifts` (never imported anywhere in this project) *could* supply the
lift abstractly, composed with `MappingDegree/Covering.lean`'s already-built
`isCoveringMapOn_compl_branchLocus hf hne : IsCoveringMapOn f (branchLocus f)ᶜ`. This is recorded
as the **documented fallback** (§13, R1) if the from-scratch route below proves fiddlier than
expected. But the **from-scratch route is recommended as primary**: it reuses the project's own
`ChartChain`/Lebesgue-number idiom (`Path/Chain.lean`, already the exact tool `pathIntegral`'s own
existence proof is built from) instead of importing a new, heavier abstract API, and — more
importantly — it produces the lift **already broken into the same finitely-many `FiberStack`-local
pieces** that the trace's own local formula (§6.2) needs to match against; the mathlib route would
still need this same local matching as a *second* step after obtaining the abstract lift, so the
from-scratch route does strictly less redundant work.

### 7.3 Construction: `FiberChain` (a `ChartChain`-style subdivision by `FiberStack`s)

**Step 1 (reduce to a regular basepoint off the branch locus).** `hy : y ∉ branchLocus f` is
required directly in the statement (rather than derived) — callers (§9) supply it via: any loop
`γ₀` based at an arbitrary point is homotopic, rel endpoints, to one based at a **regular** value,
using `period_conj` (conjugate by a connecting path to move the basepoint to a chosen regular
value `y'`, which exists by `exists_isRegularValue`) *and then* `Loop.exists_homotopic_avoiding`
(`Path/Perturb.lean`, using `hS : (branchLocus f).Finite` from `branchLocus_finite`) to homotope
the whole loop off `branchLocus f` entirely (not just its basepoint) — both period-preserving
(`period_congr_homotopic`), so this reduction costs nothing at the period-vector level (§9).

**Step 2 (subdivide `γ` into a `FiberChain`).** For each `t ∈ [0,1]`, `γ(t) ∉ branchLocus f`
(range disjoint from the branch locus by Step 1's construction), so `exists_fiberStack hf hne
(γ(t))` gives a `FiberStack` `S_t` with neighborhood `S_t.V ∋ γ(t)`, **all multiplicities `1`**
(regular value). By continuity of `γ` and compactness of `[0,1]`, get (mirroring
`exists_chartChain`'s Lebesgue-number proof **exactly**, replacing "chart ball" with "`FiberStack`
neighborhood `V`") a finite subdivision `0 = t_0 < t_1 < … < t_N = 1` and, for each piece `k`, a
single `FiberStack` `S_k` (at some `y_k ∈ γ([t_k,t_{k+1}])`) with `γ([t_k,t_{k+1}]) ⊆ S_k.V`. This
is a **new, small structure** `FiberChain γ` (~40 lines, direct copy of `ChartChain`'s proof shape
substituting `FiberStack.V` for chart balls — LOW risk, it is a mechanical re-run of an existing
proof pattern, not new mathematics).

**Step 3 (propagate a fibre-labeling across pieces).** Since all `S_k` have multiplicity `1`
everywhere on `S_k.V` (regular values throughout — `Step 1`'s avoidance), each `S_k` gives
`S_k.n = degree f`-many honest **local inverse branches** `σ_{k,i} : S_k.V → X` (`i : Fin
S_k.n`, `σ_{k,i}(y) := (S_k.A i).e.symm ((S_k.A i).e' y)` — well-defined and `ContMDiff ω` on
`S_k.V` since each `(S_k.A i)` is unramified, i.e. `k_i = 1` there literally means `(S_k.A i).e' ∘
f = (S_k.A i).e` on the source, so `(S_k.A i).e.symm ∘ (S_k.A i).e'` **is** a genuine local
right-inverse of `f`, `ContMDiff ω` by `OpenPartialHomeomorph`'s own smoothness plus `IsManifold`'s
transition-analyticity). On the overlap `S_k.V ∩ S_{k+1}.V ∋ γ(t_{k+1})`, both stacks' branch
labelings restrict to bijections `F⁻¹{γ(t_{k+1})} ≅ Fin S_k.n` / `≅ Fin S_{k+1}.n`; compose to get
a **matching permutation** `τ_k : Fin S_k.n ≃ Fin S_{k+1}.n` (well-defined since both `σ_{k,i}`
and `σ_{k+1,i'}`, evaluated at `γ(t_{k+1})`, are single points of the same finite fibre, and the
matching is "same point ⟹ same index"). This is the **whole content of "monodromy"** here, made
completely explicit and finite (no fundamental-group/covering-space abstraction needed) — ~30
lines (`Finset`/`Fintype` bijection bookkeeping).

**Step 4 (assemble lifted sheets).** For each `x ∈ f⁻¹{y}` (`y := γ(0) = γ(1)`, the basepoint,
regular so `f⁻¹{y}` is a genuine `Fin (degree f)`-indexed finite set via `S_0`'s own labeling, `x
= σ_{0,i₀}(y)` for a unique `i₀`), define the **lifted sheet** `Γ_x : Path x (σ_{N-1,τ(i₀)}(y))`
(`τ := τ_{N-1} ∘ ⋯ ∘ τ_0` the total monodromy permutation, matched back to `Fin S_0.n` via `S_0 =
S_N`'s shared basepoint) by **concatenating**, piece by piece, `(σ_{k, i_k} ∘ γ)|_{[t_k,t_{k+1}]}`
(`i_k` the label carried forward via `τ_0,…,τ_{k-1}`) — a `Path.trans` chain of `N` pieces, each
individually a genuine path since `σ_{k,i_k}` is `ContMDiff ω` hence continuous and each piece is
`γ` restricted-and-reparametrized into `[0,1]` (`Path.Icc`/segment-restriction machinery already
used by `ChartChain`'s own consumers, e.g. `IsPrimitiveAlongMap.glue`'s subdivided-path idiom).
`Γ_x` need **not** be a loop (`σ` may not fix `i₀`) — this is expected and fine; only the FULL
collection `{Γ_x}_{x ∈ f⁻¹{y}}`, summed, is used (§7.4/§9), never an individual `Γ_x`'s period in
isolation.

### 7.4 Proof plan: `pathIntegral_trace` itself, via local primitive matching (~45 lines given
§7.3)

Both sides of the target equation are computed via **local primitives glued along the SAME
subdivision `t_0 < … < t_N`** (this is the "reduce to chart-local primitive matching" move flagged
in the task mandate): on piece `k` (`t ∈ [t_k, t_{k+1}]`), a primitive of `Form1.trace f hf hne η`
along `γ|_{[t_k,t_{k+1}]}`, in the target chart `chartAt ℂ y_k` say, is — by `Form1.
coeffIn_ofCoeffs`/`coeffIn_pullback`-style rechart of §6's defining formula, restricted to `S_k`'s
regular-value case (elementary sum, §6.2) — **literally the sum over `i : Fin S_k.n` of a primitive
of `coeffIn (S_k.A i).e η` transported through `σ_{k,i}`**; but "`a primitive of `coeffIn (S_k.A
i).e η` transported through `σ_{k,i}`" is *exactly* what `IsPrimitiveAlongMap.pullback_comp`
(§4.2, applied to the local biholomorphism `σ_{k,i}` in place of a general `f`) produces as a
primitive of `Form1.pullback σ_{k,i} (hσ_{k,i}) η` — and since `σ_{k,i}` is a local **section**
of `f` (`f ∘ σ_{k,i} = id`), `Form1.pullback σ_{k,i} (hσ_{k,i}) η`'s path integral along
`γ|_{[t_k,t_{k+1}]}` is, by `pathIntegral_pullback` (§4.1) applied with `f := σ_{k,i}`, exactly
`pathIntegral (σ_{k,i} ∘ γ|_{[t_k,t_{k+1}]}) η` — i.e. the `i`-th piece of the `i_k`-labeled
lifted-sheet segment from §7.3 Step 4. **So, piece by piece, a primitive of the LHS (`Form1.trace
f hf hne η` along `γ`) is exactly the sum, over `i`, of primitives of the RHS's per-sheet pieces**
— both sides' primitives agree termwise on every subdivision piece, so by `pathIntegral_trans`
(additivity under concatenation, applied `N` times to both the trace-side single path `γ` — no
subdivision needed there, `pathIntegral` doesn't care how you chop it, only the PRIMITIVE
construction does — and the lifted-sheets side, which is *defined* as a concatenation) and
`IsPrimitiveAlong.pathIntegral_eq`, the two totals match: `pathIntegral γ (Form1.trace f hf hne
η) = ∑_k ∑_{i} pathIntegral (piece k of the i-labeled sheet) η = ∑_{x} pathIntegral Γ_x η`
(reindexing the double sum by "starting label `i₀` at `t_0`", using §7.3's bijective labeling to
match `x ↔ i₀` and collapsing the inner telescoping sum over `k` for a *fixed* starting label into
`pathIntegral Γ_x η` via repeated `pathIntegral_trans`). ~45 lines of bookkeeping (subdivision
sums, reindexing by the label bijections, repeated `pathIntegral_trans`), **zero new
mathematical content beyond §4's naturality lemma applied to local inverse branches** — this is
the payoff of designing `TraceIntegral` to depend on `PullbackIntegral`: the "hard" content is
front-loaded into building the `FiberChain`/lifted-sheets scaffolding (§7.3, itself mechanical);
the actual integral identity is then a direct, repeated application of naturality already proved.

### 7.5 Corollary used by §9: sum over the fibre lands in `periodSubgroup X`

For `γ` a loop at a regular `y`, avoiding `branchLocus f` (§7.1's `hy`), decompose `f⁻¹{y}` by the
cycles of the total monodromy permutation `τ` (§7.3): for each cycle `(x_1 → x_2 → ⋯ → x_ℓ →
x_1)`, concatenating the `ℓ` lifted sheets `Γ_{x_1}.trans (Γ_{x_2}.trans (⋯.trans Γ_{x_ℓ}))`
(endpoint-matched by construction, using `Path.cast` along the propositional equalities
`τ(x_j) = x_{j+1}` — `pathIntegral_cast` is a `@[simp]` no-op on the integral itself) produces an
honest **loop** based at `x_1`, with `pathIntegral (this loop) η = ∑_{j=1}^{ℓ} pathIntegral
Γ_{x_j} η` (`pathIntegral_trans`, iterated). Summing over all cycles reconstructs `∑_x
pathIntegral Γ_x η` exactly (a reordering of the same finite sum). Each cycle-loop, being a
based loop at some `x_1 ∈ X` (not necessarily the fixed arbitrary basepoint of `periodSubgroup
X`'s own definition), has `periodVector (basis X) (cycle-loop) ∈ periodSubgroup X` **exactly**, by
`RS.periodVector_mem_periodSubgroup` (basepoint-flexible, `JacobianConstruction/OfCurve.lean:46-47`
— already proved, exactly for this kind of use). **Conclusion**: `∑_x pathIntegral Γ_x η`, for
`η := basis X i`, is a `ℤ`-linear combination (sum) of elements of `periodSubgroup X`, hence itself
∈ `periodSubgroup X` (a subgroup is closed under finite sums) — **exact** membership, not merely
closure. ~25 lines (cycle-decomposition bookkeeping via `Equiv.Perm.cycleOf`/`Equiv.Perm.
sameCycle`-style mathlib API, or a direct hand-rolled "iterate `τ` from `x` until return" argument
— either is fine at this level of generality; standard finite combinatorics, no analysis).

---

## 8. Period-space plumbing (`PeriodMaps.lean`)

### 8.1 Coordinatization (spiked, §16 — compiles clean)

```lean
noncomputable def periodCoordEquiv (X) [...] :
    Module.Dual ℂ (RS.Form1 X) ≃ₗ[ℂ] (Fin (genus X) → ℂ) :=
  (RS.basis X).dualBasis.equivFun
```
(`Module.Basis.dualBasis_repr : b.dualBasis.repr l i = l (b i)` confirms `periodCoordEquiv X φ =
fun i => φ (basis X i)`, matching `periodVector`'s own defining formula
`periodVector b γ i = period γ (b i) = pathIntegralₗ γ (b i)` under `φ := pathIntegralₗ γ`.)

```lean
noncomputable def pushforwardT (f : X → Y) (hf) : (Fin (genus X) → ℂ) →ₗ[ℂ] (Fin (genus Y) → ℂ) :=
  (periodCoordEquiv Y).toLinearMap ∘ₗ (Form1.pullback f hf).dualMap ∘ₗ (periodCoordEquiv X).symm.toLinearMap

noncomputable def pullbackT (f : X → Y) (hf) : (Fin (genus Y) → ℂ) →ₗ[ℂ] (Fin (genus X) → ℂ) :=
  (periodCoordEquiv X).toLinearMap ∘ₗ (Form1.trace f hf).dualMap ∘ₗ (periodCoordEquiv Y).symm.toLinearMap
```

### 8.2 `hT` for `pushforwardT` (easy — exact containment, no closure/density needed)

```lean
theorem periodSubgroup_le_comap_pushforwardT :
    RS.periodSubgroup X ≤ (RS.periodSubgroup Y).topologicalClosure.comap
      (pushforwardT f hf).toAddMonoidHom
```
Suffices (`AddSubgroup.closure_le`) to check generators: for `γ : Path x₁ x₁` (`x₁ :=
Classical.arbitrary X`, `periodSubgroup X`'s fixed generating basepoint), show `pushforwardT f hf
(periodVector (basis X) γ) ∈ (periodSubgroup Y).topologicalClosure`. Unfold: `pushforwardT f hf
(periodVector (basis X) γ) i = (Form1.pullback f hf).dualMap (pathIntegralₗ γ) (basis Y i) =
pathIntegral γ (Form1.pullback f hf (basis Y i)) = pathIntegral (γ.map hf.continuous) (basis Y i)`
(`pathIntegral_pullback`, §4.1) `= periodVector (basis Y) (γ.map hf.continuous) i`. So
`pushforwardT f hf (periodVector (basis X) γ) = periodVector (basis Y) (γ.map hf.continuous)`,
and `γ.map hf.continuous : Path (f x₁) (f x₁)` is an honest **based loop** in `Y` (at `f x₁`, not
necessarily `Y`'s own fixed arbitrary basepoint) — so `RS.periodVector_mem_periodSubgroup (γ.map
hf.continuous) : periodVector (basis Y) (γ.map hf.continuous) ∈ periodSubgroup Y ≤
(periodSubgroup Y).topologicalClosure` (`AddSubgroup.le_topologicalClosure`) finishes. **~15
lines, exact membership, no perturbation/lifting needed** — this is the "easy direction" payoff.

### 8.3 `hT` for `pullbackT` (hard — needs §7's relation + monodromy-cycle argument)

```lean
theorem periodSubgroup_le_comap_pullbackT :
    RS.periodSubgroup Y ≤ (RS.periodSubgroup X).topologicalClosure.comap
      (pullbackT f hf).toAddMonoidHom
```
**Case `f` constant**: `Form1.trace f hf = 0` (§6.1's `dite`), so `pullbackT f hf = 0`, and `0 ∈
closure(…)` trivially — done in 2 lines.

**Case `f` nonconstant (`hne`)**: as in §8.2, reduce to generators `γ : Path y₁ y₁` (`y₁ :=
Classical.arbitrary Y`). Need `pullbackT f hf (periodVector (basis Y) γ) ∈
(periodSubgroup X).topologicalClosure`. **If `y₁` happens to be regular and `γ` happens to avoid
`branchLocus f`**, §7.5 applies directly (`pullbackT f hf (periodVector (basis Y) γ) i =
pathIntegral γ (Form1.trace f hf (basis X i)) = ∑_x pathIntegral Γ_x (basis X i) ∈
periodSubgroup X` **exactly**, stronger than needed). **In general** (`y₁` possibly a branch value,
`γ` possibly crossing `branchLocus f`): use `period_conj` to replace `γ` by a conjugate loop `γ' :=
(σ.trans γ).trans σ.symm` based at a *chosen* regular value `y' ∉ branchLocus f`
(`exists_isRegularValue`, connecting path `σ : Path y' y₁`), with `period γ' η = period γ η` for
every `η` (`period_conj`, `Path/Periods.lean:45`) — so `periodVector (basis Y) γ' = periodVector
(basis Y) γ` exactly, and `pullbackT f hf` applied to either gives the same result. Then further
replace `γ'` by `γ'' := (Loop.exists_homotopic_avoiding γ' (branchLocus_finite hf hne)
hy'-not-in-branchLocus).choose`, homotopic to `γ'` rel the (now branch-locus-avoiding) basepoint
`y'`, with `period γ'' = period γ'` (`period_congr_homotopic`). Now `γ''` satisfies §7.1's `hy`
hypothesis at basepoint `y'`, and §7.5 applies. **~20 lines given §7.5**, all glue (`period_conj`
+ `Loop.exists_homotopic_avoiding` + `period_congr_homotopic`, each a one-line citation).

### 8.4 Assembly

```lean
noncomputable def Jacobian.pushforward (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian X →ₜ+ Jacobian Y := Jacobian.inducedHom (periodSubgroup_le_comap_pushforwardT f hf)

noncomputable def Jacobian.pullback (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian Y →ₜ+ Jacobian X := Jacobian.inducedHom (periodSubgroup_le_comap_pullbackT f hf)
```
Matches `docs/Jacobian_challenge.lean:107-109,130-132` **verbatim** (same explicit `f`/`hf`
argument order the challenge and `ProperDegree.ChallengeDegree` already commit to — §11).

---

## 9. `ContMDiff`, functoriality laws, projection formula (`Challenge.lean`)

### 9.1 `ContMDiff` — free

```lean
theorem Jacobian.pushforward_contMDiff :
    ContMDiff 𝓘(ℂ, Fin (genus X) → ℂ) 𝓘(ℂ, Fin (genus Y) → ℂ) ω (Jacobian.pushforward f hf) :=
  Jacobian.contMDiff_inducedHom _   -- jacobian-construction's Functorial.lean:73-89, unchanged
```
Needs `[DiscreteTopology (periodSubgroup X).topologicalClosure]`/`[…Y…]` — exactly the same
gated instances `ofCurve_contMDiff`/every manifold instance on `Jacobian _` already needs (period-
lattice-rank's job, not this unit's — this unit inherits the gate transparently, no new gate
introduced). Symmetric for `pullback_contMDiff`.

### 9.2 Functoriality laws — need one small addition to `jacobian-construction`

`pushforward_id_apply`/`pushforward_comp_apply` reduce, via `Jacobian.inducedHom`'s definition
(`uliftUpHom.comp (Torus.inducedHom … T … ).comp uliftDownHom`) and `uliftDownHom.comp
uliftUpHom = id` (`ULift.down ∘ up = id`, trivial), to two facts about the abstract `Torus.
inducedHom` (`JacobianConstruction/Torus.lean §9.2`) that **do not currently exist**:
```lean
theorem Torus.inducedHom_id (L) [...] : Torus.inducedHom L L LinearMap.id hT_id = ContinuousAddMonoidHom.id _
theorem Torus.inducedHom_comp (L L' L'') (T hT) (T' hT') :
    (Torus.inducedHom L' L'' T' hT').comp (Torus.inducedHom L L' T hT) =
      Torus.inducedHom L L'' (T'.comp T) hT_comp
```
Both are one-line consequences of `QuotientAddGroup.map`'s own functoriality
(`QuotientAddGroup.map_id`/`map_comp_map`-style facts, standard group-quotient API) plus
`ContinuousAddMonoidHom`-level bundling (continuity of `id`/`comp` free). **Request filed to
jacobian-construction** (§14); **local `Compat` fallback** (proved once, in `Challenge.lean`,
clearly marked, per `CONVENTIONS.md` rule 4) if the request isn't picked up in time — ~20-30 lines
either way, low risk (pure group-quotient bookkeeping, no analysis).

Given these two, `pushforward_id_apply`/`pushforward_comp_apply` follow from `Form1.pullback_id`/
`Form1.pullback_comp` (§3.4) transported through `dualMap`'s own contravariant functoriality
(`LinearMap.dualMap_id`, `(g.comp f).dualMap = f.dualMap.comp g.dualMap`) into
`pushforwardT`/`Torus.inducedHom_id`/`_comp` — ~20 lines of composition bookkeeping.
`pullback_id_apply`/`pullback_comp_apply` are the dual argument via `Form1.trace_id` (§6.5) and a
new `Form1.trace_comp` (needs the **doubly-regular-value density argument** sketched in §7's
introduction — cofinite test set `Y \ (branchLocus g ∪ g '' (branchLocus f))`, no pointwise local-
multiplicativity lemma needed, avoiding a dependency on an unbuilt `multiplicity_comp` fact; ~30
lines given `Density.lean`'s Lemma A).

### 9.3 Projection formula

The Form1-level projection formula:
```lean
theorem Form1.trace_pullback_eq_degree_smul (η : Form1 Y) :
    Form1.trace f hf hne (Form1.pullback f hf η) = (ContMDiff.degree f hf : ℂ) • η
```
*Proof plan.* At a regular value `y` with `FiberStack S` (`S.n = degree f`, `MappingDegree`'s
`fiberMultSum_eq_sum`/`fiberMultSum_const`/`degree`-unfolding, all multiplicities `1`): both sides'
`coeffAt y` reduce, via §6.2's elementary regular-case formula and §3's pullback formula composed
(`f ∘ σ_{S,i} = id` for each unramified local section `σ_{S,i}`, so `Form1.pullback σ_{S,i}
(Form1.pullback f hf η) = Form1.pullback (f ∘ σ_{S,i}) η = Form1.pullback id η = η` by `Form1.
pullback_comp`/`pullback_id`, §3.4 — the chain-rule cancellation "pull back then push back along
the SAME unramified branch returns the original coefficient") to `∑_{i=1}^{S.n} coeffAt y η =
S.n • coeffAt y η = (degree f) • coeffAt y η` exactly. Then `Density.lean`'s Lemma A (both sides
are elements of `Form1 Y`, agreeing on the dense regular-value locus) upgrades this to equality of
`Form1`s. **~35 lines given §3, §6.2, §9.1's ingredients** (mirrors, and is a strict form-level
generalization of, `FormTrace/ResidueTraceCompat.lean`'s already-proved
`trace_pullback_eq_degree_smul_of_regular` — same regular-value computation, upgraded from
"regular values only" to "everywhere" using the NEW density tool that the function-level object
could never use, since it was proven discontinuous — §0).

Lifted to the challenge statement: `pushforwardT f hf ∘ pullbackT f hf = (degree f : ℂ) • id`
(dualMap of the Form1-level identity, `LinearMap.dualMap_smul`/`_comp`), then `Jacobian.inducedHom`
applied to `T := (degree f)•id` is `(degree f) • id` as a `→ₜ+` map (`QuotientAddGroup.map`
commutes with `nsmul` since `mk`/`map` are `AddMonoidHom`s — `map_nsmul`, standard; checked on
`mk`-representatives, extended to all of `Jacobian Y` via `QuotientAddGroup.mk_surjective` +
`Quotient.forall`-style surjectivity extension, ~15 lines) — giving
```lean
theorem Jacobian.pushforward_pullback (P : Jacobian Y) :
    Jacobian.pushforward f hf (Jacobian.pullback f hf P) = (ContMDiff.degree f hf) • P
```
verbatim against `docs/Jacobian_challenge.lean:151-152`. **Note**: this route needs `T_push ∘
T_pull = (deg f)•id` and a direct representative-level computation, **not** the general
`Torus.inducedHom_comp` from §9.2 (that general fact is only needed for `pullback_comp_apply`/
`pushforward_comp_apply` with two *different* maps `f`,`g` — the degree formula, using the *same*
`f` twice, is handled more directly here).

---

## 10. Constant-map conventions — summary (already threaded through §3, §6, §8)

| | `f` constant | `f` nonconstant |
|---|---|---|
| `Form1.pullback f hf` | `0` (automatic: `deriv` of a constant chart-read map is `0`, **no case split in the definition**) | genuine chain-rule pullback |
| `Form1.trace f hf` | `0` (`dite`'s `else` branch — the ONE explicit case split in the whole unit, matching `MTrace.trace`'s own convention) | `traceZkForm`-assembled trace |
| `Jacobian.pushforward f hf` | zero `→ₜ+` map (from `pullback=0`) | `Jacobian.inducedHom pushforwardT` |
| `Jacobian.pullback f hf` | zero `→ₜ+` map (matches challenge docstring **verbatim**: "Equal to the zero map if the map on curves is constant") | `Jacobian.inducedHom pullbackT` |
| `ContMDiff.degree f hf` | `0` (`ContMDiff.degree_of_forall_eq`, already proved, `ProperDegree/ChallengeDegree.lean:46-48`) | honest covering degree |
| `pushforward_pullback` at constant `f` | `0 = 0 • P = 0` (both sides `0`, via `pullback=0` and `degree=0`, no extra work) | §9.3 |

No new decidability/`IsConstant` predicate introduced — this design uses the project's
established `¬ ∃ c, ∀ x, f x = c` existential-negation convention throughout (matching
`MappingDegree`'s style exactly, per that unit's own research finding: no `Function.const`-based
predicate anywhere in the project).

---

## 11. Exact challenge signatures matched (verbatim, `docs/Jacobian_challenge.lean:104-153`)

```lean
variable (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)

def pushforward (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : Jacobian X →ₜ+ Jacobian Y := sorry
theorem pushforward_contMDiff :
  ContMDiff 𝓘(ℂ, Fin (genus X) → ℂ) 𝓘(ℂ, Fin (genus Y) → ℂ) ω (pushforward f hf) := sorry
lemma pushforward_id_apply (P : Jacobian X) : pushforward id contMDiff_id P = P := sorry
lemma pushforward_comp_apply (P : Jacobian X) :
    pushforward (g ∘ f) (hg.comp hf) P = pushforward g hg (pushforward f hf P) := sorry

def pullback (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : Jacobian Y →ₜ+ Jacobian X := sorry
theorem pullback_contMDiff :
    ContMDiff 𝓘(ℂ, Fin (genus Y) → ℂ) 𝓘(ℂ, Fin (genus X) → ℂ) ω (pullback f hf) := sorry
lemma pullback_id_apply (P : Jacobian X) : pullback id contMDiff_id P = P := sorry
lemma pullback_comp_apply (P : Jacobian Z) :
    pullback (g.comp f) (hg.comp hf) P = pullback f hf (pullback g hg P) := sorry

def _root_.ContMDiff.degree (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ := sorry   -- f explicit, see below
lemma pushforward_pullback (P : Jacobian Y) :
  pushforward f hf (pullback f hf P) = (ContMDiff.degree f hf) • P := sorry
```
`ContMDiff.degree` is **already built** at `ProperDegree/ChallengeDegree.lean:39` with `f`
**explicit** — confirmed load-bearing: the challenge's own `variable (f : X → Y)` (explicit) plus
the positional call `(ContMDiff.degree f hf) • P` at line 152 force this; `ProperDegree`'s
docstring records this as a deliberate deviation from an earlier implicit-`f` design sketch, now
corrected to match the gist verbatim. **This unit's own `pushforward`/`pullback`/`pushforward_
comp_apply`/`pullback_comp_apply` etc. must use the identical explicit-`f`/explicit-`hf`
convention** (already reflected throughout §8-§9 above) for the same reason — their own call
sites (e.g. `pushforward (g ∘ f) (hg.comp hf) P`) apply `f`/`g` positionally.

---

## 12. Gate confirmation — no dependency on canonical-forms / laurent-tails / serre-duality-tails

Every ingredient used above traces to one of exactly six units:

| Ingredient | Owning unit |
|---|---|
| `Form1`, `coeffIn`, `ofCoeffs`, `Form1CoeffData`, `analyticOnNhd_coeffIn`, `ext_coeffAt`, `mdifferential` (template) | **holomorphic-forms** |
| `pathIntegral`, `periodVector`, `period`, `IsPrimitiveAlongMap` (+`.rechart`/`.comp`), `ChartChain`/`exists_chartChain`, `Loop.exists_homotopic_avoiding`, `period_conj`, `pathIntegral_cast/trans` | **paths-and-integrals** |
| `traceZk`, `FiberStack`/`exists_fiberStack` (re-exported), `laurentCoeffAt_traceZk`, analytic-vanishing-of-Laurent-coefficients (standard, from the same file family) | **meromorphic-trace** |
| `traceZkForm`, `laurentCoeffAt_traceZkForm`, `resAtP1_trace_eq_sum`'s `hcal` pattern (used as a template, not imported), `trace_const_mul_pullback`/`trace_pullback_eq_degree_smul_of_regular` (superseded, not needed once §9.3 is built, but confirm no regression) | **form-trace-tower** |
| `FiberStack` (definition site), `degree`, `multiplicity`, `IsRegularValue`, `branchLocus`/`branchLocus_finite`, `exists_isRegularValue`, `isCoveringMapOn_compl_branchLocus` (documented fallback only), `AdaptedChartsAt` (via `LocalMultiplicity`, transitively) | **mapping-degree** (+ `LocalMultiplicity` transitively) |
| `ContMDiff.degree` (exact challenge wrapper), `degree_comp`, `degree_of_forall_eq` | **proper-map-degree** |
| `Jacobian.inducedHom`, `Jacobian.contMDiff_inducedHom`, `RS.basis`, `RS.periodSubgroup`, `periodVector_mem_periodSubgroup`, `Jacobian` type itself | **jacobian-construction** |

**No file above reads or imports** `Jacobian.CanonicalForms`, `Jacobian.LaurentTail`, or
`Jacobian.ProperDegree.DivisorDegreeZero`/`GenusZeroFinisher`/anything from
`serre-duality-tails`/`riemann-roch` (that unit is downstream of `ProperDegree`, not upstream of
it) — confirmed by tracing every citation above to source. **Gate confirmed: none beyond the six
units listed.**

---

## 13. Risks & fallbacks (ranked)

1. **R1 — `TraceIntegral.lean` (§7), highest risk.** The `FiberChain`/lifted-sheets/monodromy-
   cycle construction is the single largest genuinely new piece of engineering in the unit (~150-
   200 lines of new structure + bookkeeping, no direct precedent in the codebase beyond
   `ChartChain`'s *proof shape*, which it mechanically imitates). Mathematical content is standard
   (finite covering-space monodromy, made concrete) but the `Path.cast`/`Path.trans` endpoint-
   matching bookkeeping (§7.3 Step 4, §7.5's cycle concatenation) is fiddly. **Fallback**: import
   `Mathlib.Topology.Homotopy.Lifting` (`IsCoveringMap.liftPath`/`monodromy`,
   `IsCoveringMapOn.existsUnique_continuousMap_lifts`) composed with `MappingDegree/Covering.lean`'s
   already-built `isCoveringMapOn_compl_branchLocus` instead of the hand-rolled `FiberChain` —
   trades "reprove Lebesgue-subdivision by hand" for "learn mathlib's covering-space API and still
   need the same local-primitive-matching argument (§7.4) afterward," a lateral, not strictly
   cheaper, move; recorded as the documented alternative (§7.2), not preferred, since it does not
   remove the need for §7.4's matching argument, only replaces §7.3's construction.
2. **R2 — `Trace.lean`'s branch-point analyticity (§6.3), high risk.** Two routes identified: (a)
   the Laurent-coefficient route via `laurentCoeffAt_traceZkForm` + a "no negative Laurent
   coefficients ⟹ analytic" bridge (recommended, needs confirming/proving the bridge lemma, likely
   ~10-20 lines if not already present under `residue-calculus`); (b) making `PlanarTrace.lean`'s
   private `exists_analyticAt_traceZk` (boundedness-based removable singularity) public and
   composing it with the Jacobian-division used by `traceZkForm` (would need a small new lemma
   combining the two, not currently done anywhere — flagged by `meromorphic-trace`'s own research
   as a genuine, not-yet-built composition). **Request filed to meromorphic-trace** (§14) for
   either (a)'s bridge lemma or (b)'s visibility change, whichever is cheaper on their end; local
   `Compat` fallback for either, ~30-40 lines, if the request isn't picked up in time.
3. **R3 — `Density.lean`'s `Continuous.ext_on`, low-medium risk.** Exact mathlib name/hypotheses
   for "continuous functions agreeing on a dense set are equal" not confirmed by name (only by
   general-topology reasoning: standard for Hausdorff codomains). Fallback: ~5-line direct proof
   via `Set.EqOn.closure`/`IsClosed.mem_of_closure_subset`-style manual argument if the exact
   packaged lemma doesn't unify.
4. **R4 — `Torus.inducedHom_id`/`_comp` (§9.2), low risk.** Small, standard group-quotient
   compositionality facts, absent from `jacobian-construction`'s current `Functorial.lean`/
   `Torus.lean`. Request filed (§14); local `Compat` fallback, mechanical, ~20-30 lines.
5. **R5 — genus-0 degeneration, negligible risk.** `Form1 X`/`Form1 Y` zero-dimensional cases
   (`genus = 0`) trivialize every construction above (`Form1.pullback`/`Form1.trace` act on the
   zero module, `dualMap` of a map between zero modules is the zero map on a zero module,
   `Jacobian.inducedHom` degenerates to the already-covered one-point-space case per
   `jacobian-construction`'s own R5) — no special-casing needed, consistent with that unit's own
   verified stance.
6. **R6 — the `[DiscreteTopology (periodSubgroup _).topologicalClosure]` gate on `ContMDiff`
   proofs, zero risk to this unit specifically.** Inherited transparently from
   `jacobian-construction`/`period-lattice-rank`; this unit's `pushforward_contMDiff`/
   `pullback_contMDiff` are one-line corollaries of `contMDiff_inducedHom` regardless of when that
   gate is discharged upstream — no new gate introduced here.

---

## 14. Requests to other units

Filed in `docs/requests/jacobian-construction.md`:
1. `Torus.inducedHom_id (L) : Torus.inducedHom L L LinearMap.id (trivial hT) =
   ContinuousAddMonoidHom.id _` and `Torus.inducedHom_comp` (compositionality of the abstract
   `V⧸L →ₜ+ V'⧸L'` substrate under composing two induced homs) — §9.2, needed for
   `pushforward_comp_apply`/`pullback_comp_apply`. Non-blocking: local `Compat` copy carried either
   way.

Filed in `docs/requests/meromorphic-trace.md`:
1. Either (a) a public "no negative Laurent coefficients at a point ⟹ `AnalyticAt` there" bridge
   lemma (if not already present under `residue-calculus`), or (b) making
   `PlanarTrace.lean`'s private `exists_analyticAt_traceZk` public/reusable — §6.3/R2. Non-blocking:
   local reproof carried either way.

No requests filed to `holomorphic-forms`, `paths-and-integrals`, `mapping-degree`,
`proper-map-degree`, or `form-trace-tower` — every ingredient consumed from them is already public
and exactly shaped for this unit's needs (confirmed by the research pass, §0/§12).

---

## 15. Downstream consumption

**Final assembly only** (`Jacobian/Challenge.lean`, per `CONVENTIONS.md`'s workflow — this unit is
itself the last piece of the `Jacobian_challenge.lean` API surface listed in the "Main missing
definitions/theorems" header, together with `genus`/`Jacobian`/`ofCurve`, all now fully covered
across `holomorphic-forms`→`jacobian-construction`→this unit). No other unit's design doc names
`jacobian-functoriality` as a dependency (confirmed: this is a leaf in the blueprint-plus-gap DAG).
Orchestrator action once built: register `import Jacobian.JacobianFunctoriality` in `Jacobian.lean`
and in the final `Jacobian/Challenge.lean` assembly alongside `Jacobian.JacobianConstruction`.

---

## 16. Spike report (`scratch_jfun.lean`, 39 lines, kept at project root)

Gated per protocol (`pgrep -cx lean` was `0` before running). Compiles clean, `lake env lean
scratch_jfun.lean`, ~8.7s wall, exit 0, only the expected `sorry`-usage warning. Two items, the
riskiest elaboration points identified during design:

1. **The `dualMap` + `Basis.dualBasis.equivFun` coordinatization (§8.1) typechecks exactly as
   designed**, including feeding the result straight into `Jacobian.inducedHom`'s implicit
   `T`/explicit `hT` argument shape with no unification friction:
   ```lean
   example (L : RS.Form1 Y →ₗ[ℂ] RS.Form1 X) :
       (Fin (genus X) → ℂ) →ₗ[ℂ] (Fin (genus Y) → ℂ) :=
     (RS.basis Y).dualBasis.equivFun.toLinearMap ∘ₗ
       (L.dualMap ∘ₗ (RS.basis X).dualBasis.equivFun.symm.toLinearMap)

   example (L : RS.Form1 Y →ₗ[ℂ] RS.Form1 X)
       (hT : RS.periodSubgroup X ≤ (RS.periodSubgroup Y).topologicalClosure.comap
         (((RS.basis Y).dualBasis.equivFun.toLinearMap ∘ₗ
           (L.dualMap ∘ₗ (RS.basis X).dualBasis.equivFun.symm.toLinearMap))).toAddMonoidHom) :
       Jacobian X →ₜ+ Jacobian Y :=
     Jacobian.inducedHom hT
   ```
   This de-risks §8's whole plumbing story: the exact mathlib names (`Basis.dualBasis`,
   `.equivFun`, `LinearMap.dualMap`, `LinearEquiv.toLinearMap`, `∘ₗ`) compose with **zero manual
   coercion/`rfl`-massaging**, and `Jacobian.inducedHom`'s implicit `T` unifies against the
   constructed term directly from `hT`'s type, exactly as `jacobian-construction`'s own design
   anticipated.
2. **A minimal `Form1CoeffData`/`Form1.ofCoeffs` structure literal (§3.1/§6.1's shape) elaborates**
   against the real fields (`chart`, `mem_maximalAtlas`, `exists_mem`, `coeff`, `analyticOnNhd`,
   `compat`) with a trivial one-chart family and `sorry`'d mathematical content:
   ```lean
   example [Nonempty X] : RS.Form1CoeffData X Unit where
     chart _ := chartAt ℂ (Classical.arbitrary X)
     mem_maximalAtlas _ := sorry
     exists_mem _ := sorry
     coeff _ := fun _ => 0
     analyticOnNhd _ := sorry
     compat _ _ _ _ := sorry

   example [Nonempty X] (D : RS.Form1CoeffData X Unit) : RS.Form1 X := RS.Form1.ofCoeffs D
   ```
   confirming the `Form1.pullback`/`Form1.trace` "build a `Form1CoeffData`, call `.ofCoeffs`"
   assembly pattern (§3.1, §6.1) has no field-name/type surprises against the actually-built
   `holomorphic-forms` API (as opposed to the sub-agent-summarized version consulted during
   research). Not spiked (out of the ≤50-line budget; proof plans only, fully worked above):
   `pathIntegral_pullback`'s chain-rule/`eventuallyEq` bookkeeping (§4.2), the `FiberChain`
   construction (§7.3), and the Laurent-coefficient analyticity bridge (§6.3/R2) — these remain
   the highest-genuine-effort items for an implementation builder, though none are flagged as
   *mathematically* uncertain, only as engineering-effort items.
