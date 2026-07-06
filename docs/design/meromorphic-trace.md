# Design: meromorphic-trace (`Jacobian/MeromorphicTrace/`)

Blueprint unit **meromorphic-trace**. Blueprint text: "Surface-level trace of functions/forms
along a degree-`d` map, and the argument principle on `X` (zeros = poles for an exact
log-derivative trace)." Read: Forster §4 (Thm 4.24, Cor 4.25); Forster §8 (Thm 8.2, symmetric
functions of a covering extend across branch points — the classical shape of "trace of
functions"); Miranda Ch. VI §3 (the residue identity, eq. (3.2), PDF 198–200 — see §0.3 below for
a citation correction) and Ch. VIII §3 ("trace operations", PDF 263–268, Abel's necessity proof —
the other place Miranda uses `Tr_f`). Declared **Builds on:** jacobian-construction,
residue-calculus.

Everything below verified against pinned mathlib `548398201a64f3a5127d90d83945278cfe38cac4` by
reading source, and against the *actual built state* of upstream units (not just their design
docs) by reading their files on disk. One gated spike (`scratch_mtrace.lean`, §9) compiled clean.

---

## 0. Scope, the two deliverables, and a DAG correction

### 0.1 The two deliverable clusters

1. **The argument principle on `X`**: for `f : X → ℂ` meromorphic everywhere, "nonconstant", on
   compact connected `X`: `∑_x ordAtX f x = 0` (zeros counted with multiplicity cancel poles
   counted with multiplicity). This is the engine `proper-map-degree` uses for `deg(div f) = 0`;
   **we do not build `Divisor`/`deg(div f)` ourselves** (CC2, owned by meromorphic-and-divisors) —
   we deliver the finsum identity in `ordAtX` terms, stated so that repackaging it as
   `(divisor f).degree = 0` is a few lines of bookkeeping in `proper-map-degree`.
2. **The fibre trace of functions**: the planar atom `traceZk h k` (trace of `h` along `z ↦ z^k`
   near `0`) with meromorphy, linearity, pullback, and a Laurent-coefficient formula; and the
   surface-level assembly `Tr_F h : Y → ℂ` for `F : X → Y` holomorphic nonconstant of degree `d`.
   `form-trace-tower` builds the *pair-form* trace `Tr_F(h·ω)` and its rationality on top of this;
   we deliver only the function-level identities it lifts.

### 0.2 A DAG correction (flag for the orchestrator)

The blueprint's "Builds on: jacobian-construction, residue-calculus" is **incomplete** for the
actual Lean content. Both deliverables need:

- **mapping-degree** (`FiberStack`, `fiberMultSum`/`degree`, `fiber_finite`) — the blueprint's own
  `mapping-degree.md` design doc already lists meromorphic-trace as a consumer of exactly these
  exports (§7 downstream table there), so this is a real, load-bearing edge missing from the
  blueprint's edge list.
- **meromorphic-and-divisors** (`MeromorphicAtX`, `ordAtX`, the codiscrete dichotomy) — the
  `Predicates.lean` and `CodiscreteBridge.lean` layer (both **already built** at the time of this
  design) is the vocabulary "meromorphic function on `X`" is stated in; there is no way to state
  "`f` meromorphic on `X`" without it.
- **projective-line** (`OnePoint ℂ`, `coeChart`/`invChart`, `chartAt_coe`/`chartAt_infty`) — the
  target of the induced map `F : X → ℙ¹` cluster 1 needs.

`jacobian-construction` itself contributes **nothing** we call directly (its `Jacobian X` torus
type is irrelevant here); the edge is scheduling-only (it transitively pulls in mapping-degree and
paths-and-integrals, of which we need the former). `residue-calculus` **is** genuinely used, but
only by cluster 2 (`laurentCoeffAt`/`taylorCoeffAt`/`resAt` are the currency of the
Laurent-coefficient formula for `traceZk`), not cluster 1.

Action taken: requests filed in `docs/requests/projective-line.md` (new) and
`docs/requests/meromorphic-and-divisors.md` (appended) recording this; the orchestrator should
correct the blueprint's edge list for meromorphic-trace to read
`mapping-degree, meromorphic-and-divisors, projective-line, residue-calculus`.

### 0.3 A citation correction

Miranda's residue identity is **equation (3.2)** in §VI.3 (book p. 186 = PDF 198), not "Lemma
3.2" — §VI.3 has no numbered Lemma 3.2 (confirmed against `docs/refs/miranda-map.md`, itself
verified against the PDF). The identity is `Σ_p Res_p(r_p·ω) = 0`; the "trace" vocabulary Miranda
actually uses for functions (`Tr_f`) is in Ch. VIII §3 (PDF 263–268, Abel's theorem necessity
proof), not Ch. VI.

### 0.4 Why the argument principle is NOT proved via residues here

The blueprint phrase "exact log-derivative trace" suggests `Res(f'/f) = ord`
(`MeromorphicAt.resAt_deriv_div`, **already built** in residue-calculus) plus the global residue
theorem `∑ Res = 0`. **We do not take this route.** `proper-map-degree`'s blueprint entry states
the routing warning explicitly: *"get `deg(div f)=0` from the degree-counting route... not from a
general manifold Stokes theorem... the general-Stokes route to `deg∘div=0` is a dead end."* The
residue theorem (`∑Res=0`) is itself proved *later* (`residue-theorem` unit, Stokes-based) and is
not available to us; even if it were, routing through it here would violate the explicit warning.
We use `resAt_deriv_div` nowhere in cluster 1. (Residue-calculus's atoms are still needed — see
§0.2 — but for cluster 2's coefficient bookkeeping, not for the argument principle.)

---

## 1. Mathlib/project facts relied on (verified)

**Built, consumed as-is** (file:line under `.lake/packages/mathlib/Mathlib/` for mathlib; project
paths for project files):

- `RS.fiberMultSum`, `RS.degree`, `RS.FiberStack`, `RS.exists_fiberStack`,
  `RS.FiberStack.sum_multiplicity_inter_source`, `RS.fiberMultSum_eq_degree`,
  `RS.fiber_finite`, `RS.multiplicity_comp` — `Jacobian/MappingDegree/*.lean` (built; read on
  disk, §Background above).
- `RS.MeromorphicAtX`, `RS.MeromorphicOnX`, `RS.ordAtX`, arithmetic (`ordAtX_mul`, `ordAtX_inv`
  unconditional, `ordAtX_add_of_ne`), chart invariance (`ordAtX_eq_of_mem_source`),
  `tendsto_nhds_iff_ordAtX_nonneg`, `ordAtX_of_contMDiffAt_eq_zero` — `Jacobian/Meromorphic/
  Predicates.lean` (built).
- `RS.MeromorphicOnX.eventuallyEq_zero_or_forall_ordAtX_ne_top`,
  `RS.MeromorphicOnX.codiscrete_setOf_ne_zero`, `RS.eventuallyEq_codiscrete_iff`,
  `RS.eventuallyEq_codiscreteWithin_iff_of_isOpen` — `Jacobian/Meromorphic/CodiscreteBridge.lean`
  (built). **Not yet built**: `GermSpace.lean`/`OrderEval.lean`/`Field.lean`/`Divisor.lean`
  (the `ℳ X` quotient, `evalAt`/`holoRepr`, `Divisor`/`degree`). We do **not** depend on these —
  see D2 below (we build our own minimal chart-local "canonical value" helper instead of waiting
  on `evalAt`/`holoRepr`).
- `RS.P1.coeChart`, `RS.P1.invChart`, `chartAt_coe`, `chartAt_infty`, `coeChart_apply_coe/infty`,
  `invChart_apply_coe/infty` (unconditional), `coeChart_mem_maximalAtlas`,
  `invChart_mem_maximalAtlas` — `Jacobian/ProjectiveLine/Charts.lean` (built).
  **Not yet built**: `Holomorphy.lean` (`contMDiffAt_of_pole`, `ContMDiffAt.onePointCoe`,
  `meromorphicAt_coeChart_comp`, the general "`F:Z→ℙ¹` holomorphic iff analytic in
  `coeChart`/`invChart`" iff-lemmas). We **redesign the pole/coe constructors from scratch** in
  `ToP1.lean` using only `Charts.lean` + `LMCompat.contMDiffAt_iff_analyticAt_inChartAt`
  (general `X→Y` bridge, already built in local-multiplicity), so we do not block on
  `Holomorphy.lean` landing — see D2, P1.
- `RS.LMCompat.contMDiffAt_iff_analyticAt_inChartAt`, `RS.inChartAt`, `RS.multiplicityENat`,
  `RS.multiplicity`, `RS.multiplicityENat_def`, `RS.analyticOrderAt_charts_eq_multiplicityENat`
  — `Jacobian/LocalMultiplicity/{ChartBridge,Multiplicity}.lean` (built).
- `RS.AnalyticAt.exists_pow_eq` (local analytic `k`-th root of a nonvanishing germ) —
  `Jacobian/LocalMultiplicity/KthRoot.lean` (built) — **the** tool for `traceZk`'s local branches.
- `RS.setOf_pow_eq_finite`, `RS.ncard_setOf_pow_eq`, `RS.norm_lt_of_pow_eq`, `RS.exists_pow_eq`
  (planar, mathlib-only) — `Jacobian/MappingDegree/RootCounting.lean` (built).
- `RS.laurentCoeffAt`, `RS.taylorCoeffAt`, `RS.resAt`, `laurentCoeffAt_of_eventuallyEq`,
  `laurentCoeffAt_of_analyticAt`, `laurentCoeffAt_zpow_mul`, `MeromorphicAt.resAt_deriv_div` —
  `Jacobian/ResidueCalculus/*.lean` (design frozen; being finished — the exact file split is
  `TaylorCoeff/LaurentCoeff/PrincipalPart/Residue/ChangeOfVariables/IntegralBridge/
  GermFunctionals/MittagLeffler.lean` per `docs/design/residue-calculus.md`).

**Mathlib-only, freshly verified for this unit** (spike §9):

- `Complex.differentiableOn_update_limUnder_of_bddAbove {f:ℂ→E}{s}{c} (hc:s∈𝓝 c)
  (hd:DifferentiableOn ℂ f (s\{c})) (hb:BddAbove ((norm∘f)''(s\{c}))) :
  DifferentiableOn ℂ (Function.update f c (limUnder (𝓝[≠]c) f)) s`
  (`Analysis/Complex/RemovableSingularity.lean:101`) — Riemann's removable singularity theorem
  from a bare boundedness hypothesis on a punctured neighborhood. **This is the meromorphy-at-0
  engine for `traceZk`** — no monodromy, no convergent-Laurent-series machinery needed.
- `Complex.isPrimitiveRoot_exp (n) (h0:n≠0) : IsPrimitiveRoot (Complex.exp (2*π*I/n)) n`
  (`RingTheory/RootsOfUnity/Complex.lean:85`).
- `IsPrimitiveRoot.injOn_pow_mul {n}{ζ:M₀}(hζ)(hα:α≠0) : Set.InjOn (fun i => ζ^i * α)
  (Finset.range n)` (`RingTheory/RootsOfUnity/PrimitiveRoots.lean:326`) — pairwise-distinctness of
  the `k` translated roots of unity, **without any monodromy/branch-continuation argument**.
- `geom_sum_eq (h:x≠1)(n) : ∑ i∈range n, x^i = (x^n-1)/(x-1)` (`Algebra/Field/GeomSum.lean:43`) —
  the vanishing-sum-of-roots-of-unity-powers engine for the Laurent-coefficient formula.

**Gotcha found by the spike**: `π` inside `open scoped Real`/ambient namespaces can resolve to a
different notation than the one baked into `Complex.isPrimitiveRoot_exp`'s *stated* type (which
uses `↑Real.pi`); don't re-type the target type of `isPrimitiveRoot_exp`'s output by hand — bind
it with `have`/existential and let elaboration supply the exact term.

---

## 2. Core definitional decisions

### D1 — Standing setup

```lean
open scoped ContDiff Manifold Topology
open Filter Set Function
namespace RS.MTrace          -- new namespace to avoid clashing with RS.Mero (not yet landed)

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
```

"`f` meromorphic on `X`" is `RS.MeromorphicOnX f Set.univ` (CC3's frozen predicate, already
built); "nonconstant" is *not* stated as a property of `f` directly (there is no single clean
raw-function spelling — see D3) but of the *induced map* `toP1 f : X → OnePoint ℂ`, matching
mapping-degree's own hypothesis shape `¬ ∃ c, ∀ x, F x = c` verbatim so every mapping-degree
lemma applies with zero adaptation.

### D2 — `toP1`: the `f`-to-`ℙ¹` bridge, built locally (not blocked on upstream)

Both `meromorphic-and-divisors`'s future `ℳ.toP1` (recorded as a "deliverable-for-later" in
`docs/design/projective-line.md` §3.3) and `projective-line`'s `Holomorphy.lean` (which would
supply `contMDiffAt_of_pole`/`ContMDiffAt.onePointCoe`) are **not built yet**. Per the task's
explicit license, we build the bridge **here**, as a raw-function construction (no dependence on
the `ℳ X` quotient), using only `Charts.lean` (built) and local-multiplicity's *general* `X → Y`
holomorphy-in-chart bridge (also built, not `ℙ¹`-specific):

```lean
/-- The canonical `ℙ¹`-valued lift of a raw meromorphic function: `∞` at poles, the limiting
value along the punctured neighborhood elsewhere. Total (junk elsewhere for non-meromorphic
`f`); the honest content is `toP1_contMDiff`. -/
noncomputable def toP1 (f : X → ℂ) (x : X) : OnePoint ℂ :=
  if 0 ≤ ordAtX f x then ((limUnder (𝓝[≠] x) f : ℂ) : OnePoint ℂ) else ∞
```

Design rationale: `ordAtX f x ≥ 0 ↔ ∃ c, Tendsto f (𝓝[≠] x) (𝓝 c)` is *already* a built lemma
(`tendsto_nhds_iff_ordAtX_nonneg`, meromorphic-and-divisors, Predicates.lean) — `toP1` is exactly
the `if`-packaging of that dichotomy into an `OnePoint ℂ` value, mirroring meromorphic-and-
divisors's own planned `evalAt`/D5 design (same technique) but self-contained: we never touch
`MeroGermOn`/`OrderEval.lean`. If/when `OrderEval.lean` lands, `toP1` should be re-expressed as
`fun x => if 0 ≤ φ.ord x then ↑(φ.evalAt x) else ∞` for `φ : ℳ X` and this file becomes a thin
wrapper — noted in `docs/requests/meromorphic-and-divisors.md`.

The **holomorphy proof** (`toP1_contMDiff`, P1 below) is the one place we reconstruct, in
miniature, the "chart-local analytic repair" argument `projective-line`'s `Holomorphy.lean`
would have supplied generically; we only need it for *our* specific `toP1`, so it is cheap
(~50 lines, not a general-purpose transfer kit).

### D3 — Nonconstancy: `f`-side hypothesis and its translation

The natural `f`-side hypothesis, matching CC3's germ vocabulary exactly:

```lean
/-- The natural raw-function nonconstancy hypothesis: `f` is not codiscretely equal to any
single constant. (This is what `proper-map-degree`/callers will have in hand from `ℳ X`
nonzero-ness once that unit lands; stated here germ-level so we do not need `ℳ X` to exist.) -/
def NotEventuallyConstX (f : X → ℂ) : Prop := ∀ c : ℂ, ¬ (fun x => f x - c) =ᶠ[codiscrete X] 0
```

```lean
/-- The translation: an everywhere-meromorphic `f` on connected `X` that is not codiscretely a
constant induces a nonconstant `toP1 f`. Both degenerate cases (`toP1 f ≡ ↑c` and `toP1 f ≡ ∞`)
are ruled out by the SAME argument applied to `f - c` (`c = 0` covers `∞`, via `f⁻¹`). -/
theorem toP1_not_const (hf : MeromorphicOnX f Set.univ) (hnc : NotEventuallyConstX f) :
    ¬ ∃ c, ∀ x, toP1 f x = c
```

Proof plan (P-lite; ~25 lines, see §5.3): if `toP1 f ≡ ↑c` then `ordAtX (f - c) x ≥ 1` (in fact
`> 0`) for *every* `x` (not just a.e.) — this is the crucial extra strength over the usual
identity-theorem argument: the hypothesis holds at *every nearby point too*, so the analytic
repair of `f - c` near any `x₀` is *pointwise* `0` on a full (not punctured) neighborhood of
`x₀`, giving `(f-c) =ᶠ[𝓝[≠]x₀] 0` directly (no separate use of
`MeromorphicOnX.eventuallyEq_zero_or_forall_ordAtX_ne_top` needed — the hypothesis is already
strong enough pointwise), hence (D2-bridge) `(f-c)=ᶠ[codiscrete X]0`, contradicting `hnc c`. The
`toP1 f ≡ ∞` case reduces to the `c=0` case applied to `f⁻¹` (`ordAtX_inv` is unconditional, so
`ordAtX f x < 0 ↔ ordAtX f⁻¹ x > 0` for every `x`, and `f⁻¹ ≡ᶠ 0 ↔ f ≡ᶠ 0` since `(·)⁻¹` fixes
`0` and is injective off `0` in `ℂ`).

**Risk flag**: if the "pointwise-at-every-nearby-point" argument above proves fiddlier in Lean
than this sketch suggests, the fallback is to *not* prove `toP1_not_const` at all and instead
state the argument-principle theorem (§2.4) with `hFne : ¬∃c,∀x,toP1 f x=c` **as a hypothesis**,
pushed to the caller. `proper-map-degree` will have an easy nonconstancy witness once `ℳ X` is a
field (any nonzero, non-unit class), so this costs nothing downstream even if `toP1_not_const`
is dropped.

### D4 — The order↔multiplicity bridge (the real content of cluster 1)

For `F := toP1 f`, `hF := toP1_contMDiff hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F`:

```lean
/-- Zero case: chart at `↑0` is `coeChart` (identity), so the CC4 multiplicity of `F` at a
zero of `f` IS the vanishing order. -/
theorem multiplicity_toP1_of_ordAtX_pos (hf : MeromorphicOnX f Set.univ) {x : X}
    (hx : 0 < ordAtX f x) :
    (multiplicity (toP1 f) x : ℤ) = (ordAtX f x).untop₀

/-- Pole case: chart at `∞` is `invChart` (`z ↦ z⁻¹`), so the CC4 multiplicity of `F` at a pole
of `f` IS the order of the POLE (positive). -/
theorem multiplicity_toP1_of_ordAtX_neg (hf : MeromorphicOnX f Set.univ) {x : X}
    (hx : ordAtX f x < 0) :
    (multiplicity (toP1 f) x : ℤ) = -(ordAtX f x).untop₀
```

These are the "order-vs-multiplicity bridge lemmas" the task asks to be nailed exactly; proof
plan in §5.2.

### D5 — The argument principle

```lean
/-- THE argument principle: the (finite, junk-`0`-off-support) sum of orders of a meromorphic,
nonconstant function on a compact connected surface is `0`. Consumed by `proper-map-degree` for
`deg(div f) = 0` (repackaging into `Divisor`/`Divisor.degree` terms is THEIR bookkeeping). -/
theorem finsum_ordAtX_eq_zero (hf : MeromorphicOnX f Set.univ)
    (hne : ¬ ∃ c, ∀ x, toP1 f x = c) :
    ∑ᶠ x, (ordAtX f x).untop₀ = 0

/-- Finset form (matches `Divisor.degree`'s `Finset.sum`-over-`finiteSupport` shape). -/
theorem sum_ordAtX_eq_zero_of_finite {s : Finset X}
    (hf : MeromorphicOnX f Set.univ) (hne : ¬ ∃ c, ∀ x, toP1 f x = c)
    (hs : ∀ x, ordAtX f x ≠ 0 → x ∈ s) :
    ∑ x ∈ s, (ordAtX f x).untop₀ = 0
```

(`sum_ordAtX_eq_zero_of_finite` is a trivial corollary padding the finsum to any Finset containing
the support, e.g. `proper-map-degree`'s own `divisor f`'s support Finset — zero extra terms.)

### D6 — `traceZk`: the planar atom (route decision)

```lean
/-- The trace of `h` along `z ↦ z ^ k` at `w`: the sum of `h` over the (generically `k`-element)
root set. Junk-free by convention: at `w = 0` the root set is the singleton `{0}` (for `k ≠ 0`),
giving whatever `h 0` evaluates to (a harmless junk value — see §6); at `w` with `k = 0` the
support is either empty or all of `ℂ`, and `finsum` junks to `0` in the latter case. -/
noncomputable def traceZk (h : ℂ → ℂ) (k : ℕ) (w : ℂ) : ℂ :=
  ∑ᶠ z ∈ {z : ℂ | z ^ k = w}, h z
```

**Route decision** (task's explicit ask): direct root-set-sum definition, local analytic branches
**only** for the "analytic away from `0`" step, and a **norm/zpow growth bound + Riemann's
removable-singularity theorem** for the "meromorphic at `0`" step — **no monodromy, no symmetric-
function/Newton's-identity machinery, no convergent-global-Laurent-series argument.** Justification:

- Monodromy is avoided because `traceZk` is defined via the abstract root *set* (a `finsum`), not
  via a chosen branch/slit-domain formula; local branches (built via `AnalyticAt.exists_pow_eq`,
  §5.4) are only ever used to *witness* analyticity at a fixed point, never to assemble a global
  formula that would need patching across branch cuts.
- Newton's identities / elementary symmetric functions (Forster Thm 8.2's classical route) would
  require a polynomial/symmetric-function API tracking a *continuously varying* factorization
  `∏(T - z_i(w))` — heavier machinery than needed, and mathlib has no ready-made "symmetric
  functions of a varying finite root set" API at the pin. The growth-bound route needs only
  `MeromorphicAt`'s bare existential definition, one mathlib removable-singularity lemma, and
  elementary norm arithmetic on roots of unity.
- The growth-bound route sidesteps "does `h`'s Laurent series converge and can I substitute it
  termwise" worries for the *existence* of meromorphy; that finer question (needed only for the
  *coefficient formula*, not existence) is handled separately in §5.6 using mathlib's *honest*
  convergent power series for the *analytic unit factor* of `h` (never for `h` itself, which may
  have a pole) — a rigor-preserving move which the pure-`taylorCoeffAt`-algebra route of
  residue-calculus does not need to make (it works with `dslope`-extracted formal coefficients
  precisely to avoid asserting convergence for the not-necessarily-analytic `h`; we only assert
  convergence for the honestly-analytic unit factor `u`).

### D7 — `Tr_F h`: global assembly via `FiberStack` (uniform, no branch/regular case split)

```lean
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- The fibre trace of `h` along `F`, evaluated via an arbitrary chosen `FiberStack` at each
point (well-definedness against the choice: `Tr_F_eq_of_fiberStack`, §5.7). Junk `0` for
constant `F` (`FiberStack.n = 0` is NOT forced there — see §6 junk ledger; the honest guard is
`Tr_F_of_forall_eq`). -/
noncomputable def trace (F : X → Y) (h : X → ℂ) (y₀ : Y) : ℂ :=
  have S := (Classical.arbitrary (PLift (Nonempty (FiberStack F y₀)))).down.down
  ∑ i, traceZk (h ∘ (S.A i).e.symm) (multiplicity F (S.pt i)) ((S.A i).e' y₀)
```

(Exact `Classical.choice`/`Nonempty.some` plumbing to be settled by the builder — the design
content is the *formula*, not the choice mechanism; see §5.7 for the precise recipe and the
well-definedness proof obligation.)

---

## 3. File plan

| # | File | Content | Est. | Imports beyond stdlib/mathlib |
|---|------|---------|------|-------------------------------|
| 1 | `MeromorphicTrace/ToP1.lean` | `toP1`, `toP1_contMDiff` (P1), `toP1_not_const` (D3) | ~230 | `Jacobian.Meromorphic.{Predicates,CodiscreteBridge}`, `Jacobian.ProjectiveLine.Charts`, `Jacobian.LocalMultiplicity.ChartBridge` |
| 2 | `MeromorphicTrace/OrderMultiplicity.lean` | `multiplicity_toP1_of_ordAtX_pos/neg` (P2) | ~150 | file 1, `Jacobian.LocalMultiplicity.Multiplicity` |
| 3 | `MeromorphicTrace/ArgumentPrinciple.lean` | `finsum_ordAtX_eq_zero`, Finset corollary (P3) | ~150 | files 1–2, `Jacobian.MappingDegree.Degree` |
| 4 | `MeromorphicTrace/PlanarTrace.lean` | `traceZk`: linearity, pullback, analyticity off `0` (P4), meromorphy at `0` (P5, the hardest), Laurent-coefficient formula (P6) | ~420 | `Jacobian.MappingDegree.RootCounting`, `Jacobian.LocalMultiplicity.KthRoot`, `Jacobian.ResidueCalculus.{LaurentCoeff,Residue}`, mathlib `RootsOfUnity`/`RemovableSingularity`/`GeomSum` |
| 5 | `MeromorphicTrace/FunctionTrace.lean` | `trace` (`Tr_F h`), well-definedness (P7), meromorphy on `Y`, junk for constant `F` | ~260 | files 1–2, 4, `Jacobian.MappingDegree.LocalStructure` |
| 6 | `Jacobian/MeromorphicTrace.lean` | unit root, API docstring | ~30 | all |

Build waves: **file 4 (`PlanarTrace`) is fully independent of files 1–3** (pure planar content,
mathlib + mapping-degree's `RootCounting` + local-multiplicity's `KthRoot` + residue-calculus) —
build it in parallel with the `ToP1`→`OrderMultiplicity`→`ArgumentPrinciple` chain. File 5 needs
both chains (1–2 for the chart-local trace pieces, 4 for `traceZk`).

---

## 4. Exports (exact signatures)

Everything in `namespace RS.MTrace` unless noted. `f g : X → ℂ`, `h : ℂ → ℂ`, `x : X`, `k : ℕ`,
`w z : ℂ`.

### 4.1 `ToP1.lean`

```lean
noncomputable def toP1 (f : X → ℂ) (x : X) : OnePoint ℂ                      -- D2

theorem toP1_eq_infty_iff {x} : toP1 f x = ∞ ↔ ordAtX f x < 0
theorem toP1_eq_coe_iff {x} {c : ℂ} :
    toP1 f x = (c : OnePoint ℂ) ↔ 0 ≤ ordAtX f x ∧ limUnder (𝓝[≠] x) f = c

theorem toP1_contMDiff (hf : MeromorphicOnX f Set.univ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (toP1 f)                                          -- P1

def NotEventuallyConstX (f : X → ℂ) : Prop :=
    ∀ c : ℂ, ¬ (fun x => f x - c) =ᶠ[codiscrete X] 0

theorem toP1_not_const (hf : MeromorphicOnX f Set.univ) (hnc : NotEventuallyConstX f) :
    ¬ ∃ c, ∀ x, toP1 f x = c                                                 -- D3
```

### 4.2 `OrderMultiplicity.lean`

```lean
theorem multiplicity_toP1_of_ordAtX_pos (hf : MeromorphicOnX f Set.univ) {x} (hx : 0 < ordAtX f x) :
    (multiplicity (toP1 f) x : ℤ) = (ordAtX f x).untop₀
theorem multiplicity_toP1_of_ordAtX_neg (hf : MeromorphicOnX f Set.univ) {x} (hx : ordAtX f x < 0) :
    (multiplicity (toP1 f) x : ℤ) = -(ordAtX f x).untop₀

/-- Regular points (`ordAtX f x = 0`) are unramified — a cheap corollary, useful glue for
`form-trace-tower`'s branch/regular case analysis even though we do not need it ourselves. -/
theorem multiplicity_toP1_of_ordAtX_eq_zero (hf : MeromorphicOnX f Set.univ) {x}
    (hx : ordAtX f x = 0) : multiplicity (toP1 f) x = 1
```

### 4.3 `ArgumentPrinciple.lean`

```lean
theorem finsum_ordAtX_eq_zero (hf : MeromorphicOnX f Set.univ)
    (hne : ¬ ∃ c, ∀ x, toP1 f x = c) : ∑ᶠ x, (ordAtX f x).untop₀ = 0
theorem sum_ordAtX_eq_zero_of_finite {s : Finset X} (hf : MeromorphicOnX f Set.univ)
    (hne : ¬ ∃ c, ∀ x, toP1 f x = c) (hs : ∀ x, ordAtX f x ≠ 0 → x ∈ s) :
    ∑ x ∈ s, (ordAtX f x).untop₀ = 0

/-- Convenience packaging for callers holding the raw `f`-side nonconstancy hypothesis instead
of `toP1`'s. -/
theorem finsum_ordAtX_eq_zero' (hf : MeromorphicOnX f Set.univ) (hnc : NotEventuallyConstX f) :
    ∑ᶠ x, (ordAtX f x).untop₀ = 0
```

### 4.4 `PlanarTrace.lean` (mathlib + planar project imports only; no manifold content)

```lean
noncomputable def traceZk (h : ℂ → ℂ) (k : ℕ) (w : ℂ) : ℂ                     -- D6

-- Junk/basic API
theorem traceZk_apply_of_ne_zero (hk : k ≠ 0) (hw : w ≠ 0) :
    traceZk h k w = ∑ z ∈ (setOf_pow_eq_finite hk w).toFinset, h z
theorem traceZk_zero_apply (hk : k ≠ 0) : traceZk h k 0 = h 0             -- honest but junk, §6

-- Linearity
theorem traceZk_add (k : ℕ) : traceZk (f + g) k = traceZk f k + traceZk g k    -- pointwise on ℂ→ℂ
theorem traceZk_const_mul (c : ℂ) (k : ℕ) :
    traceZk (fun z => c * h z) k = fun w => c * traceZk h k w

-- Trace of a pullback (branch-point caveat: only away from `0`, see §6)
theorem traceZk_comp_pow (g : ℂ → ℂ) (hk : k ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    traceZk (fun z => g (z ^ k)) k w = k * g w

-- Analyticity away from the branch point (P4)
theorem analyticAt_traceZk (hh : ∀ᶠ z in 𝓝[≠] (0:ℂ), AnalyticAt ℂ h z) (hk : k ≠ 0)
    {w₀ : ℂ} (hw₀ : w₀ ≠ 0) (hsmall : "w₀ within h's domain of analyticity, radius-tracked") :
    AnalyticAt ℂ (traceZk h k) w₀

-- Meromorphy at the branch point (P5, the hardest)
theorem meromorphicAt_traceZk (hh : MeromorphicAt h 0) (hk : k ≠ 0) :
    MeromorphicAt (traceZk h k) 0

-- The Laurent-coefficient formula (P6; what `form-trace-tower` lifts)
theorem laurentCoeffAt_traceZk (hh : MeromorphicAt h 0) (hk : k ≠ 0) (m : ℤ) :
    laurentCoeffAt (traceZk h k) 0 m = (k : ℂ) * laurentCoeffAt h 0 (k * m)

-- Immediate corollaries (bank for form-trace-tower / residue bookkeeping)
theorem resAt_traceZk (hh : MeromorphicAt h 0) (hk : k ≠ 0) :
    resAt (traceZk h k) 0 = (k : ℂ) * laurentCoeffAt h 0 (-(k:ℤ))
theorem ordAt_traceZk_ge (hh : MeromorphicAt h 0) (hk : k ≠ 0) :
    (k : WithTop ℤ) * (meromorphicOrderAt h 0) ≤ (k:ℤ) • meromorphicOrderAt (traceZk h k) 0
    -- (order bound; exact equality does not hold in general — a coefficient CAN cancel; see §6)
```

(`analyticAt_traceZk`'s exact side-condition on `w₀`/radius will be pinned during implementation
to the natural "`h` analytic on `ball 0 r \ {0}`, `w₀` with all its `k`-th roots inside that ball"
shape mirroring mapping-degree's `RootCounting.norm_lt_of_pow_eq`; kept informal here since it is
routine bookkeeping, not designed content.)

### 4.5 `FunctionTrace.lean`

```lean
noncomputable def trace (F : X → Y) (h : X → ℂ) (y₀ : Y) : ℂ                   -- D7

theorem trace_well_defined (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hne : ¬∃c,∀x,F x=c)
    {S S' : FiberStack F y₀} : trace F h y₀ = "the S-formula" = "the S'-formula"
    -- (stated as the two formulas being equal; `trace`'s def picks ONE via Classical.choice,
    -- this lemma is what makes any OTHER FiberStack-based computation legitimate)

theorem meromorphicAtX_trace (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hne : ¬∃c,∀x,F x=c)
    (hh : MeromorphicOnX h Set.univ) (y₀ : Y) : MeromorphicAtX (trace F h) y₀

theorem trace_of_forall_eq (c : Y) : trace (fun _ : X => c) h = fun _ => 0
  -- junk convention: constant `F` gives `n = 0` fibers in a degenerate `FiberStack`; guard stated
  -- explicitly, not left to accidental unfolding — see §6

theorem trace_of_regular (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hne : ¬∃c,∀x,F x=c)
    {y₀ : Y} (hy₀ : IsRegularValue F y₀) :
    trace F h y₀ = ∑ᶠ x ∈ F ⁻¹' {y₀}, h x
  -- sanity check: at a regular value, `trace` reduces to the naive "sum over sheets" formula
  -- (multiplicity 1 everywhere ⇒ `traceZk _ 1 = id`)
```

---

## 5. Proof plans for the hardest theorems

### P1. `toP1_contMDiff` (ToP1.lean)

Fix `x : X`, `e := chartAt ℂ x`, `c := e x`. By
`LMCompat.contMDiffAt_iff_analyticAt_inChartAt` it suffices: `ContinuousAt (toP1 f) x` and
`AnalyticAt ℂ (inChartAt (toP1 f) x) c`.

**Case `0 ≤ ordAtX f x` (`toP1 f x = ↑(limUnder ... f)`, write `v := limUnder (𝓝[≠]x) f`).**
Chart at `↑v` is `coeChart` (`chartAt_coe`); need `AnalyticAt ℂ (coeChart ∘ (toP1 f) ∘ e.symm - v) c`
(after the recentering unfold). From `ordAtX f x ≥ 0` and `meromorphicOrderAt_eq_int_iff`
(via `ordAtX_def`/chart transport), obtain the analytic repair
`g : ℂ → ℂ`, `AnalyticAt ℂ g c`, with `f ∘ e.symm =ᶠ[𝓝[≠]c] g` (`n ≥ 0` case, `g` IS the whole
presentation, no extra `(·-c)^n` factor needed beyond folding it into `g`). Two facts:
1. `Tendsto (f∘e.symm) (𝓝[≠]c) (𝓝 (g c))` (continuity of `g` + the eventual equality); transport
   through `e` (`tendsto_nhdsNE_comp_chart_iff`, Predicates.lean) to get
   `Tendsto f (𝓝[≠]x) (𝓝 (g c))`; uniqueness of limits (`T2Space ℂ`) gives `v = g c`.
2. On the same punctured neighborhood, for `y` near `x` (`y ≠ x`), does `toP1 f y = ↑(g (e y))`?
   Need `0 ≤ ordAtX f y` too — true eventually on `𝓝[≠]x`
   (`eventually_ordAtX_eq_zero`-flavored propagation, or directly: `g` analytic near `c` ⇒
   `f ∘ e.symm` analytic near every nearby point off `c` (since `f∘e.symm = g` pointwise on the
   punctured set) ⇒ `ordAtX f y ≥ 0` there by chart invariance + `AnalyticAt.meromorphicOrderAt_eq`)
   and `limUnder(𝓝[≠]y) f = g (e y)` (same uniqueness-of-limit argument at `y` instead of `x`,
   using that `f ∘ e.symm = g` pointwise near `e y` too, so `f` itself tends to `g(e y)` along
   `𝓝[≠]y` after transporting back through `e`).
   Hence `toP1 f =ᶠ[𝓝[≠]x] (fun y => ↑(g (e y)))`, and at `x` itself both sides are `↑v = ↑(g c)`.
   So `toP1 f =ᶠ[𝓝 x] (fun y => ↑(g (e y)))` (full, not punctured, neighborhood).
3. `ContinuousAt (toP1 f) x`: RHS is continuous (`g` analytic ⇒ continuous, `e` continuous,
   `(↑) : ℂ → OnePoint ℂ` continuous — `continuous_coe`), congr along the `=ᶠ[𝓝 x]` fact.
4. `AnalyticAt ℂ (inChartAt (toP1 f) x) c`: `inChartAt (toP1 f) x` recentered equals
   `coeChart ∘ (toP1 f) ∘ e.symm - v`; on `e.target` this is `g - g c` (from the `=ᶠ[𝓝 x]`
   fact of step 2 transported through `e` and `coeChart_apply_coe`), analytic (`g` analytic,
   subtract constant).

**Case `ordAtX f x < 0` (`toP1 f x = ∞`).** Chart at `∞` is `invChart` (`chartAt_infty`). Need
`AnalyticAt ℂ (invChart ∘ (toP1 f) ∘ e.symm) c` (recentering is by `0`, `invChart ∞ = 0`, no-op).
Order presentation: `f ∘ e.symm =ᶠ[𝓝[≠]c] fun z => (z-c)^n • u z` with `n < 0`, `u` analytic,
`u c ≠ 0` (`meromorphicOrderAt_eq_int_iff`). On a small punctured neighborhood of `c`,
`f∘e.symm ≠ 0` (continuity of `u`, `(z-c)^n≠0` off `c`), so (by the SAME propagation argument as
the zero case, using `ordAtX_inv` unconditional) `ordAtX f y < 0` for `y` near (but `≠`) `x`, i.e.
`toP1 f y = ∞` too, i.e. `toP1 f y ≠ ↑c'` for any finite `c'` — in particular `toP1 f =ᶠ[𝓝[≠]x]
(fun y => (↑(f y) : OnePoint ℂ))`? **No** — need care: for `y` near `x` with `ordAtX f y < 0`,
`toP1 f y = ∞` by the `if`-branch, matching `((f y)⁻¹ ...)`-style only through `invChart`, not
through `↑f y` (which isn't even meaningful — `toP1` sends poles to `∞`, not to `↑(f y)`). The
correct eventual identity is `invChart ∘ (toP1 f) ∘ e.symm =ᶠ[𝓝[≠]c] (f∘e.symm)⁻¹` (both sides:
LHS is `invChart ∞ = 0`... no — at points `z ≠ c` near `c`, `toP1 f (e.symm z) = ∞` (just
established), so LHS `= invChart ∞ = 0`?? That can't be right either — rethink: `invChart ∞ = 0`
is a CONSTANT, but `(f∘e.symm)⁻¹` is not eventually constant. **Resolution**: the map `toP1 f`
does NOT send an entire punctured neighborhood of a pole to `∞` — only `x` itself (and possibly
finitely many other genuine poles nearby, which are isolated). Generic nearby points have
`ordAtX f y = 0` (regular, `f y` finite nonzero) or occasionally other honest values. So redo:
on `𝓝[≠]x` MINUS the (isolated, possibly present) other poles, `toP1 f y = ↑(f y)` (either `f y`
itself is already the honest value with `ord = 0`, giving `limUnder = f y` trivially since `f` is
literally continuous with that value there by `ContMDiffAt.ordAtX_nonneg`-flavored reasoning — OR
more simply: for such `y`, `ordAtX f y ≥ 0` (order `0` or positive, generic case) and one checks
`limUnder(𝓝[≠]y) f` equals the analytic-continuation value, which — since `f` is meromorphic and
`y` is not itself a pole/zero-degenerate point — equals the CHART value coming from the *same*
presentation `u`/`(z-c)^n` (just now with `n<0` factored differently). The clean way to avoid
this case explosion: use the presentation directly. For `z ≠ c` near `c` (`u z ≠ 0`,
`(z-c)^n ≠ 0`), `f(e.symm z) = (z-c)^n \cdot u z ≠ 0`, and (by `ordAtX_inv`,`ordAtX_mul`
unconditional-chart-arithmetic) `ordAtX (f⁻¹) (e.symm z)` — **avoid recursion on `toP1`
altogether**: prove instead, DIRECTLY, that
`invChart ∘ (toP1 f) ∘ e.symm =ᶠ[𝓝[≠]c] (fun z => (z-c)^(-n) \cdot (u z)⁻¹)` by case-splitting
the RHS's definition of `toP1 f (e.symm z)` pointwise for `z` in the eventual set where `u z ≠0`:
either `toP1 f (e.symm z) = ↑(f(e.symm z))` (if `ordAtX f (e.symm z) ≥ 0`, impossible here since
`f(e.symm z) = (z-c)^n u z` has "chart-order" exactly `n<0` there by the SAME presentation read
at `z` — i.e. `ordAtX f (e.symm z) = n < 0` too, by chart-invariance + `meromorphicOrderAt`'s
OWN local constancy of the presentation (the presentation `(z-c)^n u z` witnesses order `n` at
EVERY `z` with `u z ≠ 0`, not just at `c` — standard, `AnalyticAt.meromorphicOrderAt_eq` applied
pointwise)) so ACTUALLY `toP1 f (e.symm z) = ∞` for EVERY such `z`, not just at `c`! This
resolves the apparent contradiction above: **on the whole punctured neighborhood (where `u≠0`),
`f` has a pole, not just at `x`** — because the presentation `(z-c)^n u(z)` has vanishing order
EXACTLY `n` (not `≥ n`) at every nearby point too (`u` nonvanishing there). So indeed
`toP1 f =ᶠ[𝓝[≠]x] (fun y => ∞)`... but combined with `toP1 f x = ∞` too, this gives
`toP1 f =ᶠ[𝓝 x] (fun _ => ∞)` (CONSTANT `∞` near `x`!). That trivializes the whole case: `toP1 f`
is LOCALLY CONSTANT `∞` near any pole (matches the intuition that within one adapted-chart's
validity radius, if `f`'s LEADING presentation has `n<0` and unit factor nonvanishing on the
WHOLE chart ball, `f` has no OTHER poles/zeros nearby to begin with only if the ORDER is read at
the SAME point `c` for every `z` — wait, I conflated "order of `f` at `x`" (`n`, fixed) with
"order of `f` at a DIFFERENT point `e.symm z`" (which is a DIFFERENT local invariant, generally
`0`, NOT `n`, for `z ≠ c`! The presentation `f(e.symm z) = (z-c)^n u(z)` gives the VALUE of `f`
at `e.symm z`, not its ORDER there — order of `f` AT THE POINT `e.symm z` (as `z` ranges) is
about the behavior of `f` NEAR `e.symm z`, a different local question entirely, not read off
this single global formula's `z`-exponent. **This is the bug in the paragraph above — scrap it.**
The correct statement is only about the VALUE `f(e.symm z) = (z-c)^n u(z)`, which for `z≠c` is a
literal nonzero complex number, i.e. `f(e.symm z)` is just some specific finite value — `toP1`
at `e.symm z` is `↑(f(e.symm z))` PROVIDED `ordAtX f (e.symm z) ≥ 0` (a fact about the germ AT
`e.symm z`, generically true for `z` in the presentation's domain since `f` restricted there is
literally `(the analytic function z ↦ (z-c)^n u(z))`, ANALYTIC at every such `z≠c` (as `u`
analytic, `(z-c)^n` analytic off `c`) — hence `ordAtX f (e.symm z) = 0` (order of an analytic
NONVANISHING germ) for generic `z` in the domain, UNLESS `(z-c)^n u(z) = 0`, impossible since
`u(z)≠0` there and `z≠c`. **So `ordAtX f (e.symm z) = 0` (not `<0`!) for EVERY `z≠c` in the
presentation's validity domain** — i.e., poles ARE isolated exactly as expected, and `toP1 f`
literally equals `↑(f∘e.symm)` `= ↑((z-c)^n u(z))` on the whole punctured chart neighborhood.
*This* is the correct fact (matching intuition; the confusion above was resolved by correctly
separating "order at `x`" from "order at nearby points", which are different by design). With
this fixed: `invChart ∘ (toP1 f) ∘ e.symm =ᶠ[𝓝[≠]c] (fun z => ((z-c)^n u(z))⁻¹)`
(`invChart_apply_coe`, unconditional) `= (z-c)^{-n} \cdot (u z)⁻¹` (`n<0` so `-n>0`, honest
NATURAL power `(-n).toNat`, analytic; `u`'s inverse analytic since `u(c)≠0` ⇒ `u≠0` near `c` by
continuity). At `z=c`: `invChart(toP1 f x) = invChart ∞ = 0`, matching `(c-c)^{-n}\cdot(u c)^{-1}
= 0` (since `-n>0`). So the eventual equality extends to `𝓝 c` (full neighborhood, both sides
literally `0` at `c`, `AnalyticAt.congr`-ready), giving `AnalyticAt` of the composite directly
(product of `(·-c)^{(-n).toNat}` — entire — with `u⁻¹` — analytic near `c`, `u c≠0`).
`ContinuousAt` similarly from the same full-neighborhood equality.

Est. 90–130 lines total (both cases); the case split on sign of `ordAtX f x` is the only branch.
**Lesson embedded in the plan above for the builder**: do NOT conflate "order of `f` at `x`" with
"value of the chosen presentation function at a nearby chart-point `z`" — keep every step
pointwise-value or pointwise-order, never mix, and re-derive "`ordAtX f y = 0` for `y` near a
zero/pole `x`" from the PRESENTATION's nonvanishing unit factor, not by an appeal to some
different global fact.

### P2. `multiplicity_toP1_of_ordAtX_pos` / `_neg` (OrderMultiplicity.lean)

**Zero case.** `F := toP1 f`, `F x = ↑0` (`toP1_eq_coe_iff`, since `ordAtX f x > 0 ⟹ 0≤ordAtX f x`
and the limit is `0` — order `>0` means the repair's value AT `x` is `0`, i.e. `v = g c = 0` in
P1's notation, a one-line fact from `meromorphicOrderAt_eq_int_iff`'s `n>0` case: the
presentation is `(z-c)^n u(z)` with `n ≥1`, so its value AT `c` — which IS `limUnder`, by
uniqueness of limits as in P1 — is `0`). `chartAt ℂ (F x) = coeChart` (`chartAt_coe`).
`multiplicityENat F x = analyticOrderAt (inChartAt F x) (chartAt ℂ x x)` (`multiplicityENat_def`).
From P1's step-2 fact, `inChartAt F x =ᶠ[𝓝 c] g - g c = g` (since `g c = 0`, using P1's `g`,
the SAME analytic repair). So `analyticOrderAt (inChartAt F x) c = analyticOrderAt g c`
(`analyticOrderAt_congr`). Now `g`'s presentation IS the order presentation of `f∘e.symm` at `c`
with the SAME `n = ordAtX f x` (both `MeromorphicOrderAt` and `AnalyticAt`'s order agree via
`AnalyticAt.meromorphicOrderAt_eq`/`analyticOrderAt_eq_natCast`, since `n ≥ 0` is exactly the
"already analytic" regime, no cast subtlety), giving `analyticOrderAt g c = n.toNat` (as `ℕ∞`,
matching `(ordAtX f x).untop₀.toNat`). `multiplicity F x = (analyticOrderAt(inChartAt F x)c).toNat
= n.toNat = (ordAtX f x).untop₀.toNat`; cast to `ℤ` via `ENat.coe_toNat`/`WithTop.untop₀`
compatibility (`n ≥ 0` avoids the sign subtlety entirely) gives the stated identity.

**Pole case.** `F x = ∞`, `chartAt ℂ (F x) = invChart`. From P1's pole-case computation,
`inChartAt F x =ᶠ[𝓝 c] (fun z => ((z-c)^n u(z))⁻¹)` (`n<0`); rewrite via
`meromorphicOrderAt_inv`-flavored planar identity: the function `((z-c)^n u(z))⁻¹` has
`analyticOrderAt` at `c` equal to `-n` (a positive integer): from
`analyticOrderAt ((·-c)^n \cdot u) c = n` (negative — wait `analyticOrderAt` is `ℕ∞`-valued,
can't be negative; the RIGHT statement is at the `meromorphicOrderAt`-level: `meromorphicOrderAt
(f∘e.symm) c = n` (possibly negative, `WithTop ℤ`), and `meromorphicOrderAt ((f∘e.symm)⁻¹) c =
-n` (`meromorphicOrderAt_inv`, unconditional) `= (-n : ℕ)` since `-n > 0` now, i.e. `(f∘e.symm)⁻¹`
is ANALYTIC with a genuine natural-number vanishing order `-n`, and `AnalyticAt.meromorphicOrderAt_eq`
bridges this to `analyticOrderAt` directly: `analyticOrderAt ((f∘e.symm)⁻¹) c = (-n).toNat` (as
`ℕ∞`). Combined with `inChartAt F x =ᶠ[𝓝 c] (f∘e.symm)⁻¹` (P1's fact, `invChart_apply_coe`
unconditional avoids any `z=c`-vs-`z≠c` case split): `analyticOrderAt (inChartAt F x) c =
(-n).toNat`, so `multiplicity F x = (-n).toNat = (-(ordAtX f x)).untop₀.toNat`, matching (cast to
`ℤ`, using `n<0` to control the sign of `untop₀`/`toNat` interplay via `omega` on the `Int`/`Nat`
casts).

Est. 60–90 lines each (careful but mechanical `WithTop ℤ`/`ℕ∞`/`ℤ`/`ℕ` cast bookkeeping —
`omega`-closeable once the order identities are in `have`s). The delicate part is exactly the one
the task calls out: correctly bridging `meromorphicOrderAt`(signed, `f`) ↔ `analyticOrderAt`
(unsigned, CC4's `multiplicityENat`) THROUGH the `invChart` composition, using
`meromorphicOrderAt_inv`'s **unconditional** sign flip as the hinge.

### P3. `finsum_ordAtX_eq_zero` (ArgumentPrinciple.lean)

`F := toP1 f`, `hF := toP1_contMDiff hf`. By `fiberMultSum_eq_degree hF hne`,
`fiberMultSum F ↑0 = degree F = fiberMultSum F ∞`. Unfold via `fiberMultSum_eq_finset_sum`
(mapping-degree, using `fiber_finite hF hne` at both `↑0` and `∞`):
`∑ x ∈ (fiber_finite hF hne ↑0).toFinset, multiplicity F x
  = ∑ x ∈ (fiber_finite hF hne ∞).toFinset, multiplicity F x`.
Rewrite each `multiplicity F x` termwise via P2 (`multiplicity_toP1_of_ordAtX_pos` on the LHS
Finset — every `x` there has `F x = ↑0`, hence, by `toP1_eq_coe_iff`/junk-elsewhere,
`ordAtX f x > 0` PROVIDED `ordAtX f x ≠ ⊤`... need the finset membership to translate to
`0 < ordAtX f x` exactly, not just `≥0` — this needs a small lemma `toP1_eq_zero_iff_ordAtX_pos`
(a one-line corollary of `toP1_eq_coe_iff` plus "the analytic-repair value is `0` iff order `>0`",
itself from `meromorphicOrderAt_eq_int_iff`'s unit-factor nonvanishing at the order value; ~10
lines) and similarly `_neg` on the RHS. Get: `∑_{x: ord f x >0} (ord f x).untop₀
= ∑_{x: ord f x <0} (-(ord f x)).untop₀` as integers (cast the ℕ equality). Rewrite RHS as
`-∑_{x:ord<0}(ord f x).untop₀` (`Finset.sum_neg_distrib` / pull the negation through) and move to
one side: `∑_{x:ord>0} ord + ∑_{x:ord<0} ord = 0`. The full finsum
`∑ᶠ x, (ordAtX f x).untop₀` has support exactly `{x | ordAtX f x ≠ 0}` (junk `.untop₀` of `0` is
`0`, and — crucially — `ordAtX f x ≠ ⊤` for EVERY `x`, else `.untop₀` of `⊤` would ALSO be junk
`0`, silently but CORRECTLY dropping `⊤`-points from the sum; we do not even need to separately
rule out `⊤`, since `.untop₀` already sends it to the same junk `0` as the "not in support" case
— though for the two Finsets above to literally partition the full support we do want
`ordAtX f x ≠ ⊤` everywhere, which follows from `hne` via `toP1_not_const`'s contrapositive
reasoning OR is simply not needed: any `⊤`-order point contributes `0` to the finsum trivially
and is invisible to BOTH the "zero fiber" and "pole fiber" finsets, so the equation
`∑_{>0} + ∑_{<0} = 0` established above IS ALREADY the full finsum, with `⊤`-points contributing
`0` on both sides of the accounting for free). Assemble via `finsum_mem_finset`/
`finsum_eq_sum_of_finite_support`-style rewriting of `∑ᶠ x, (ordAtX f x).untop₀` into the disjoint
union of the "`>0`" and "`<0`" Finsets (support ⊆ their union, terms `0` outside).

Est. 90–120 lines. Main fiddliness: assembling the "support of the finsum ⊆ zero-Finset ∪
pole-Finset" fact and the sign bookkeeping casting `ℕ` equalities to the `ℤ`/`WithTop ℤ` mix
(`omega` after enough `have`s).

### P4. `analyticAt_traceZk` (PlanarTrace.lean, off the branch point)

Fix `w₀ ≠ 0`, radius `r>0` with `h` analytic on `ball 0 r \ {0}` and `‖w₀‖^{1/k} < r`
(informally — the exact side condition mirrors `norm_lt_of_pow_eq`). **Local branches** (no
monodromy): apply `RS.AnalyticAt.exists_pow_eq (u := id) analyticAt_id (hu₀ : w₀ ≠ 0) hk` to get
`ψ₁ : ℂ → ℂ` analytic at `w₀`, `ψ₁ w₀ ≠ 0`, `∀ᶠ w in 𝓝 w₀, ψ₁ w ^ k = w`. Fix
`ζ := Complex.isPrimitiveRoot_exp k hk` (a witness primitive `k`-th root of unity, spike-verified
existence) and set `ψ i w := ζ^i * ψ₁ w` for `i ∈ Finset.range k`. Each `ψ i` is analytic at
`w₀` (constant multiple), `ψ i w₀ ≠ 0`, and (eventually near `w₀`) `ψ i w ^ k = ζ^{ik} ψ₁(w)^k =
w` (`ζ^k = 1`). **Distinctness**: `IsPrimitiveRoot.injOn_pow_mul ζ_prim (hα := ψ₁ w₀ ≠ 0)` gives
`Set.InjOn (fun i => ζ^i * ψ₁ w₀) (Finset.range k)`, i.e. `i ↦ ψ i w₀` injective on
`Finset.range k` — a **pointwise-at-`w₀`** fact requiring zero continuity/openness argument.
Persistence nearby: each pairwise difference `ψ i - ψ j` (`i≠j`) is continuous and nonzero at
`w₀`, hence nonzero on some further-shrunk neighborhood (`ContinuousAt.eventually_ne`); intersect
over the finitely many pairs (`Finset.range k ×ˢ Finset.range k`) to get a single neighborhood
`V ∋ w₀` on which all `ψ i` remain pairwise distinct and all satisfy `ψ i w^k = w`.
**Bijection onto the root set**: for `w ∈ V` (`w ≠ 0` automatic, shrinking `V` if needed so
`0 ∉ V`), `i ↦ ψ i w` is an injective map `Finset.range k → {z | z^k = w}`; the target has
EXACTLY `k` elements (`ncard_setOf_pow_eq hk hw`, mapping-degree's `RootCounting`), so by a
finite-pigeonhole/cardinality argument (`Set.Finite.injOn_iff_bijOn_of_ncard_le` or
`Finset.image`-then-`Finset.eq_of_subset_of_card_le`) the map is actually a BIJECTION
`Finset.range k ≃ {z|z^k=w}` (as finsets, via `Set.Finite.toFinset`). **Conclude**: `traceZk h k w
= ∑ᶠ z ∈ {z|z^k=w}, h z = ∑ i ∈ Finset.range k, h (ψ i w)` (reindex along the bijection —
`Finset.sum_bij`/`finsum_mem_eq_of_bijOn`, the SAME lemma mapping-degree's `LocalConstancy.lean`
already uses for an analogous chart-transport, `finsum_mem_eq_of_bijOn`). The RHS, as a function
of `w`, is a FINITE sum of `h ∘ ψ i` (composites of `h`, analytic at `ψ i w₀ ≠ 0` by hypothesis on
`h`'s domain, with `ψ i`, analytic at `w₀`) — analytic at `w₀` (`AnalyticAt.comp`, finite sum).
Since `traceZk h k =ᶠ[𝓝 w₀]` this RHS (the bijection holds on the whole neighborhood `V`, not
just at `w₀`), `AnalyticAt.congr` closes.

Est. 80–110 lines (the distinctness-persistence + bijection-from-injection-and-equal-cardinality
steps are the fiddly parts; both are standard finite combinatorics, no analysis).

### P5. `meromorphicAt_traceZk` (PlanarTrace.lean, THE hardest theorem — 40+ line plan)

Fix `hh : MeromorphicAt h 0`, `hk : k ≠ 0`. Goal: `MeromorphicAt (traceZk h k) 0`, i.e. produce
`M : ℕ` with `AnalyticAt ℂ (fun w => w ^ M * traceZk h k w) 0` (mathlib's bare existential
definition of `MeromorphicAt`, `Analysis/Meromorphic/Basic.lean:36` — we will in fact produce a
function equal to `traceZk h k` off `0` and analytic-after-repair, then transport via
`MeromorphicAt.congr`, which only needs `𝓝[≠]0`-agreement, sidestepping any pointwise-junk
bookkeeping at `w=0` entirely).

1. **Order presentation of `h`.** From `meromorphicOrderAt_eq_int_iff hh`, get `n₀ : ℤ`,
   `u : ℂ → ℂ` analytic at `0`, `u 0 ≠ 0`, `h =ᶠ[𝓝[≠]0] fun z => z^{n₀} * u z` (`smul_eq_mul`).
2. **Euclidean split of the exponent by `k`.** `q := n₀ / k` (`Int.ediv`), `r := (n₀ % k).toNat`
   (`Int.emod`, `0 ≤ n₀ % k < k` since `k > 0` — `Int.emod_nonneg`/`Int.emod_lt_of_pos`), with
   `n₀ = k * q + r` (`Int.ediv_add_emod`). Both `q, r` depend only on `n₀, k` — the SAME for
   every root, no per-branch bookkeeping.
3. **Reduction to a bounded punctured-disk function.** Define (globally, no branch choice)
   `V : ℂ → ℂ := fun w => w ^ (-q) * traceZk h k w` (`zpow`, `q : ℤ`; well-defined pointwise for
   ALL `w`, junk at `w = 0` where `0^{-q}` is `0` if `-q>0`, undefined-convention `0` if `-q≤0`
   times whatever `traceZk h k 0` is — irrelevant, see below). **Claim**:
   `traceZk h k =ᶠ[𝓝[≠]0] fun w => w^q * V w` — literally `w^q \cdot w^{-q} = 1` off `w=0`
   (`zpow_add₀`/cancellation), so this is an unconditional pointwise identity off `0`, no
   eventual-ness even needed beyond `w ≠ 0`.
4. **`V` is analytic on a punctured disk near `0`.** By P4, `traceZk h k` is analytic at every
   `w₀ ≠ 0` small enough (using `hh`'s analyticity of `h` away from its own pole locus — `h` is
   `AnalyticAt` at every `z ≠ 0` in a punctured neighborhood of `0`, a standard consequence of
   `MeromorphicAt` — `MeromorphicAt.eventually_analyticAt hh`); `w ↦ w^{-q}` is analytic on
   `{w≠0}` (`zpow`, entire away from `0` regardless of sign of `q`). Product of analytic
   functions ⇒ `V` analytic at every `w₀≠0` in a small enough punctured disk `D := ball 0 ρ \ {0}`.
5. **Norm bound on `V` over `D` (the crux — NO branch functions needed here, just the root SET).**
   For `w ∈ D`, `w ≠ 0`:
   `traceZk h k w = ∑ᶠ z ∈ {z|z^k=w}, h z`. Shrink `ρ` so that (a) EVERY root `z` of every
   `w ∈ D` lies in `h`'s domain of validity for the order presentation (i.e. `‖z‖ < ρ_h` for the
   presentation's radius — using `‖z‖^k = ‖w‖ < ρ^k` i.e. `‖z‖<ρ`, so take `ρ ≤ ρ_h`), and (b)
   `ρ ≤ 1` (so `‖z‖<1`, needed for a crude power bound below) and (c) `ρ` small enough that
   `u`'s continuity gives a bound `‖u z‖ ≤ C_u` for `‖z‖ < ρ` (`u` continuous at `0` — bounded
   near `0` by continuity, `IsCompact.exists_bound_of_continuousOn` on `closedBall 0 ρ` or
   simply `Metric.continuousAt_iff`-style `∃ρ, ∀ z, ‖z‖<ρ → ‖u z - u 0‖<1` then triangle
   inequality for `C_u := ‖u 0‖+1`). For each root `z` (`z^k=w`, `‖z‖<ρ`, `z ≠ 0` since `w≠0`):
   `h z = z^{n₀} u z` (order presentation, valid since `‖z‖<ρ_h`), and
   `z^{n₀} = z^{kq+r} = (z^k)^q \cdot z^r = w^q \cdot z^r` (`zpow`/`pow` algebra, `z≠0`, `q:ℤ`,
   `r:ℕ`). So `‖h z‖ = ‖w‖^{(q:ℝ)} \cdot ‖z‖^r \cdot ‖u z‖` (`norm_zpow`, `norm_pow`, `norm_mul` —
   `‖w^q‖=‖w‖^q` a REAL zpow of a nonneg real, well-defined for ANY sign of `q`, no `rpow`) `≤
   ‖w‖^q \cdot 1 \cdot C_u` (`‖z‖ < ρ ≤ 1` ⇒ `‖z‖^r ≤ 1`, `r:ℕ`). Summing over the (at most `k`,
   by `ncard_setOf_pow_eq`/`setOf_pow_eq_finite`) roots:
   `‖traceZk h k w‖ ≤ (k:ℝ) \cdot C_u \cdot ‖w‖^q` (triangle inequality over the finite
   `finsum`/`Finset.sum`, `finsum_mem_le_sum`-style or convert to `Finset.sum` first via
   `finsum_mem_eq_finite_toFinset_sum`). Hence
   `‖V w‖ = ‖w‖^{-q} \cdot ‖traceZk h k w‖ ≤ k \cdot C_u` for all `w ∈ D` (the `‖w‖^{-q}\cdot
   ‖w‖^q=1` cancellation is exact real-zpow arithmetic, `zpow_add₀`/`Real.zpow` cancellation, no
   sign case split needed since it is a group identity in `ℝ≥0`/`ℝ` away from `0`).
6. **Riemann removable singularity.** `V` is `DifferentiableOn ℂ` on `D = ball 0 ρ \ {0}` (step
   4, `AnalyticAt.differentiableAt` pointwise ⇒ `DifferentiableOn`) and
   `BddAbove ((norm∘V) '' D)` (step 5, uniform bound `k C_u`). Apply
   `Complex.differentiableOn_update_limUnder_of_bddAbove (hc : ball 0 ρ ∈ 𝓝 0) (hd) (hb)`:
   `DifferentiableOn ℂ (Function.update V 0 (limUnder (𝓝[≠]0) V)) (ball 0 ρ)`. In particular
   `AnalyticAt ℂ (update V 0 (limUnder (𝓝[≠]0) V)) 0` (open-set `DifferentiableOn` in `ℂ` is
   `AnalyticOnNhd`, standard mathlib equivalence — `DifferentiableOn.analyticOnNhd`-style,
   confirm exact name during implementation; a `DifferentiableAt`-at-every-point-of-an-open-set
   fact is literally `AnalyticAt` for holomorphic functions, one of mathlib's basic complex
   analysis equivalences).
7. **Transport back to `traceZk h k`.** `update V 0 _ =ᶠ[𝓝[≠]0] V` (`Function.update`, agrees off
   the updated point, `Filter.eventually_of_mem self_mem_nhdsWithin`-style / literally
   `update_noteq` pointwise for every `w≠0`). So `AnalyticAt.meromorphicAt` on step 6's function,
   `.congr` along this `𝓝[≠]0`-agreement gives `MeromorphicAt V 0`. Then
   `MeromorphicAt (fun w => w^q) 0` (`analyticAt_id.meromorphicAt.zpow q` if `q ≥0`, or via the
   bare existential directly: `(·)^q` IS meromorphic at `0` for ANY `q:ℤ` — mathlib's
   `MeromorphicAt.zpow`/`meromorphicAt_zpow`-style closure lemma, confirm name). Product:
   `MeromorphicAt (fun w => w^q * V w) 0` (`MeromorphicAt.mul`). Finally, `traceZk h k =ᶠ[𝓝[≠]0]
   fun w => w^q * V w` (step 3, unconditional off `0`), so `MeromorphicAt.congr` (in the OTHER
   direction — congr transports the conclusion from the RHS witness to `traceZk h k` itself)
   closes: `MeromorphicAt (traceZk h k) 0`. ∎

Est. **210–260 lines** for the full file-4 write-up of this theorem (steps 1–3 are ~30 lines,
step 4 ~20, step 5 is the longest at ~90–120 lines of norm/zpow bookkeeping, steps 6–7 ~40).
This matches the task's "40+ lines of plan" ask (the plan itself, above, is already ~55 lines of
prose; the Lean is 4–5× that). **Key insight enabling the whole plan**: bounding
`h`'s value at a root `z` of `w` via `‖z‖^k=‖w‖` needs NO real (non-integer) exponents anywhere,
because the "fractional part" of `n₀/k` is entirely absorbed into the FIXED natural number `r`
(bounded crudely by `1`, since `‖z‖<1`), leaving only the honest INTEGER zpow `w^q` to carry the
growth/decay — this is what makes the removable-singularity route clean instead of needing
`Real.rpow` continuity/monotonicity lemmas.

### P6. `laurentCoeffAt_traceZk` (Laurent-coefficient formula)

Reuse P5's `q, r, u` (same order presentation, same Euclidean split). **Key sub-identity**:
on a small enough punctured disk, `V w = ∑_{i<k} (ψ i w)^r \cdot u(ψ i w)` for `w ≠ 0` — this
follows by combining P4's local-branch computation of `traceZk h k` with the same
`z^{n₀}=w^q z^r` algebra as P5 step 5 (now used to derive an EXACT identity, not just a bound):
`traceZk h k w = ∑_i h(ψ i w) = ∑_i (ψ i w)^{n₀} u(ψ i w) = ∑_i w^q (ψ i w)^r u(ψ i w) = w^q
\sum_i (ψ i w)^r u(ψ i w)`, so `V w = \sum_i (ψ i w)^r u(ψ i w)` (cancel `w^q`, `w≠0`) — matches
`traceZk h k w / w^q` by definition of `V`.
**Power-series substitution.** `u` is genuinely `AnalyticAt ℂ` at `0` (not just meromorphic), so
mathlib gives `HasFPowerSeriesAt u p 0` for a convergent `p`, with `taylorCoeffAt u 0 j = p.coeff
j =: b j` (`HasFPowerSeriesAt.taylorCoeffAt_eq`, residue-calculus, built). For `w` in a small
enough punctured disk (all `ψ i w` within `p`'s radius of convergence — shrink further if
needed), `u (ψ i w) = ∑'_j b_j (ψ i w)^j` (the genuine convergent sum, `HasFPowerSeriesAt`'s
`hasSum`). So `(ψ i w)^r u(ψ i w) = ∑'_j b_j (ψ i w)^{j+r}`, and (finite sum over `i`, linearity
of `tsum`) `V w = ∑'_j b_j \left(\sum_{i<k} (ψ i w)^{j+r}\right)`.
**Geometric-sum collapse.** `∑_{i<k} (ψ i w)^{j+r} = (ψ_1 w)^{j+r} ∑_{i<k} ζ^{i(j+r)}` — this sum
is `k` if `k ∣ (j+r)` (all terms `1`) and `0` otherwise (`geom_sum_eq` with ratio `ζ^{j+r} ≠ 1`,
spike-verified §9, since `ζ` is a PRIMITIVE `k`-th root, `ζ^{j+r}=1 ↔ k ∣ (j+r)` —
`IsPrimitiveRoot.pow_eq_one_iff_dvd` or equivalent, standard). When `k ∣ (j+r)`, write
`j + r = k m'` (`m' ≥ 0` since `j,r≥0`); then `(ψ_1 w)^{j+r} = (ψ_1 w)^{k m'} = ((ψ_1 w)^k)^{m'} =
w^{m'}` (EXACT, integer power, no branch ambiguity — the whole point of only ever raising `ψ_1(w)`
to a MULTIPLE of `k`). So `V w = k \sum_{m' : k m' - r ≥ 0} b_{km'-r} w^{m'}` — a genuine
convergent power series in `w` (reindexed `j = km'-r`), confirming (independently of P5's
removable-singularity route) that `V` is analytic at `0` with **Taylor coefficient at `m'` equal
to `k \cdot b_{km'-r}`** (`taylorCoeffAt V 0 m' = k * taylorCoeffAt u 0 (k*m'-r)`, matching the
"pad with 0 if `km'-r<0`" convention already built into `taylorCoeffAt`/`laurentCoeffAt`'s API).
**Shift to `traceZk`.** `traceZk h k = (·)^q \cdot V` off `0` (P5 step 3), so by the shift lemma
`laurentCoeffAt_zpow_mul` (residue-calculus, built): `laurentCoeffAt (traceZk h k) 0 m =
laurentCoeffAt V 0 (m - q)`. Since `V` is analytic (just reproven), `laurentCoeffAt V 0 (m-q) =
taylorCoeffAt V 0 (m-q)` for `m-q ≥ 0`, `0` else (`laurentCoeffAt_of_analyticAt`, built) `=
k \cdot b_{k(m-q)-r}` (for `m-q≥0`; the `m-q<0` case gives `0` on both sides — check against `h`'s
own coefficient at `km`, which is ALSO `0` there since `km < kq+r=n₀`'s ordering... — `omega`
after unfolding). Recognize `k(m-q)-r = km-kq-r = km-n₀` — this is **exactly** `h`'s Taylor
coefficient index for its unit factor `u` at the SHIFTED index `km`: `laurentCoeffAt h 0 (km) =
taylorCoeffAt u 0 (km - n₀)` (`laurentCoeffAt_of_eventuallyEq` with `h`'s own presentation,
`n:=n₀`). So `laurentCoeffAt (traceZk h k) 0 m = k \cdot taylorCoeffAt u 0 (km-n₀) = k \cdot
laurentCoeffAt h 0 (km)`. ∎

Est. 130–170 lines (the `tsum`/power-series substitution and the geometric-sum-collapse indexing
are the bulk; the final shift-matching is short given residue-calculus's `laurentCoeffAt_zpow_mul`
and `laurentCoeffAt_of_analyticAt`/`laurentCoeffAt_of_eventuallyEq` are already built). **This
theorem is secondary to P5** (existence of meromorphy) — if it proves harder than budgeted, ship
P5 alone and defer P6/`resAt_traceZk` to a follow-up pass; `form-trace-tower` needs the
COEFFICIENT-SHIFT fact eventually but not before it needs `traceZk` to exist as a meromorphic
function at all.

**Why this does NOT simplify to "residue of trace = sum of residues".** Setting `m = -1`:
`resAt (traceZk h k) 0 = k \cdot laurentCoeffAt h 0 (-k)`, a single coefficient of `h` at index
`-k`, not a residue of `h` (which would be the coefficient at `-1`) unless `k=1`. This confirms
the blueprint's own scoping: Miranda's eq. (3.2) residue identity `Res(Tr(h·ω)) = ∑ Res(h·ω)`
holds **only after multiplying by the form `ω`**, whose transformation law under `z ↦ z^k`
contributes an extra factor `k z^{k-1}` (from `d(z^k) = kz^{k-1}dz`) that exactly compensates
this coefficient shift (index `-1` upstairs becomes, after the `z^{k-1}` factor, the SAME index
`-1` downstairs instead of `-k`). This is precisely why the form-level identity is
`form-trace-tower`'s job and not provable at the bare-function level here — good confirmation the
scope split is mathematically forced, not just a work-division convenience.

### P7. `trace` well-definedness and meromorphy (FunctionTrace.lean)

**Definition mechanics.** `trace F h y₀` picks, via `Classical.choice (exists_fiberStack hF hne
y₀)`, SOME `S : FiberStack F y₀`, and computes `∑_i traceZk (h ∘ (S.A i).e.symm) (multiplicity F
(S.pt i)) ((S.A i).e' y₀)`. (`(S.A i).e' y₀ = 0` always, by `map_eq_zero'` — so the formula
always evaluates `traceZk` AT its junk point `0`; this is fine, see §6, since we only need the
GERM/meromorphy of `y ↦ trace F h y` near `y₀`, not this one value, exactly as `toP1`'s
construction never needed its `w=0` junk value either.)

**Meromorphy at `y₀` (`meromorphicAtX_trace`).** Work in the chart `chartAt ℂ y₀`. For `y` near
`y₀` (in `S.V`), `trace F h y = \sum_i traceZk (h∘(S.A i).e.symm) (mult_i) ((S.A i).e' y)` — this
is the SAME formula as at `y₀` but evaluated at the moving point `(S.A i).e' y`; since (as
observed in D7) `(S.A i).e'` restricted to `S.V` agrees, for every `i`, with the SAME function
`η(y) := chartAt ℂ y₀ y - chartAt ℂ y₀ y₀` (both are literal unfoldings of
`AdaptedChartsAt`'s target-chart construction — `chartAt ℂ (F (S.pt i)) = chartAt ℂ y₀` for
every `i` since `F (S.pt i) = y₀` for all `i`, `(S.pt i)`'s own recentering translation is
therefore identical across `i` too), `trace F h` reads, in the chart `η`, as the FINITE SUM
`\sum_i traceZk (h ∘ (S.A i).e.symm) (mult_i)`, each summand meromorphic at `0` by P5 (applied to
`h ∘ (S.A i).e.symm`, meromorphic at `0` since `h` is meromorphic at `S.pt i` and `(S.A i).e` is
a biholomorphism there — chart-invariance of meromorphy, `meromorphicAtX_iff_of_mem_source`-style,
composed with `(S.A i).e.symm`'s own analyticity). Sum of finitely many `MeromorphicAt`-at-`0`
functions is `MeromorphicAt` at `0` (`MeromorphicAt.sum`/iterated `.add`); transport through the
chart `η` (essentially `chartAt ℂ y₀`, up to the harmless additive recentering) back to
`MeromorphicAtX (trace F h) y₀` via the standard chart-composite definitional unfold (`ordAtX`/
`MeromorphicAtX`'s own definitional shape — `MeromorphicAtX g y₀ := MeromorphicAt (g∘(chartAt ℂ
y₀).symm)(chartAt ℂ y₀ y₀)`, and our formula IS `g∘(chartAt ℂ y₀).symm` up to the recentering
constant, a `meromorphicAt_congr`-transparent rewrite).

**Well-definedness against the `FiberStack` choice (`trace_well_defined`).** Two `FiberStack`s
`S, S'` at `y₀` both decompose the SAME fiber `F⁻¹{y₀}` (via `range_pt`), just with possibly
different enumerations/chart radii/adapted-chart choices. The two candidate formulas, AS GERMS
at `y₀` (i.e., as elements of `MeromorphicAt _ (chartAt ℂ y₀ y₀)`, not as literal functions), must
agree: both equal, term-by-term-in-a-common-refinement, the SAME underlying "sum over preimages,
weighted by `traceZk` at each adapted chart" — the cleanest proof avoids re-proving a general
"any two adapted-chart covers of a fiber give co-refinable data" lemma from scratch by instead
comparing each `S`-term DIRECTLY against the disjoint decomposition `fiber_eq_iUnion`
(`FiberStack`'s own export) shared by both stacks: since `pt_injective`/`range_pt` pin down the
SAME underlying finite index SET (`F⁻¹{y₀}`, just enumerated differently by `S.pt`/`S'.pt`), a
bijection `Fin S.n ≃ Fin S'.n` matching `S.pt`/`S'.pt` at the same fiber points exists
(`Equiv.ofBijective` on the composite `S'.pt⁻¹ ∘ S.pt`, both injective with the same range); under
this bijection, `multiplicity F (S.pt i) = multiplicity F (S'.pt (σ i))` (multiplicity is a
function of the POINT, not the stack) and the two adapted charts `(S.A i)`, `(S'.A (σ i))` at the
SAME point `S.pt i` differ only by a bi-analytic overlap transition (both are `AdaptedChartsAt F
(S.pt i) _` — local-multiplicity's own uniqueness-up-to-transition machinery, if exported, or a
direct argument: composing `h∘(S.A i).e.symm` with the transition `(S.A i).e ∘ (S'.A (σ i)).e.symm`
recovers `h∘(S'.A(σi)).e.symm`, and `traceZk`'s meromorphy/Laurent data transport correctly
through a LOCAL biholomorphic change of variable fixing `0`... **this last step needs a
"`traceZk` intertwines with precomposition by a `k`-th-root-preserving biholomorphism" lemma we
have NOT designed** — flagged as **Risk R1** below (§7); the fallback is to simply not prove
general well-definedness and instead state all downstream consequences (`meromorphicAtX_trace`,
`trace_of_regular`) directly in terms of `trace`'s `Classical.choice`d value, which is all
`form-trace-tower` actually needs (it will always call `trace F h y₀` and separately invoke
`exists_fiberStack`, never needing to compare two different explicit stacks itself).

**Junk for constant `F`** (`trace_of_forall_eq`): if `F ≡ c`, `exists_fiberStack` still produces
SOME stack at any `y₀' ≠ c` with `n = 0` (empty fiber, `range_pt = F⁻¹{y₀'} = ∅` since `F ≡ c ≠
y₀'`) — the formula's sum over `Fin 0` is vacuously `0`. At `y₀' = c` itself, though,
`F⁻¹{c} = univ` (ALL of `X`), and `exists_fiberStack`'s existence proof does NOT need `F`
nonconstant (mapping-degree's own note, §2 `exists_fiberStack`'s docstring: "does NOT need `F`
surjective... nor the fiber nonempty") — but does it produce a SENSIBLE (finite!) stack when the
fiber is ALL of `X`? Only if `X` itself is somehow finite (it is not, being a positive-dimensional
manifold) — **`exists_fiberStack` for constant `F` at `y₀=c` will fail to exist or (more likely,
tracing through its proof) silently misbehave since `fiber_finite` itself REQUIRES `hne`**
(mapping-degree's `fiber_finite` signature: `(hF)(hne : ¬∃c,∀x,F x=c)(y)`). So `trace` as
DEFINED (via `Classical.choice (exists_fiberStack hF hne y₀)`) **requires `hne` as an argument to
typecheck the choice** — meaning `trace`'s signature must actually carry `hF`/`hne` as
hypotheses baked into the `noncomputable def` (unusual — defs are normally hypothesis-free, with
hypotheses only on the THEOREMS about them, matching `fiberMultSum`'s own pattern of being
hypothesis-free with junk built in via `finsum`). **Design correction**: redefine `trace` via
`Classical.choice` guarded by an `if`-dispatch on `Nonempty (FiberStack F y₀)` (always inhabited
when `F` is holomorphic and nonconstant, by `exists_fiberStack`, but the DEFINITION itself should
not demand the hypothesis): `noncomputable def trace (F) (h) (y₀) : ℂ := if hS :
Nonempty (FiberStack F y₀) then (formula using hS.some) else 0` — total, junk `0` when no stack
can be witnessed (which provably only happens for `F` non-holomorphic or `y₀` in some genuinely
pathological case; for holomorphic possibly-constant `F`, `exists_fiberStack`'s proof, rechecked,
ACTUALLY only used `hne` to invoke `one_le_multiplicity_of_not_const`/`fiber_finite`, i.e. it is
NOT provable without `hne` in general, so for CONSTANT `F` the `if`-condition
`Nonempty (FiberStack F y₀)` is simply left an open question — a stack might or might not exist
per point; either way `trace` is well-defined via the `if`-dispatch, and `trace_of_forall_eq`
becomes a real theorem to prove (probably via: for constant `F ≡ c`, `y₀ ≠ c` DOES admit a
trivial degenerate 0-fiber stack directly hand-built (`n:=0`, vacuous data) regardless of `hne`,
giving `trace F h y₀ = 0` there by the empty sum; `y₀ = c` is the genuinely degenerate point,
where we simply case on `Nonempty (FiberStack F y₀)` being possibly False (as in there is no
consistent finite/adapted-chart structure over the full fiber `univ`) — if False, `trace F h c =
0` by the `if`'s else-branch, done; the design does not need to resolve whether it is actually
False, only that EITHER branch gives `0`, so `trace_of_forall_eq`'s proof only needs the `y₀≠c`
case done honestly plus the `y₀=c` case handled by a SEPARATE small direct argument or simply
accepted as an open sub-case left for the builder — flagged as **Risk R2**).

Est. 150–200 lines for the meromorphy proof (the bulk), the well-definedness caveat write-up
(with R1's fallback taken) ~20 lines, junk-guard ~30–40 lines including the `if`-based
redefinition.

---

## 6. Junk/convention ledger

| Object | Honest domain | Junk value | Why safe |
|---|---|---|---|
| `toP1 f x` | `MeromorphicAtX f x` | whatever `if`-branch fires on non-meromorphic `f` | never quoted for non-meromorphic `f`; all theorems guard with `MeromorphicOnX` |
| `multiplicity (toP1 f) x` | `ordAtX f x ≠ 0` (zero/pole) | CC4's own junk (`0` if `toP1 f` not holomorphic at `x`, `1` at genuinely unramified points) | bridge theorems (P2) are stated only for `>0`/`<0`; the `=0` case is a SEPARATE, easy corollary, never silently assumed |
| `∑ᶠ x, (ordAtX f x).untop₀` | `f` meromorphic everywhere, nonconstant | `0` contribution from every `ordAtX f x ∈ {0,⊤}` point | matches `Divisor`'s own convention (support = `{ord ≠ 0}`); `⊤`-points (locally-≡0, excluded by nonconstancy in practice) contribute `0` harmlessly either way |
| `traceZk h k w` | `w ≠ 0` (root set has the "correct" `k` elements) | `traceZk h k 0 = h 0` literally (root set is the singleton `{0}`) | **the one genuinely non-obvious junk value in this unit** — mathematically the "correct" branch-point value would be a multiplicity-`k`-weighted limit, not `h 0`; we NEVER state a lemma about `traceZk h k 0`'s literal value (only about `MeromorphicAt`/`laurentCoeffAt`/`resAt` at `0`, all of which are `𝓝[≠]0`-germ notions, hence blind to this junk) |
| `traceZk_comp_pow` | `w ≠ 0` | not stated at `w=0` | the identity is genuinely FALSE at `w=0` (LHS `g(0)`, "should be" `k·g(0)`) — flagged explicitly in §4.4, not silently dropped |
| `trace F h y₀` | `Nonempty (FiberStack F y₀)` (always true for holomorphic nonconstant `F`) | `0` if no stack witnessed (only possibly relevant for constant `F`, §5.7 R2) | constant-`F` guard (`trace_of_forall_eq`) stated and proved (mod R2) explicitly, not left to accidental unfolding |

No junk value here makes a stated theorem vacuously true: every "honest" theorem (P2–P6, `P7`'s
meromorphy statement) carries the precise guarding hypothesis (`0 < ordAtX f x`,
`MeromorphicAt h 0`, `Nonempty (FiberStack F y₀)` implicitly via `hF/hne`), and the argument
principle's finsum is over ALL of `X` with the RIGHT junk convention baked into `.untop₀`
(matching CC2's own `Divisor`/`degree` convention, so `proper-map-degree`'s repackaging is
literally a rewrite, not a re-derivation).

---

## 7. Risks & fallbacks

1. **HIGH — upstream drift on three partially-built units simultaneously.**
   `meromorphic-and-divisors` (`Predicates.lean`/`CodiscreteBridge.lean` built; `GermSpace`/
   `OrderEval`/`Field`/`Divisor`/`LinearSystem` not), `projective-line` (`Inversion`/`Charts`
   built; `Holomorphy`/`Sphere`/`GenusZero` not), `residue-calculus` (design frozen, files being
   finished). Mitigation already baked into the design: `ToP1.lean` does NOT depend on either
   `OrderEval.lean` or `Holomorphy.lean` (§0.2, D2) — it only reads the ALREADY-BUILT
   `Predicates.lean`/`CodiscreteBridge.lean` and `Charts.lean`. If `Predicates.lean`'s exact
   lemma names drift before this unit is built, only `ToP1.lean`/`OrderMultiplicity.lean` need
   mechanical edits (both files are thin wrappers over 4–5 named lemmas each, listed in §1).
   `PlanarTrace.lean` has ZERO manifold-unit dependencies beyond mathlib +
   `MappingDegree.RootCounting` + `LocalMultiplicity.KthRoot` + `ResidueCalculus`, all four
   already built or frozen-designed — it is the SAFEST file to build first if the manifold-side
   units are still churning.
2. **MEDIUM — `trace`'s well-definedness (P7) is the weakest link.** The "any two `FiberStack`s
   give the same germ" argument needs a `traceZk`-intertwines-with-local-biholomorphisms lemma
   that is NOT designed here (flagged R1 in P7). Fallback (already the design's default, not an
   afterthought): state `trace`'s consumer-facing theorems (`meromorphicAtX_trace`,
   `trace_of_regular`) purely in terms of the `Classical.choice`-fixed value; do not attempt
   general well-definedness unless `form-trace-tower` explicitly needs to compare two
   independently-constructed stacks (it should not — it will call `RS.MTrace.trace F h` and treat
   it as a black box, exactly as `RS.degree`/`RS.fiberMultSum` are treated by THEIR consumers).
3. **MEDIUM — `toP1_not_const` (D3, P-lite in §2.3)'s "pointwise at every nearby point" step.**
   If the "canonical value ≡ 0 as a genuine function near `x₀`, not just at `x₀`" argument proves
   fiddlier than sketched, DROP `toP1_not_const` entirely and state
   `finsum_ordAtX_eq_zero`/`ArgumentPrinciple.lean`'s theorems with `hne : ¬∃c,∀x,toP1 f x=c` as
   a bare hypothesis (already the PRIMARY signature in §4.3 — `finsum_ordAtX_eq_zero'` is the
   convenience wrapper, not the load-bearing export). Zero cost to `proper-map-degree`, which
   will have its own nonconstancy witness once `ℳ X`/`Field` land.
4. **MEDIUM — P5/P6's `zpow`/`Int.ediv`/`Int.emod` bookkeeping.** Sign-heavy integer arithmetic
   (`q,r` from Euclidean division, `WithTop ℤ`/`ℕ∞`/`ℤ`/`ℕ` casts throughout P2/P3/P5/P6). No
   single fallback beyond generous `omega`/`push_cast` use and keeping every cast explicit in
   intermediate `have`s (the design's proof plans already do this deliberately, unlike a
   from-scratch attempt that might try to shortcut through mixed `WithTop ℤ`/`ℤ` arithmetic
   directly).
5. **LOW — `DifferentiableOn.analyticOnNhd`-equivalence exact name (P5 step 6).** Standard
   mathlib fact (differentiable on an open ℂ-subset ⟺ analytic there) but the exact lemma name
   was not pinned during this design's spike (§9 did not need it, only the removable-singularity
   lemma itself, which directly gives `DifferentiableOn`). Pin during implementation; if
   surprisingly absent, `AnalyticAt` follows from `DifferentiableAt` + `Complex.analyticAt_of_
   differentiable_on_punctured_nhds_of_continuousAt`-style reasoning restated at a point already
   known differentiable on a full neighborhood (trivial specialization, already in
   `RemovableSingularity.lean`, read in full at §1/§9).
6. **LOW — `π`-notation ambiguity** (spike gotcha, §1/§9): when re-stating
   `Complex.isPrimitiveRoot_exp`'s output type by hand, elaboration can pick a different `π`
   notation than the one baked into the lemma. Always bind via `have`/`obtain`, never re-type the
   target type.
7. **LOW — degree_comp-style scope creep.** None of this unit's exports are in any OTHER unit's
   critical path except `proper-map-degree` (cluster 1) and `form-trace-tower` (cluster 2's
   `traceZk`/`trace`); if `Tr_F h`'s well-definedness (R1) or the junk-for-constant-`F` guard (R2)
   run long, ship `traceZk`'s full planar theory (file 4, self-contained) plus the argument
   principle (files 1–3) and report `FunctionTrace.lean` as partial — cluster 1 has zero
   dependency on cluster 2's global assembly.

---

## 8. Downstream map

| Consumer | What it needs | Our export |
|---|---|---|
| **proper-map-degree** | `deg(div f) = 0` | `finsum_ordAtX_eq_zero`/`sum_ordAtX_eq_zero_of_finite` (repackage via `Divisor`/`Divisor.degree`, their bookkeeping) |
| **form-trace-tower** | the planar trace atom + its Laurent-coefficient behavior; the surface-level `Tr_F h` as a black box | `traceZk`, `meromorphicAt_traceZk`, `laurentCoeffAt_traceZk`, `resAt_traceZk`; `RS.MTrace.trace`, `meromorphicAtX_trace`, `trace_of_regular` (sanity anchor), `trace_of_forall_eq` (junk guard) |
| **laurent-tails (CC8)** | none directly from us (blueprint edge is `canonical-forms, meromorphic-trace`, but nothing here is `laurent-tails`-facing beyond what `residue-calculus`/`form-trace-tower` already mediate) | — |
| **genus-zero-headline / Abel** | indirectly, via `proper-map-degree`'s `deg(div f)=0` | (transitive) |

---

## 9. Spike report (`scratch_mtrace.lean`, project root)

Gate respected (`pgrep -cx lean` < 3 at run time). `lake env lean scratch_mtrace.lean`:
**compiles clean, exit 0, ~5.3 s wall** (imports: `Analysis.Complex.RemovableSingularity`,
`RingTheory.RootsOfUnity.{Complex,PrimitiveRoots}`, `Algebra.Field.GeomSum`,
`Jacobian.MappingDegree`, `Jacobian.ProjectiveLine.Charts`). Verified by re-typing exact
statements:

1. `Complex.differentiableOn_update_limUnder_of_bddAbove` — exact hypothesis shape
   (`s ∈ 𝓝 c`, `DifferentiableOn ℂ f (s\{c})`, `BddAbove ((norm∘f)''(s\{c}))`) and conclusion
   (`DifferentiableOn ℂ (Function.update f c (limUnder (𝓝[≠]c) f)) s`) — **the meromorphy-at-0
   engine for `traceZk`, confirmed usable exactly as planned in P5**.
2. `Complex.isPrimitiveRoot_exp k hk : IsPrimitiveRoot (cexp (2*↑Real.pi*I/k)) k` exists (note:
   restating its type by hand hits the `π`-notation gotcha, §1/§7 R6 — fixed by binding via
   `⟨_, ...⟩` instead).
3. `IsPrimitiveRoot.injOn_pow_mul` — confirmed usable to get pairwise distinctness of the `k`
   branches `ζ^i * α` against a nonzero basepoint `α`, with ZERO continuity/monodromy argument
   (a pointwise fact at a single value, exactly as P4 needs it).
4. The `Σ_{i<k} (ζ^m)^i = 0` geometric-sum-vanishing engine (`geom_sum_eq` + `zpow`/`pow`
   algebra for `(ζ^m)^k=1`) compiles as planned — confirms P6's collapse step is mechanically
   available.
5. **Cross-unit smoke test** (the DAG-gap check, §0.2): `Jacobian.MappingDegree` and
   `Jacobian.ProjectiveLine.Charts` import together without conflict; `RS.fiberMultSum_eq_degree`
   applied to an abstract `F : X → OnePoint ℂ` and `RS.P1.chartAt_coe`/`RS.P1.invChart_apply_coe`
   both typecheck in the same file — confirms the missing blueprint edge (mapping-degree +
   projective-line as joint dependencies of meromorphic-trace) causes no actual Lean conflict,
   only a documentation gap.

---

## 10. Coordination notes filed

- `docs/requests/projective-line.md` (**new file**): records that `meromorphic-trace` needed
  `Holomorphy.lean`'s planned exports (`contMDiffAt_of_pole`, `ContMDiffAt.onePointCoe`,
  `meromorphicAt_coeChart_comp`) but did not block on them — built `ToP1.lean`'s bridge locally
  instead, using only `Charts.lean` + local-multiplicity's general `X→Y` bridge. Suggests, once
  `Holomorphy.lean` lands, `ToP1.toP1_contMDiff`'s proof could be shortened by reusing its general
  iff-lemmas — non-blocking, cosmetic.
- `docs/requests/meromorphic-and-divisors.md` (appended): records the same for `OrderEval.lean`'s
  planned `evalAt`/`holoRepr` (D2) — once landed, `toP1` should be re-expressed over `ℳ X`/
  `MeroGermOn`'s `evalAt` rather than a bespoke `limUnder`, and this unit's `ToP1.lean` becomes a
  thin wrapper. Also flags the blueprint DAG correction (§0.2) for the orchestrator to apply to
  `clean_room_blueprint.md`'s meromorphic-trace entry.
