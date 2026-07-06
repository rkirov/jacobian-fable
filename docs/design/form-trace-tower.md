# Design: form-trace-tower (`Jacobian/FormTrace/`)

Blueprint unit **form-trace-tower**. Blueprint text: "Fibrewise trace tower for pair forms
`h·ω₀` along `f : X → ℙ¹`: fibre traces, branch handling, coherent selection, globalization, and
rationality of the traced form. This is the Gate-A reduction machinery feeding the residue
theorem and Serre. Read: Forster §17; Miranda Ch. VI. Strategy: push a meromorphic 1-form down
to `ℙ¹` as an honest rational form; its residues are the ones you sum." Declared **Builds on:**
meromorphic-trace.

Everything below verified against pinned mathlib `548398201a64f3a5127d90d83945278cfe38cac4` by
reading source, and against the *actual built state* of upstream units (not just their design
docs) by reading their files on disk. `meromorphic-trace` (`Jacobian/MeromorphicTrace/`) is
**mid-build at design time**: `ToP1.lean`/`OrderMultiplicity.lean`/`PlanarTrace.lean` exist on
disk but are not yet sorry-free (see §0.4). This design is written against mtrace's *design doc*
plus the *actual current file contents*, with an explicit adapter note for the one place where
this matters (§7 Risk 1). One gated end spike (`scratch_ftt.lean`, §9) compiled clean.

---

## 0. Scope, citation corrections, and a DAG audit

### 0.1 The citation correction: Miranda Ch. VI does NOT contain "trace"

The task brief's own citation ("Miranda Ch. VI, PDF 181–206, eq. 3.2 at PDF 198") was checked
directly against the PDF. **Miranda Ch. VI §3 never constructs a trace along a map to `ℙ¹`.**
Its "Residue Map" subsection (book p. 186 = PDF 198) simply *cites* "the Residue Theorem"
(`Σ_p Res_p(r_p·ω) = 0`, eq. (3.2), confirming mtrace's own §0.3 citation correction) as an
already-available black box and builds the Serre pairing `Res : L⁽¹⁾(−D) → H¹(D)*` directly on
`X`, at whatever genus. No push-to-`ℙ¹` construction appears anywhere in Ch. VI.

**The actual mathematical home of "trace along `F : X → Y`" is Miranda Ch. VIII §3, "Trace
Operations" (book pp. 251–256 = PDF 263–268)**, in the chapter on **Abel's Theorem**, used there
for the *necessity* direction of Abel's theorem (`div(f) = D` principal `⟹ A₀(D) = 0`). This is
confirmed by mtrace's own design doc (§0.3): "the 'trace' vocabulary Miranda actually uses for
functions (`Tr_f`) is in Ch. VIII §3 ..., not Ch. VI." Read in full (§9 below records the exact
page content); its four ingredients are exactly the four numbered items in the task brief:

1. **Trace of a function** (book 251–252): `Tr(h)(q) = Σ_{p∈F⁻¹(q)} h(p)` away from branch
   points; at a branch point with a *single* preimage of multiplicity `m`, local model `z = w^m`,
   `h(w) = Σ_n c_n w^n` gives (their computation, using a primitive `m`-th root `ζ` and the
   vanishing-geometric-sum trick) `Tr(h)(z) = Σ_k m·c_{km}·z^k` — **this is *exactly* mtrace's
   `traceZk`/`laurentCoeffAt_traceZk` formula** (`laurentCoeffAt (traceZk h k) 0 m =
   k·laurentCoeffAt h 0 (k·m)`, mtrace design §4.4), with Miranda's `m` = mtrace's `k` and
   Miranda's summation index `k` = mtrace's `m`. Confirms mtrace's own design is the correct
   formalization of this classical computation.
2. **Trace of a 1-form** (book 252–253, eq. (3.1)): writing `ω = h(w)dw` and using
   `dz = m·w^{m-1}dw`, they get `Tr(ω) = Σ_k c_{km-1}·z^{k-1}dz` — **no factor of `m` this time**,
   and an index *shift by `m-1`* relative to the function formula. This is exactly the "Jacobian
   factor `k·w^{k-1}` bookkeeping" the task brief asks to be designed; §2 D3 below derives it
   cleanly as a corollary of mtrace's own function-trace formula, confirming *why* the `m`
   cancels (their derivation re-does the geometric-sum argument from scratch; ours reuses
   mtrace's `laurentCoeffAt_traceZk` + the built residue-calculus shift lemma
   `laurentCoeffAt_zpow_mul` — cheaper, and the `traceZkForm := traceZk` factorization it yields
   is a genuinely small, non-classical simplification).
3. **The residue of a trace, Lemma 3.2** (book 253): `Res_q(Tr(ω)) = Σ_{p∈F⁻¹(q)} Res_p(ω)` —
   the task brief's item 3, THE central theorem of this unit (§2 D3, §5 P-main).
4. **"An Algebraic Proof of the Residue Theorem"** (book 253–254): using the trace to give an
   *alternative*, Stokes-free proof of `Σ_p Res_p(ω) = 0` on **any** compact Riemann surface, by
   (a) choosing *any* nonconstant `f : X → ℙ¹`, (b) tracing `ω` down to a *rational* 1-form on
   `ℙ¹` (any rational function decomposes into partial fractions, and `Σ Res = 0` for each
   elementary piece `c(z−a)ⁿdz` is checked by hand — three cases, `n ≤ −2` / `n = −1` / `n ≥ 0`),
   (c) applying Lemma 3.2 twice (sum over `q`, then over `p` in each fibre). This is **exactly**
   the task brief's "cheap base case" — see §0.3 for its ownership.
5. **"Integration of a Trace"** (book 254–255) and the **necessity half of Abel's theorem**
   (book 255–256): the trace of a *holomorphic* form is holomorphic on `ℙ¹`, hence `≡ 0` since
   `ℙ¹` has genus `0` — literally the sentence "since `C_∞` has genus `0`, there are no nonzero
   holomorphic 1-forms on `C_∞`. Hence `Tr(ω_j) = 0` for each `j`." **This fact is already fully
   proved in this repository**: `RS.P1.form1_eq_zero`/`RS.genus_onePoint`
   (`Jacobian/ProjectiveLine/GenusZero.lean`, built, zero sorries). §2 D4/§4.4 below wire our
   trace tower to it directly — this is almost certainly the actual "Gate-A" payload Miranda's
   route would want handed to Abel's theorem, more directly than the rational-partial-fraction
   machinery of item 4.

### 0.2 Forster's parallel material does not use trace either

Forster §17 (Serre duality, PDF 138–144, read in full) parallels Miranda Ch. VI: Mittag-Leffler
distributions of forms, `Res(μ) = Res([δμ])` (Thm 17.3, proved by a **partition-of-unity/Stokes**
argument, not a trace), the sheaves `Ω_D`, and the duality pairing — again, no push to `ℙ¹`.
Forster's own residue theorem (§10, Thm 10.21) and his Abel's theorem (§20, "weak solutions" +
chain/1-cycle machinery, `docs/refs/forster-map.md` confirms no monodromy-based trace there
either) are both genuinely different, dissection-free routes that this project's blueprint has
*chosen* over Miranda's trace-based ones for the top-level theorems (`residue-theorem` unit:
PoU + planar Stokes; `abel-theorem` unit: Forster's dissection-free §20.7). **This does not make
form-trace-tower's Miranda-VIII.3 content useless** — the blueprint's own `Builds on` edge wires
it to `abel-weak-solutions` (see §0.3), and the object itself (traced pair-forms, chart-invariant
local residues) is the natural, reusable "Gate-A" atom the blueprint blurb describes, independent
of which specific downstream proof consumes which piece of it.

### 0.3 DAG audit: who actually needs what (a load-bearing finding)

Re-reading `clean_room_blueprint.md`'s `Builds on:` edges (not just the prose blurbs) gives:

- `form-trace-tower` — **Builds on: meromorphic-trace** (only).
- `abel-weak-solutions` — **Builds on: form-trace-tower, monodromy, planar-stokes-atoms.**
- `residue-theorem` — **Builds on: canonical-forms, planar-stokes-atoms.** Its own strategy text:
  "cover `X`, write the form as a sum of locally-supported pieces, apply planar Stokes to each" —
  **no mention of a push to `ℙ¹`.** This is Forster's route (§0.2), not Miranda's.
- `laurent-tails` — **Builds on: canonical-forms, meromorphic-trace.** Not form-trace-tower.
- `serre-duality-tails` — **Builds on: laurent-tails, proper-map-degree, residue-theorem,
  serre-duality-cech.** Not form-trace-tower, and (per the reading in §0.1) Miranda's *own* Ch.
  VI development doesn't need a trace-to-`ℙ¹` step either — it consumes `Σ Res = 0` as an
  imported black box, supplied here by `residue-theorem`'s independent Stokes route.

**Conclusion (mirrors mtrace's own §0.2 DAG-correction pattern): the blueprint blurb's phrase
"feeding the residue theorem and Serre" oversells what the frozen `Builds on:` edges actually
wire up.** The *only* consumer this unit is DAG-required to feed is `abel-weak-solutions`. The
"rationality of the traced form" and "cheap `Σ Res = 0` on `ℙ¹`" content (task item 2, item 4)
is real, cheap, and worth building (it is exactly Miranda's own algebraic-proof ingredient, and a
natural closure fact for this unit), but **no currently-designed unit is blocked on it** — flagged
explicitly in §7/§8 so no downstream builder mistakenly waits on it, and so this unit's own
builder does not over-invest in it relative to the one genuinely wired theorem (§0.1 item 3, the
residue-trace compatibility, needed — see below — for `abel-weak-solutions`'s Miranda-flavored
sub-arguments, and for item 5's `jacobian-functoriality` interface, itself not a current
blueprint unit — see §0.5).

Action: no blueprint edit filed (unlike mtrace's §0.2, this is not a *missing* edge, just a
prose/strategy-text mismatch already partially self-corrected by the blueprint's own routing
warnings in its final section — noted here for the orchestrator's awareness, no action needed).

### 0.4 What "builds on meromorphic-trace" means when mtrace is mid-build

Read directly off disk at design time (`Jacobian/MeromorphicTrace/*.lean`, all three files
present, **no root `Jacobian/MeromorphicTrace.lean` yet**):

- `ToP1.lean` (312 lines): `toP1`, `toP1_contMDiff`, `toP1_not_const` — **zero sorries** (all
  proved). Irrelevant to this unit (cluster 1, the argument principle — we need cluster 2).
- `OrderMultiplicity.lean` (130 lines): `multiplicity_toP1_of_ordAtX_pos` proved;
  `multiplicity_toP1_of_ordAtX_neg` and `multiplicity_toP1_of_ordAtX_eq_zero` **have `sorry`s**.
  Irrelevant to this unit (cluster 1 again).
- `PlanarTrace.lean` (384 lines, cluster 2, the one we need): `traceZk`, `traceZk_eq_finset_sum`,
  `traceZk_zero_apply`, `traceZk_add`, `traceZk_const_mul`, `traceZk_comp_pow`,
  `analyticAt_traceZk` (P4), `meromorphicAt_traceZk` (P5) — **all fully proved, zero sorries**.
  `laurentCoeffAt_traceZk` (P6, the Laurent-coefficient formula) — **has a `sorry`**, with an
  in-file comment recording two attempted-but-incomplete routes and explicitly deferring
  `resAt_traceZk`/`ordAt_traceZk_ge` as consequences not yet stated. `FunctionTrace.lean`
  (mtrace's own global `Tr_F h` assembly, file 5 of its plan) **does not exist yet on disk.**

**This is the single load-bearing external dependency of the whole unit** (§7 Risk 1 elaborates):
everything about *existence* of the trace tower (meromorphy, the "same object as `traceZk`"
factorization) is available today; everything about the *exact coefficient/residue values*
(Miranda eq. 3.1, Lemma 3.2, and hence this unit's own central theorem) is currently blocked on
mtrace's P6 landing. §5/§7 design the dependency so that as much as possible is buildable *now*.

### 0.5 "jacobian-functoriality (#33)": no such blueprint unit exists

Searched `clean_room_blueprint.md` exhaustively: there is no unit named `jacobian-functoriality`,
and the blueprint lists exactly 30 units (through `period-lattice-rank`), so "#33" is out of
range of the current blueprint. The only place this content is discussed is
`docs/design/jacobian-construction.md` §9.4/§10 (read in full), which explicitly flags a
**blueprint gap**: constructing `Jacobian.pushforward`/`pullback` for a specific holomorphic
`f : X → Y` needs "pullback-of-forms `f^* : Form1 Y →ₗ[ℂ] Form1 X`... and the functoriality
lemmas `pushforward_id_apply`/`pushforward_comp_apply`/`pushforward_pullback`. **No blueprint unit
explicitly owns this**... some unit (a new one, or an addendum...) must own 'pullback of
holomorphic 1-forms along a holomorphic map' and the period-naturality lemma." This is almost
certainly the referent of "jacobian-functoriality (#33)" in the task brief — a *future*,
not-yet-designed unit. §2 D5 and §4.6 design the interface this unit *can* hand to it (Miranda's
own Problems VIII.3.B/D/F, read directly off the page — projection-formula-shaped facts,
buildable now from mtrace's already-proved `traceZk_comp_pow`), flagged as forward-looking,
non-blocking exports (no current consumer is DAG-wired to them).

---

## 1. Facts relied on (verified against files on disk)

**Built, zero-sorry, consumed as-is:**

- `RS.resAt`, `RS.laurentCoeffAt`, `RS.resAt_congr`, `RS.resAt_fun_add`, `RS.resAt_fun_sum`,
  `RS.resAt_const_mul`, `RS.laurentCoeffAt_congr`, `RS.laurentCoeffAt_const_mul`,
  `RS.laurentCoeffAt_zpow_mul` (`(hg)(m k : ℤ) : laurentCoeffAt (fun z => (z-z₀)^m*g z) z₀ k =
  laurentCoeffAt g z₀ (k-m)`) — `Jacobian/ResidueCalculus/{Residue,LaurentCoeff}.lean`.
- `RS.resAt_comp_mul_deriv {φ}(hφ : AnalyticAt ℂ φ w₀)(hφ' : deriv φ w₀ ≠ 0)(hφ₀ : φ w₀ = z₀)
  (hf : MeromorphicAt f z₀) : resAt (fun w => f (φ w) * deriv φ w) w₀ = resAt f z₀` —
  `Jacobian/ResidueCalculus/ChangeOfVariables.lean` — **the** chart-invariance atom (item 1).
- `RS.MeromorphicAt.exists_principalPart_add_analyticAt`, `RS.principalPartAt`,
  `RS.meromorphicAt_principalPartAt`, `RS.eq_principalPart_of_eventuallyEq` —
  `Jacobian/ResidueCalculus/PrincipalPart.lean` — the Mittag-Leffler-style decomposition item 4
  reuses (finite case).
- `RS.analyticAt_transition {e e'}(he he'){x}(hx hx') : AnalyticAt ℂ (e'∘e.symm) (e x) ∧
  deriv (e'∘e.symm) (e x) ≠ 0` — `Jacobian/LocalMultiplicity/ChartBridge.lean` — the exact
  hypothesis-producer for `resAt_comp_mul_deriv`; already the engine behind the ALREADY-BUILT
  `RS.ordAtX_eq_of_mem_source` (`Jacobian/Meromorphic/Predicates.lean:272`), whose proof is the
  literal template for item 1's chart-invariance proof (§5 P1).
- `RS.AdaptedChartsAt F x k` (fields `e`,`e'`,`radius`,`map_eq_zero`,`map_eq_zero'`,`target_eq`,
  `target_eq'`,`eqOn_pow : ∀ z ∈ e.source, e' (F z) = e z ^ k`), `RS.exists_adaptedChartsAt` —
  `Jacobian/LocalMultiplicity/AdaptedCharts.lean`.
- `RS.FiberStack F y₀` (fields `n`,`pt`,`pt_injective`,`range_pt`,`one_le_mult`,`A`,
  `disjoint_sources`,`V`,...), `RS.exists_fiberStack`, `RS.fiberMultSum_eq_degree`, `RS.degree`,
  `RS.multiplicity` — `Jacobian/MappingDegree/{LocalStructure,Degree,Basics}.lean`.
- `RS.MeromorphicAtX`, `RS.MeromorphicOnX`, `RS.ordAtX`, `RS.ordAtX_eq_of_mem_source`,
  `RS.meromorphicAtX_iff_of_mem_source` — `Jacobian/Meromorphic/Predicates.lean`.
- `RS.ℳ X` (`GermSpace.lean`), `RS.finite_support_divisor`, `RS.divisorOn`, `RS.evalAt`,
  `RS.holoRepr` (`OrderEval.lean`, `Divisor.lean`) — **fully built**, more complete than mtrace's
  own design doc assumed at ITS design time; usable directly if a full `ℳ (OnePoint ℂ)`-level
  statement of item 4 is wanted (design below uses the cheaper planar-only route instead, see D5).
- `RS.P1.coeChart`, `RS.P1.invChart`, `chartAt_coe`, `chartAt_infty`, `RS.P1.form1_eq_zero`,
  `RS.genus_onePoint`, `RS.P1.contMDiffAt_of_pole`, `RS.P1.ContMDiffAt.onePointCoe` —
  `Jacobian/ProjectiveLine/{Charts,GenusZero,Holomorphy}.lean` — **all built**, more complete than
  mtrace's design doc assumed (its `Holomorphy.lean` has since landed).
- `RS.Form1`, `RS.Form1CoeffData`, `RS.Form1.ofCoeffs`, `RS.Form1.coeffIn_ofCoeffs`, `RS.coeffIn`,
  `RS.coeffIn_trans` — `Jacobian/Forms/{Basic,OfCoeffs,Coeffs}.lean` (per
  `docs/design/holomorphic-forms.md`; spike-verified there, not re-verified here).
- `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` —
  `Mathlib/Analysis/Complex/Liouville.lean:44` — the Cauchy-estimate atom for item 4's
  "polynomial-growth entire ⟹ polynomial" lemma (not itself in mathlib as a packaged theorem —
  checked, see §5 P-rational).

**mtrace, partially built (see §0.4):** `RS.MTrace.traceZk`, `RS.MTrace.traceZk_comp_pow`,
`RS.MTrace.analyticAt_traceZk`, `RS.MTrace.meromorphicAt_traceZk` — zero-sorry, used as-is.
`RS.MTrace.laurentCoeffAt_traceZk` — **sorry'd**, used only where flagged. `RS.MTrace.trace`
(`Tr_F h`, `FunctionTrace.lean`) — **not yet written**; this unit's global assembly (§2 D2) is
designed to be the *same formula* mtrace's own design doc already specifies for it (§2 D7 there),
so once `FunctionTrace.lean` lands, no rework is needed here beyond an import line.

---

## 2. Core definitional decisions

### D1 — The pair-form scope: `ω₀ := F^*(dz)`, no new form type

The blueprint's general pair convention is `h·ω₀` for an arbitrary fixed reference form `ω₀`.
Meromorphic 1-forms have no type yet (owned by the not-yet-designed `canonical-forms` unit, #18,
"meromorphic 1-form systems"). Building that general system here would be badly out of scope.

**Decision**: this unit only ever needs pair-forms whose reference is the pullback of the
target's *own* coordinate differential along the map being traced — i.e. `ω = h·F^*(dz)` for
`F : X → Y` (specialized to `Y := OnePoint ℂ` for the global trace-tower content, general `Y` for
the local residue definition, since it costs nothing extra). **No new Lean structure is
introduced**: a "pair-form along `F`" is *just* its coefficient function `h : X → ℂ`; the
reference `F^*(dz)` is implicit, fixed once `F` is fixed, and never reified. This mirrors mtrace's
own convention for `Tr_F h` (bare `h : X → ℂ`, no wrapper) and is consistent with
`docs/design/holomorphic-forms.md`'s explicit ruling ("meromorphic 1-forms are later pairs
`(f,η)` ~ `f•η`... do not add meromorphic sections to this [Forms] unit").

**Scope boundary, documented honestly**: this does *not* give a way to trace `h·ω` for an
*arbitrary* meromorphic `ω` (e.g. a canonical form `K`) that is not of the shape `F^*(dz)` — that
would need `canonical-forms`'s future general system. Per §0.3, no current unit needs that more
general operation from us, so this is not a live blocker.

### D2 — The pair-form residue `resAtX` and its chart-invariance (task item 1)

For `F : X → Y` (any target manifold satisfying the standing hypotheses) and `h : X → ℂ`:

```lean
namespace RS.FormTrace

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- The residue at `x` of the pair-form `h · F^*(dz)`, read in the PREFERRED chart at `x` (and
the preferred chart at `F x` for the target coordinate). Chart-independence: `resAtX_eq_of_mem_source`
below — may equivalently be read in ANY pair of maximal-atlas charts. -/
noncomputable def resAtX (F : X → Y) (h : X → ℂ) (x : X) : ℂ :=
  resAt (fun z => h ((chartAt ℂ x).symm z) *
    deriv (chartAt ℂ (F x) ∘ F ∘ (chartAt ℂ x).symm) z) (chartAt ℂ x x)
```

The `deriv(chartAt ℂ (F x) ∘ F ∘ (chartAt ℂ x).symm)` factor is exactly `F^*(dz)`'s coefficient
in the `x`-chart (the same "coefficient of a pulled-back differential" computation
`holomorphic-forms.md`'s `coeffIn_trans` uses for honest `Form1`s, specialized to the meromorphic,
one-chart-pair setting we can afford here without a `Form1`-meromorphic type).

```lean
/-- Chart-invariance (task item 1): `resAtX` may be computed in ANY maximal-atlas chart pair. -/
theorem resAtX_eq_of_mem_source {F : X → Y} {h : X → ℂ} {x : X}
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    (hx : x ∈ e.source) {e' : OpenPartialHomeomorph Y ℂ}
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Y) (hFx : F x ∈ e'.source)
    (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x) (hh : MeromorphicAtX h x) :
    resAtX F h x = resAt (fun z => h (e.symm z) * deriv (e' ∘ F ∘ e.symm) z) (e x)
```

Proof plan in §5 P1 (mirrors the ALREADY-BUILT `RS.ordAtX_eq_of_mem_source` proof, extended with
a second `analyticAt_transition`/`resAt_comp_mul_deriv` application on the `Y` side).

### D3 — `traceZkForm`: the Jacobian-weighted planar atom (task item 2's local model)

**The key simplification** (found via the derivation in §0.1 item 2, verified mechanically in the
spike, §9): if the ADAPTED-chart coefficient of a pair-form is written with its Jacobian factor
*explicit* — `h_adapted(w) := h(w)·k·w^{k-1}` for `h : X → ℂ` the AMBIENT coefficient against
`F^*(dz)` and `k` the local multiplicity — then dividing back out by that same factor to get the
downstairs coefficient (Miranda's construction, eq. (3.1)) is **literally mtrace's own function
trace `traceZk`, unweighted**:

```lean
/-- The Jacobian-weighted planar trace atom: divides the `k·w^{k-1}` Jacobian factor of
`F^*(dz)` back out before applying mtrace's `traceZk`. -/
noncomputable def traceZkForm (h : ℂ → ℂ) (k : ℕ) (w : ℂ) : ℂ :=
  RS.MTrace.traceZk (fun v => h v * ((k : ℂ) * v ^ ((k : ℤ) - 1))⁻¹) k w

/-- The cancellation identity (spike-verified, Fact 1): applying `traceZkForm` to a coefficient
that ALREADY carries the Jacobian factor recovers the bare `traceZk` of the un-weighted function
exactly — this is why "trace of the pair-form `h·F^*dz`" needs NO new global object: its
coefficient function IS `RS.MTrace.trace F h`. -/
theorem traceZkForm_hAdapted_eq {g : ℂ → ℂ} (k : ℕ) (hk : k ≠ 0) :
    traceZkForm (fun v => g v * (k : ℂ) * v ^ ((k : ℤ) - 1)) k = RS.MTrace.traceZk g k := by
  unfold traceZkForm; congr 1; funext v
  rw [mul_inv, ← zpow_neg]
  -- pointwise cancellation, unconditional (no `v ≠ 0` needed — `mul_inv`/`zpow_neg` hold at `0`
  -- too by the `0⁻¹ = 0` convention); see the spike (§9, Fact 1) for the fully closed proof.
```

**Consequence** (the resolution of the "does form-trace-tower need a NEW global trace object"
question): it does **not**. `RS.MTrace.trace F h : Y → ℂ` (mtrace's own, already-designed
`Tr_F h`, D7 of the mtrace design doc) is EXACTLY the coefficient function of `Tr(h·F^*dz)` in the
target's preferred chart. This unit's own new content is (a) `resAtX`/chart-invariance (D2), (b)
`traceZkForm` as an internal *proof device* used only to derive the Laurent-coefficient/residue
identities below (not exposed as a competing "trace of forms" definition), and (c) the
residue-trace compatibility theorem itself (D4).

**The Laurent-coefficient formula and its residue corollary** (task item 2's "Jacobian factor
bookkeeping", ⚠ **gated on mtrace's P6**, see §0.4/§7):

```lean
theorem laurentCoeffAt_traceZkForm (hh : MeromorphicAt h 0) (hk : k ≠ 0) (j : ℤ) :
    laurentCoeffAt (traceZkForm h k) 0 j = laurentCoeffAt h 0 (k * j + ((k : ℤ) - 1))

/-- Miranda Lemma 3.2, LOCAL case (single preimage): the residue is preserved EXACTLY (no factor
of `k` — the Jacobian factor exactly cancels mtrace's `k`-multiplier at the residue index `j=-1`).
Spike-verified (Fact 2, given P6 as a hypothesis): the derivation chain compiles end-to-end. -/
theorem resAt_traceZkForm (hh : MeromorphicAt h 0) (hk : k ≠ 0) :
    resAt (traceZkForm h k) 0 = resAt h 0 := by
  have := laurentCoeffAt_traceZkForm hh hk (-1)
  simpa [resAt] using this
```

Both facts are provable *unconditionally in `k`* (need only `k ≠ 0`) and both **existence**
theorems below (which do NOT need P6) already give the qualitative shape:

```lean
/-- Existence of meromorphy: builds ONLY on mtrace's already-proved `meromorphicAt_traceZk` (P5,
zero sorries) — NOT gated on P6. -/
theorem meromorphicAt_traceZkForm (hh : MeromorphicAt h 0) (hk : k ≠ 0) :
    MeromorphicAt (traceZkForm h k) 0 :=
  RS.MTrace.meromorphicAt_traceZk (hh.mul (((zpow_meromorphicAt (k:ℤ) (-1) ...)) -- Compat helper,
    -- (k:ℂ)⁻¹ constant times `v^(-(k-1))`, meromorphic at `0` unconditionally in the sign of
    -- `k - 1`) hk    -- see §5 for the exact compat lemma name
```

### D4 — `resAtP1` and the residue-trace compatibility (task item 3, the central theorem)

Since the global trace-tower content always specializes `Y := OnePoint ℂ`, introduce the
simpler, Jacobian-factor-free residue on `ℙ¹` itself (its own coordinate paired against itself —
`deriv id = 1` — so no Jacobian bookkeeping is needed at this level):

```lean
/-- Residue at `y₀ : ℙ¹` of a function `R : ℙ¹ → ℂ`, viewed as the coefficient of `R·dz`. -/
noncomputable def resAtP1 (R : OnePoint ℂ → ℂ) (y₀ : OnePoint ℂ) : ℂ :=
  resAt (R ∘ (chartAt ℂ y₀).symm) (chartAt ℂ y₀ y₀)

theorem resAtP1_eq_resAtX_id (R : OnePoint ℂ → ℂ) (y₀ : OnePoint ℂ) :
    resAtP1 R y₀ = resAtX (id : OnePoint ℂ → OnePoint ℂ) R y₀ := by
  unfold resAtP1 resAtX; simp
```

**THE main theorem** (Miranda Lemma 3.2, globalized over an arbitrary fibre via `FiberStack`):

```lean
theorem resAtP1_trace_eq_sum {F : X → OnePoint ℂ} (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) {h : X → ℂ} (hh : MeromorphicOnX h Set.univ)
    {y₀ : OnePoint ℂ} (S : RS.FiberStack F y₀) :
    resAtP1 (RS.MTrace.trace F h) y₀ = ∑ i, resAtX F h (S.pt i)
```

Full proof plan (≥ 40 lines): §5 P-main.

### D5 — `ℳ(ℙ¹)`, rationality, and the ownership decision (task item 4)

**Decision (cheapest honest route for item 4's stated need, matching the task's candidate
(b)):** do **not** build a `ℳ(ℙ¹) ≃ RatFunc ℂ` ring isomorphism (heavier than needed, and
mathlib's `RatFunc` is a formal-fraction-field construction with no a-priori bridge to
`MeromorphicAt`/analytic data — would need its own analytic-realization lemma, strictly more work
for no extra payoff here). Instead: a **finite-pole partial-fraction existence** statement,
built by (1) isolating the finitely many poles via the SAME "compact ⟹ finite poles" argument
`RS.finite_support_divisor` already proves for general `X` (reusable *as-is* for `X := OnePoint
ℂ`, since `ℙ¹` already carries every standing instance the general lemma needs — no
re-derivation), (2) subtracting each pole's `RS.principalPartAt` (already built,
`ResidueCalculus/PrincipalPart.lean`) to leave an entire remainder, (3) a **new, small, locally
provable** compat lemma "entire + polynomial growth ⟹ polynomial" (not found in mathlib — checked,
§1), via the Cauchy-estimate `norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` (built) letting
the sphere radius `R → ∞`. Full plan: §5 P-rational.

**Ownership** (per §0.3's DAG audit): this fact is **not** needed by `residue-theorem` or
`serre-duality-tails` (both have independent, already-wired routes to `Σ Res = 0`/the Serre
residue functional). It **is** exactly Miranda's own "algebraic proof of the residue theorem"
ingredient (§0.1 item 4) and is offered here as a documented, self-contained, non-load-bearing
bonus corollary — built if time allows, explicitly **not** blocking any currently-designed unit if
deprioritized (own it here, flag it, do not let it hold up D2–D4).

**The cheaper, more likely load-bearing fact (task item 5's "5"/§0.1 item 5):** tracing a
*holomorphic* pair-form gives a holomorphic function on `ℙ¹`, hence `≡ 0` by the ALREADY-BUILT
`RS.P1.form1_eq_zero`/`RS.genus_onePoint` — no partial fractions needed at all:

```lean
theorem trace_eq_zero_of_holomorphic {F : X → OnePoint ℂ} (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) {h : X → ℂ} (hh : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω h) :
    RS.MTrace.trace F h = fun _ => 0
```

Proof plan: §5 P-holomorphic. This is (almost certainly) THE fact Miranda's own necessity-of-Abel
argument needs handed to `abel-weak-solutions`, matching the literal sentence quoted in §0.1
item 5 far more directly than the general partial-fraction machinery.

---

## 3. File plan

| # | File | Content | Est. | Imports beyond stdlib/mathlib |
|---|------|---------|------|-------------------------------|
| 1 | `FormTrace/PairForm.lean` | `resAtX` (D2), `resAtX_eq_of_mem_source`, basic algebra (`resAtX_add`, `resAtX_const_mul`, `resAtX_congr`) | ~180 | `Jacobian.ResidueCalculus.ChangeOfVariables`, `Jacobian.LocalMultiplicity.ChartBridge`, `Jacobian.Meromorphic.Predicates` |
| 2 | `FormTrace/TraceZkForm.lean` | `traceZkForm` (D3), cancellation identity, `meromorphicAt_traceZkForm` (unconditional), `laurentCoeffAt_traceZkForm`/`resAt_traceZkForm` (⚠ gated on mtrace P6) | ~230 | `Jacobian.MeromorphicTrace.PlanarTrace`, `Jacobian.ResidueCalculus.{LaurentCoeff,Residue}` |
| 3 | `FormTrace/ResidueTraceCompat.lean` | `resAtP1` (D4), **`resAtP1_trace_eq_sum`** (the main theorem), the functoriality/projection-formula facts (§4.6, task item 5) | ~260 | files 1–2, `Jacobian.MeromorphicTrace.FunctionTrace` (once it lands; see §7 Risk 1 for the interim adapter), `Jacobian.MappingDegree.LocalStructure` |
| 4 | `FormTrace/HolomorphicVanishing.lean` | `trace_eq_zero_of_holomorphic` (D5, the likely `abel-weak-solutions` payload) | ~120 | files 1–3, `Jacobian.Forms.OfCoeffs`, `Jacobian.ProjectiveLine.GenusZero` |
| 5 | `FormTrace/RationalOnP1.lean` | Partial-fraction decomposition on `ℙ¹` + elementary `Σ Res = 0` base case (D5, flagged non-load-bearing bonus) | ~220 | files 1–3, `Jacobian.ResidueCalculus.PrincipalPart`, `Jacobian.Meromorphic.Divisor`, `Mathlib.Analysis.Complex.Liouville` |
| 6 | `Jacobian/FormTrace.lean` | unit root, API docstring | ~30 | all |

Build waves: **file 1 is fully independent** of mtrace's build state (only needs the frozen
`ResidueCalculus`/`LocalMultiplicity`/`Meromorphic` units) — build it first, regardless of
mtrace's progress. File 2's *definition* and *existence* theorems only need mtrace's already-proved
`traceZk`/`meromorphicAt_traceZk` (stable today); its coefficient-formula theorems are gated on P6
landing (§7). Files 3–4 need file 2's residue corollary (hence indirectly gated on P6) plus
mtrace's `FunctionTrace.lean` (not yet on disk). File 5 is independent of mtrace entirely (pure
`ℙ¹`/`ResidueCalculus`/`Meromorphic.Divisor` content) — buildable any time, lowest priority.

---

## 4. Exports (exact signatures)

Everything in `namespace RS.FormTrace` unless noted. Standing variables as in D2/D4.

### 4.1 `PairForm.lean`

```lean
noncomputable def resAtX (F : X → Y) (h : X → ℂ) (x : X) : ℂ                          -- D2

theorem resAtX_eq_of_mem_source {F h x} {e} (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) (hx : x ∈ e.source)
    {e'} (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω Y) (hFx : F x ∈ e'.source)
    (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x) (hh : MeromorphicAtX h x) :
    resAtX F h x = resAt (fun z => h (e.symm z) * deriv (e' ∘ F ∘ e.symm) z) (e x)

theorem resAtX_congr {F h h' x} (hh : h =ᶠ[𝓝[≠] x] h') : resAtX F h x = resAtX F h' x
theorem resAtX_add {F h h' x} (hh : MeromorphicAtX h x) (hh' : MeromorphicAtX h' x) :
    resAtX F (h + h') x = resAtX F h x + resAtX F h' x
theorem resAtX_const_mul (c : ℂ) {F h x} : resAtX F (fun y => c * h y) x = c * resAtX F h x
```

### 4.2 `TraceZkForm.lean`

```lean
noncomputable def traceZkForm (h : ℂ → ℂ) (k : ℕ) (w : ℂ) : ℂ                          -- D3

theorem traceZkForm_hAdapted_eq {g} (k) (hk : k ≠ 0) :
    traceZkForm (fun v => g v * (k:ℂ) * v ^ ((k:ℤ) - 1)) k = RS.MTrace.traceZk g k

theorem meromorphicAt_traceZkForm (hh : MeromorphicAt h 0) (hk : k ≠ 0) :
    MeromorphicAt (traceZkForm h k) 0                                                  -- NOT gated

theorem laurentCoeffAt_traceZkForm (hh : MeromorphicAt h 0) (hk : k ≠ 0) (j : ℤ) :
    laurentCoeffAt (traceZkForm h k) 0 j = laurentCoeffAt h 0 (k * j + ((k:ℤ) - 1))     -- ⚠ P6

theorem resAt_traceZkForm (hh : MeromorphicAt h 0) (hk : k ≠ 0) :
    resAt (traceZkForm h k) 0 = resAt h 0                                               -- ⚠ P6
```

### 4.3 `ResidueTraceCompat.lean`

```lean
noncomputable def resAtP1 (R : OnePoint ℂ → ℂ) (y₀ : OnePoint ℂ) : ℂ                    -- D4
theorem resAtP1_eq_resAtX_id (R y₀) : resAtP1 R y₀ = resAtX (id : OnePoint ℂ → OnePoint ℂ) R y₀

/-- THE main theorem (task item 3 / Miranda Lemma 3.2, globalized). ⚠ gated on P6 (via
`resAt_traceZkForm`) and on mtrace's `FunctionTrace.lean` (for `RS.MTrace.trace` itself). -/
theorem resAtP1_trace_eq_sum {F : X → OnePoint ℂ} (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) {h : X → ℂ} (hh : MeromorphicOnX h Set.univ)
    {y₀ : OnePoint ℂ} (S : RS.FiberStack F y₀) :
    resAtP1 (RS.MTrace.trace F h) y₀ = ∑ i, resAtX F h (S.pt i)

-- Task item 5 / §0.5, §4.6: projection-formula facts for the future `jacobian-functoriality`
-- unit, Miranda Problems VIII.3.B/D/F. NOT gated on P6 (pure `traceZk_comp_pow` + FiberStack sum).
theorem trace_const_mul_pullback {F : X → OnePoint ℂ} (hF) (hne) {g : OnePoint ℂ → ℂ} (h : X → ℂ)
    (hg : ∀ y, MeromorphicAtX g y) (hh : MeromorphicOnX h Set.univ) :
    RS.MTrace.trace F (fun x => g (F x) * h x) = fun y => g y * RS.MTrace.trace F h y

theorem trace_pullback_eq_degree_smul {F : X → OnePoint ℂ} (hF) (hne) (g : OnePoint ℂ → ℂ)
    (hg : ∀ y, MeromorphicAtX g y) :
    RS.MTrace.trace F (fun x => g (F x)) = fun y => (RS.degree F : ℂ) * g y
```

### 4.4 `HolomorphicVanishing.lean`

```lean
theorem trace_eq_zero_of_holomorphic {F : X → OnePoint ℂ} (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) {h : X → ℂ} (hh : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω h) :
    RS.MTrace.trace F h = fun _ => 0
```

### 4.5 `RationalOnP1.lean` (flagged non-load-bearing, §0.3/D5)

```lean
/-- A "meromorphic-on-`ℙ¹`" coefficient given planar (avoids `ℳ (OnePoint ℂ)` packaging): `R`
meromorphic at every finite point, and meromorphic at `∞` via the inversion chart. -/
structure MeroOnP1 (R : ℂ → ℂ) : Prop where
  mero : ∀ z, MeromorphicAt R z
  mero_infty : MeromorphicAt (fun w => R w⁻¹) 0

theorem exists_partialFraction {R} (hR : MeroOnP1 R) :
    ∃ (S : Finset ℂ) (c : ℂ → ℤ →₀ ℂ) (P : Polynomial ℂ),
      (∀ a ∈ S, ∀ n ∈ (c a).support, n < 0) ∧
      ∀ᶠ z in Filter.cofinite, R z = P.eval z + ∑ a ∈ S, ∑ n ∈ (c a).support, c a n * (z - a) ^ n

/-- The cheap base case (task item 2/item 4): `Σ Res = 0` for a rational (elementary) piece,
verified by direct case split — no Stokes, no partition of unity. -/
theorem sum_resAtP1_partialFraction_eq_zero {R} (hR : MeroOnP1 R)
    (hpacked : (* the `OnePoint ℂ → ℂ` lift of `R`, agreeing with `R`/`R∘inv` on each chart *)) :
    ∑ᶠ y₀ : OnePoint ℂ, resAtP1 hpacked y₀ = 0
```

(`RationalOnP1.lean`'s exact packaging of `R : ℂ → ℂ` into an `OnePoint ℂ → ℂ` for `resAtP1`'s
signature is routine `OnePoint.elim`-style bookkeeping, left to the builder — not designed
content; see §5 P-rational for the mathematical proof plan, which is the real content.)

### 4.6 Downstream interface for the future `jacobian-functoriality` unit (§0.5)

Miranda's Problems VIII.3 (read directly off the page, book p. 256): "**B.** ... show that `Tr :
ℳ(X) → ℳ(Y)` is a group homomorphism"; "**D.** ... show that if `g` is meromorphic on `Y`, `Tr(F^*(g))
= dg` [`d = deg F`]. More generally ... `Tr(F^*(g)h) = g·Tr(h)`. Hence ... `Tr` is `ℳ(Y)`-linear.";
"**F.** ... if `ω` is a meromorphic 1-form on `Y` and `h` meromorphic on `X`, `Tr(hF^*(ω)) =
Tr(h)·ω`." These are exactly `trace_const_mul_pullback`/`trace_pullback_eq_degree_smul` above (the
`ω`-form of Problem F, "`Tr∘pullback = deg·id`" per the task brief, is the `g := 1`/pair-form
reading of `trace_pullback_eq_degree_smul` — pulling back the reference form itself). A future
`jacobian-functoriality` unit wanting the period-naturality lemma for `Jacobian.pushforward`
(`docs/design/jacobian-construction.md` §9.4's flagged gap) would use
`trace_pullback_eq_degree_smul` at `g := ` a chart-coefficient of a pulled-back holomorphic form,
composed with `holomorphic-forms.md`'s `coeffIn`/`Form1.ofCoeffs` machinery to reassemble an
honest `Form1 X → Form1 Y` pushforward — **this reassembly is not designed here** (would need the
not-yet-built `Form1`-pullback operation `jacobian-construction.md` itself flags as missing); we
only supply the raw-coefficient projection-formula facts a future designer of that operation would
need. No current unit is DAG-wired to consume this — purely a forward-looking interface note.

---

## 5. Proof plans for the hardest theorems

### P1. `resAtX_eq_of_mem_source` (`PairForm.lean`)

Directly generalizes the ALREADY-BUILT, ALREADY-PROVED `RS.ordAtX_eq_of_mem_source`
(`Jacobian/Meromorphic/Predicates.lean:272`, read in full, §1) from a *source*-chart-only change
to a source-AND-target-chart change. Fix `x`, `c := chartAt ℂ x`, `c' := chartAt ℂ (F x)`, the
given `e`/`e'` with `hx`/`hFx`.

1. **Source-side transition.** `RS.analyticAt_transition he (chart_mem_maximalAtlas x) hx
   (mem_chart_source ℂ x) : AnalyticAt ℂ (c∘e.symm) (e x) ∧ deriv (c∘e.symm) (e x) ≠ 0` — call
   the pair `(hτ, hτ')`, `τ := c∘e.symm`.
2. **Target-side transition.** `RS.analyticAt_transition he' (chart_mem_maximalAtlas (F x)) hFx
   (mem_chart_source ℂ (F x)) : AnalyticAt ℂ (c'∘e'.symm) (e' (F x)) ∧ deriv (c'∘e'.symm)
   (e' (F x)) ≠ 0` — call the pair `(hσ, hσ')`, `σ := c'∘e'.symm`.
3. **Rewrite the `resAtX` integrand via `τ`.** `resAtX F h x` unfolds to `resAt (fun z => h (c.symm
   z) * deriv (c'∘F∘c.symm) z) (c x)`. Since `c.symm = e.symm ∘ τ⁻¹`-flavored (more precisely: on
   a neighborhood of `e x`, `c.symm =ᶠ e.symm ∘ ...`; the clean way, avoiding an extra inverse, is
   to apply `resAt_comp_mul_deriv` with `φ := τ = c∘e.symm`, `w₀ := e x`, `z₀ := c x` (since
   `τ (e x) = c (e.symm (e x)) = c x` by `e.left_inv hx`) directly to the FUNCTION
   `f := fun z => h (c.symm z) * deriv (c'∘F∘c.symm) z` and hypothesis `MeromorphicAt f (c x)`
   (from `hh : MeromorphicAtX h x` unfolded via `ordAtX`'s own definitional shape, chart `c`, plus
   the `deriv(...)` factor's local analyticity — `hF`/`analyticAt_transition` give this):
   `resAt (fun w => f (τ w) * deriv τ w) (e x) = resAt f (c x) = resAtX F h x`. So it remains to
   identify `fun w => f (τ w) * deriv τ w` with the TARGET formula in `e`.
4. **Chain-rule identification.** `f (τ w) = h (c.symm (τ w)) * deriv (c'∘F∘c.symm) (τ w)
   = h (e.symm w) * deriv(c'∘F∘c.symm)(τ w)` (using `c.symm∘τ = c.symm∘c∘e.symm = e.symm` on the
   overlap, `c.left_inv`). And `deriv (c'∘F∘c.symm) (τ w) * deriv τ w = deriv ((c'∘F∘c.symm)∘τ) w`
   (chain rule, `deriv.comp`/`HasDerivAt.comp`, both factors differentiable near `w` by `hF`'s
   `ContMDiffAt` + step 1's `hτ`) `= deriv (c'∘F∘e.symm) w` (since `c.symm∘τ = e.symm` again, so
   `(c'∘F∘c.symm)∘τ = c'∘F∘e.symm` pointwise near `w`, `deriv_congr`/`Filter.EventuallyEq.deriv_eq`
   on the open overlap). So `f(τ w)·deriv τ(w) = h(e.symm w)·deriv(c'∘F∘e.symm)(w)` — the
   SOURCE-side target formula, but still with `c'` (not `e'`) as the target chart.
5. **Repeat on the target side.** Apply `resAt_comp_mul_deriv` AGAIN, now with `φ := σ = c'∘e'.symm`
   composed appropriately — concretely, rewrite `deriv(c'∘F∘e.symm)(w) = deriv(σ ∘ (e'∘F∘e.symm))(w)`
   pointwise (since `σ ∘ e' = c'` near `F x`, by `e'.left_inv`, valid on the open set where
   `F(e.symm w) ∈ e'.source`, nonempty near `x` by continuity/`hFx`) `= deriv σ ((e'∘F∘e.symm) w) *
   deriv (e'∘F∘e.symm) w` (chain rule again, `hσ` gives `σ`'s differentiability). Substituting
   into the whole `resAt` expression and using `resAt_comp_mul_deriv` a SECOND time (this time
   trivially, since composing `resAt (fun z=> g(σ z)*deriv σ z) at a point equal to `resAt g` at
   the image point requires `σ` be evaluated at a FIXED point, not integrated over — here instead
   we are just doing a pointwise `deriv`-factor substitution, not a further `resAt_comp_mul_deriv`
   application; the "second use" is really just algebra: `deriv σ (·) * deriv(e'∘F∘e.symm)(·)` is
   already the SAME shape as the claimed target formula times a `deriv σ`-factor that is
   IDENTICALLY the constant used to convert `c'`-chart data to `e'`-chart data — this is exactly
   the residual bookkeeping `coeffIn_trans` handles for honest `Form1`s) gives, after simplifying,
   `resAt (fun w => h(e.symm w) * deriv(e'∘F∘e.symm)(w) * deriv σ (...)) (e x)`. The EXTRA
   `deriv σ(...)` factor is exactly compensated by ONE more `resAt_comp_mul_deriv` step reading the
   whole thing as "the `σ`-pullback of `resAt (fun z=> h(e.symm(...)) * deriv(e'∘F∘e.symm)(...))
   at `e' (F x)`" — concretely: package `g(z) := h(e.symm w(z)) ...` is circular; the CLEAN way to
   avoid re-deriving a two-hop chain rule by hand is to observe steps 3–5 are literally **two
   independent, commuting applications of `resAt_comp_mul_deriv`** — one for the `X`-side chart
   change (`e ↔ c`, done in steps 3–4) and one for the `Y`-side chart change (`e' ↔ c'`, symmetric
   to steps 3–4 but applied to the OUTPUT coefficient function rather than reparametrizing the
   residue point) — and the design's recommended IMPLEMENTATION order is to prove a
   ONE-CHART-AT-A-TIME lemma first (`resAtX_eq_of_mem_source_left` changing only the `X`-chart,
   exactly steps 1–4 above, a direct copy of `ordAtX_eq_of_mem_source`'s proof) and a SEPARATE
   `resAtX_eq_of_mem_source_right` changing only the `Y`-chart (a genuinely NEW, but structurally
   parallel, lemma: fix the `X`-chart at `c`, vary only `e'`; the target-chart change affects
   the coefficient factor `deriv(e'∘F∘c.symm)` by exactly a multiplicative `deriv σ`-factor
   evaluated at the FIXED point `c x`, i.e. becomes a single, non-iterated
   `resAt_comp_mul_deriv`-free algebraic rewrite via `resAt_const_mul` composed with the SAME
   `analyticAt_transition`/chain-rule argument, since now the reparametrization is of the
   INTEGRAND at a fixed base point, not of the residue's OWN base point) — then compose the two
   one-chart lemmas to get the general two-chart statement stated in D2. This factoring is the
   right engineering move: it isolates the genuinely new content (the `Y`-side lemma) from the
   copy-paste content (the `X`-side lemma, already fully precedented by `ordAtX_eq_of_mem_source`).

Est. **90–130 lines** (X-side lemma, a near-verbatim adaptation of the built
`ordAtX_eq_of_mem_source` proof, ~40 lines; Y-side lemma, genuinely new but structurally similar,
~50–70 lines; composition, ~10 lines).

### P-main. `resAtP1_trace_eq_sum` (`ResidueTraceCompat.lean`, ≥ 40 lines, Miranda Lemma 3.2 globalized)

Fix `F`, `hF`, `hne`, `h`, `hh`, `y₀`, `S : FiberStack F y₀` (`n := S.n`, `pt := S.pt`,
`A := S.A`, `k i := multiplicity F (pt i)`).

1. **Unfold `trace F h y₀` near `y₀` as a finite sum in the `y`-chart.** By mtrace's own
   `FunctionTrace.lean` design (D7: `trace F h y := ∑ i, traceZk (h∘(S.A i).e.symm) (k i)
   ((S.A i).e' y)`, evaluated via SOME chosen `FiberStack`; well-definedness against the choice is
   mtrace's own `trace_well_defined`/R1, orthogonal to us — we simply use the SAME `S` throughout,
   which is legitimate since `resAtP1` and `∑ i, resAtX F h (S.pt i)` are both computed from a
   single fixed `S`, so no comparison across stacks is ever needed here). Near `y₀`, in the
   PREFERRED chart `c := chartAt ℂ y₀`: since (by `AdaptedChartsAt`'s target-chart uniqueness at a
   COMMON image point `y₀ = F(pt i)` for every `i`) each `(S.A i).e'` and `c` are BOTH maximal-atlas
   charts at `y₀`, apply P1's `resAtX_eq_of_mem_source`-style transition ONCE per `i` (or, more
   directly, since we only need `resAtP1`'s `c`-chart formula, transport `trace F h`'s `(S.A i).e'`-
   chart pieces into the `c`-chart via the SAME `analyticAt_transition`/chain-rule machinery as
   P1) to get: `trace F h =ᶠ[𝓝 y₀] fun y => ∑ i, traceZk (h∘(A i).e.symm) (k i) ((A i).e' y)`
   reads, after transporting each `(A i).e'` into `c` via its transition `τ_i := c∘(A i).e'.symm`
   (analytic, `τ_i (0) = c y₀` since `(A i).e' (F (pt i)) = 0` and `F(pt i)=y₀`), as an honest
   FUNCTION of the `c`-chart variable `z := c y` near `c y₀` — this is EXACTLY mtrace's own
   `meromorphicAtX_trace` proof content (§5 P7 of the mtrace design doc), reused, not re-derived,
   once `FunctionTrace.lean` lands (§7 notes the interim risk if it has not).
2. **`resAt` is additive over the finite sum** (`resAt_fun_sum`, built,
   `Jacobian/ResidueCalculus/Residue.lean:60`, needs each summand `MeromorphicAt _ 0` — supplied by
   `meromorphicAt_traceZkForm`/mtrace's `meromorphicAt_traceZk`, both UNCONDITIONAL, not gated on
   P6): `resAtP1 (trace F h) y₀ = resAt(∑ i, [traceZk (h∘(A i).e.symm∘τ_i) (k i) ∘ ...]) (c y₀)
   = ∑ i, resAt (fun z => traceZk (h∘(A i).e.symm) (k i) (τ_i z)) (τ_i⁻¹-adjusted...)`. To avoid
   piling up chart-transition bookkeeping inside this step, the CLEAN implementation choice is:
   apply `resAt_comp_mul_deriv` termwise BEFORE distributing the sum, i.e. reduce step 1's
   `=ᶠ[𝓝 y₀]` identity to an identity in the `(A i).e'`-chart directly for term `i` (where
   `traceZk`'s formula is native, no transition needed for THAT term) and handle the transport to
   the COMMON `c`-chart via ONE application of `resAt_comp_mul_deriv` per term, exactly as P1's
   Y-side lemma does — i.e., literally invoke `resAtX_eq_of_mem_source` (P1, already proved,
   general `F`/`Y`) applied to `F := A i's local chart data` to identify each `c`-chart residue
   term with the `(A i).e'`-chart term BEFORE any further computation. This reuses P1 rather than
   re-deriving its content, keeping this proof's OWN new content confined to steps 3–5.
3. **Identify each term with `traceZkForm`.** In the `(A i).e`/`(A i).e'` adapted chart pair, `F`
   reads EXACTLY as `w ↦ w^{k i}` (`AdaptedChartsAt.eqOn_pow`), so the AMBIENT-coefficient-to-
   adapted-coefficient conversion (D1's `h_adapted`) is, BY THE ADAPTED-CHART STRUCTURE ITSELF
   (not an extra hypothesis): `h_adapted_i(w) := h((A i).e.symm w) · (k i) · w^{(k i) - 1}` is
   EXACTLY `resAtX`'s own integrand `h(e.symm w) * deriv(e'∘F∘e.symm)(w)` read in the `(A i).e`/
   `(A i).e'` chart pair (`deriv(e'∘F∘e.symm)(w) = deriv(w↦w^{k i})(w) = (k i)·w^{(k i)-1}` by
   `AdaptedChartsAt.eqOn_pow` + `hasDerivAt_pow`/`deriv_pow`). So, by `resAtX_eq_of_mem_source`
   (P1) applied to THIS chart pair: `resAtX F h (S.pt i) = resAt h_adapted_i 0`.
4. **Apply the Jacobian-cancellation + residue corollary** (D3): `traceZk (h∘(A i).e.symm) (k i)
   = traceZkForm h_adapted_i (k i)` (by `traceZkForm_hAdapted_eq`, UNCONDITIONAL — no gate), so
   `resAt (traceZk (h∘(A i).e.symm) (k i)) 0 = resAt (traceZkForm h_adapted_i (k i)) 0 =
   resAt h_adapted_i 0` (the SECOND equality is `resAt_traceZkForm`, ⚠ **gated on mtrace's P6**,
   D3) `= resAtX F h (S.pt i)` (step 3).
5. **Assemble.** Combining steps 1–4: `resAtP1 (trace F h) y₀ = ∑ i, resAt(traceZk(h∘(A
   i).e.symm)(k i)) 0 = ∑ i, resAtX F h (S.pt i)`. ∎

Est. **170–220 lines** (step 1's chart-transport bookkeeping, reusing mtrace's own
`meromorphicAtX_trace` proof pattern, is the bulk, ~80–100 lines; steps 2–4 are short given P1/D3
are already proved, ~50–70 lines; step 5 is a `simp`/rewrite assembly, ~20 lines). This meets the
task's "≥ 40 lines of plan" ask (the prose plan above is itself ~55 lines).

**Corollary (the `deg`-weighted sanity check, sanity-anchors against mtrace's own
`trace_of_regular`):** at a REGULAR value `y₀` (`k i = 1` for every `i`, `S.n = degree F`),
`resAtP1_trace_eq_sum` specializes to `resAtP1 (trace F h) y₀ = ∑ i, resAt h (S.pt i)` with no
Jacobian bookkeeping at all (since `traceZkForm h 1 = traceZk h 1 = h` literally, `k-1=0`) — a
cheap corollary worth stating as `resAtP1_trace_eq_sum_of_regular`, matching mtrace's own
`trace_of_regular` sanity anchor.

### P-holomorphic. `trace_eq_zero_of_holomorphic` (`HolomorphicVanishing.lean`)

1. **`trace F h` is `ContMDiff` on all of `OnePoint ℂ`.** Away from branch points: `traceZk`
   applied to an analytic (not just meromorphic) `h∘(A i).e.symm` is analytic by
   `RS.MTrace.analyticAt_traceZk` (P4, ALREADY PROVED, zero sorry) directly — no gate. AT branch
   points: need "`h` analytic at `0` ⟹ `traceZk h k` analytic (not just meromorphic) at `0`" — a
   genuinely NEW fact not currently exported by mtrace (its P5 only gives meromorphy for
   meromorphic `h`). **Proof, reusing mtrace's P5 CONSTRUCTION rather than its statement**: `h`
   analytic at `0` means order `n₀ ≥ 0` (`meromorphicOrderAt_eq_int_iff`'s `n₀`th case with `n₀≥0`
   literally IS analyticity, or simply skip the order-presentation step: bound `|h|` directly near
   `0`, apply P5's OWN growth-bound argument (§5 P5 of the mtrace design doc, steps 4–5) with
   `q := 0` (no `zpow` factor needed at all since there is no pole to absorb) to get `V := traceZk
   h k` bounded on a punctured disk, then Riemann's removable-singularity theorem
   (`Complex.differentiableOn_update_limUnder_of_bddAbove`, the SAME mathlib lemma mtrace's P5
   already uses) gives an analytic repair, and since `traceZk h k` ALREADY agrees with its own
   repair off `0` unconditionally (no `w^q` factor to strip when `q=0`), the repair equals
   `traceZk h k` on the punctured neighborhood — `AnalyticAt.congr` closes `AnalyticAt (traceZk h
   k) 0`. **Filed as a coordination request** (§10) to `meromorphic-trace`: either they export this
   as a corollary of their own P5 proof (cheap, since it is a strict simplification — no `zpow`
   factor to track), or `form-trace-tower` proves it locally in a marked `Compat` section
   (~40 lines, re-running P5's argument with `q=0` hard-coded) per `CONVENTIONS.md` rule 4. Either
   way, NOT gated on P6 (this only needs the EXISTENCE/qualitative argument, not the coefficient
   formula).
2. **Hence `RS.MTrace.trace F h : OnePoint ℂ → ℂ` has `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω _ y` at every `y`**
   (step 1, both chart cases; the transport from "analytic in SOME adapted/preferred chart" to
   `ContMDiffAt` is the standard `contMDiffAt_iff_analyticAt_comp_chartAt`-style bridge, already
   used pervasively, e.g. `ContMDiffAt.meromorphicAtX`'s converse direction,
   `Jacobian/Meromorphic/Predicates.lean:291`).
3. **Build the `Form1 (OnePoint ℂ)` and apply `form1_eq_zero`.** Package `trace F h`'s
   `ContMDiff`ness (step 2) directly as a `Form1CoeffData (OnePoint ℂ) (Bool)` over the TWO
   `ProjectiveLine.Charts`-atlas charts (`coeChart`/`invChart`, `chartFamily`/`chartIndex`,
   already built, `Jacobian/ProjectiveLine/Charts.lean`), using `trace F h`'s own value as the
   coefficient in EACH chart (`coeff true := trace F h ∘ coeChart.symm`, `coeff false := trace F h
   ∘ invChart.symm`) — the `compat` field of `Form1CoeffData` (the transition-rule compatibility)
   is EXACTLY the statement that `trace F h`, viewed as a coefficient against `dz`, transforms
   correctly between `coeChart`/`invChart` — this is `deriv(coeChart∘invChart.symm)`-weighted
   agreement, which is automatic here since we are packaging the SAME function `trace F h`'s VALUE
   (not a form-transformed coefficient) in both charts... **careful**: `Form1CoeffData.compat`
   requires the COEFFICIENT (not the raw function value) to transform by the `deriv`-factor
   between charts — since `trace F h` (as constructed) is precisely the "coefficient of `Tr(ω)`
   against `dz`" in the AMBIENT `ℙ¹`-chart sense (D1), and `Form1CoeffData`'s two charts here ARE
   `ℙ¹`'s own two charts (not adapted `X`-side charts), the compatibility is EXACTLY the
   `coeCharge`/`invChart` transition rule for the differential `dz` on `ℙ¹` itself — a SHORT,
   self-contained check (the `ℙ¹`-side transition `deriv(invChart∘coeChart.symm)(z) = deriv(z↦
   z⁻¹)(z) = -z⁻²`, and `trace F h`'s own agreement across charts, both being the SAME function
   evaluated via the SAME chart-independent `resAtX`/`trace` construction, is `rfl`-adjacent once
   unfolded correctly) — ~30 lines given `atlas_eq`/`coeChart_inversion_coe`/`invChart_inversion_coe`
   (all built, `Jacobian/ProjectiveLine/Charts.lean`) supply the needed transition identities
   directly.
4. **`Form1.ofCoeffs D = 0`** by `RS.P1.form1_eq_zero` (zero-sorry, built) — since `Form1
   (OnePoint ℂ)` is a SUBSINGLETON, `Form1.ofCoeffs D = 0` unconditionally, for ANY `D`.
5. **Transport back**: `Form1.coeffIn_ofCoeffs D true` (built, `Jacobian/Forms/OfCoeffs.lean`)
   gives `coeffIn coeChart (Form1.ofCoeffs D) = D.coeff true = trace F h ∘ coeChart.symm` on
   `coeChart.target`; combined with step 4 (`Form1.ofCoeffs D = 0`, so its `coeffIn` is
   IDENTICALLY `0`), `trace F h ∘ coeChart.symm = 0` on `coeChart.target = univ` (`Charts.lean`'s
   `coeChart` has full target), i.e. `trace F h = 0` on `coeChart`'s image (all finite points);
   the SAME argument with `invChart` (step 3's second chart) gives `trace F h ∞ = 0` too. ∎

Est. **90–130 lines** (step 1's Compat lemma, ~40 lines if proved locally; steps 2–5, ~60–90
lines of `Form1CoeffData` bookkeeping, mostly mechanical given the cited built lemmas).

### P-rational. `exists_partialFraction`/`sum_resAtP1_partialFraction_eq_zero` (`RationalOnP1.lean`)

1. **Finitely many poles.** `{z : ℂ | ordAtX-flavored-negative}` — rather than re-deriving
   compactness-of-poles from scratch, the CHEAPEST route is to observe `R`'s poles-plus-`∞`-pole
   data assemble into an honest `φ : ℳ (OnePoint ℂ)` (`RS.GermSpace.mk`, built, applicable since
   `hR.mero`/`hR.mero_infty` give `MeromorphicOnX` for the packaged `OnePoint ℂ → ℂ` lift of `R`
   directly — `RS.P1.contMDiffAt_of_pole`/chart-invariance already do the "meromorphic in EITHER
   chart ⟹ `MeromorphicAtX`" bridge, built), then `RS.finite_support_divisor φ` (built,
   `Jacobian/Meromorphic/Divisor.lean:277`, needs only `[T2Space][CompactSpace]` — both already
   instances for `OnePoint ℂ`) gives finiteness of `{y | φ.ord y ≠ 0}` DIRECTLY, no bespoke
   compactness argument needed. Intersect with "finite poles" (`ord < 0`) to get `S`.
2. **Subtract principal parts.** For each `a ∈ S` (`a ≠ ∞`; the `∞` pole, if present, is handled
   in step 3), `RS.principalPartAt R a` (built) is the honest Laurent-tail; set `g := R - ∑_{a∈S}
   principalPartAt R a` — `AnalyticAt ℂ g` EVERYWHERE on `ℂ` (`MeromorphicAt.orderAt_sub_
   principalPartAt_nonneg`, built, at each pole; at non-poles `g = R` locally, already analytic).
3. **Polynomial growth at `∞` and the new Compat lemma.** From `hR.mero_infty` (order `-N` at `w=0`
   for some `N`, possibly after ALSO subtracting `S`'s principal parts, which only改善 growth),
   `g`'s growth is `O(|z|^N)` as `z→∞` (standard translation of "meromorphic at `∞` with pole
   order `≤ N`" into "polynomial growth `≤ N`" — a `deriv`/order unfolding, ~20 lines). **New
   lemma needed** (checked: absent from mathlib, §1): `entire_of_polynomialGrowth : Differentiable
   ℂ g → (∃ N C, ∀ z, ‖g z‖ ≤ C*(1+‖z‖)^N) → ∃ P : Polynomial ℂ, g = fun z => P.eval z`. Proof: for
   `n > N`, `‖iteratedDeriv n g z‖ ≤ n! * C' * R^{-(n-N)} → 0` as `R → ∞`
   (`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`, built, applied on
   `sphere z R`, using the growth bound to control the sup there), so `iteratedDeriv n g z = 0` for
   all `z`, all `n > N`; then `g`'s (globally convergent, entire) power series at `0` truncates at
   degree `N`, giving `g = fun z => (Taylor poly of degree ≤ N).eval z` via
   `HasFPowerSeriesOnBall`/`Differentiable.hasFPowerSeriesOnBall`-style global Taylor expansion
   (mathlib's `Complex`-analytic global power series machinery) — ~50–70 lines total. File a
   `docs/requests/` note suggesting this lemma is generically useful and might belong in
   `Mathlib.Analysis.Complex.Liouville` upstream, or in a shared `Compat` section here if narrowly
   scoped to `ℙ¹`'s needs only.
4. **Assemble the partial fraction and the elementary residue computation.** `R = P.eval + ∑_{a∈S}
   principalPartAt R a` off the (finite) support, matching the stated existence theorem; the
   `Σ Res = 0` computation is the ELEMENTARY per-term case-split ALREADY WORKED OUT by hand in
   Miranda's own text (§0.1 item 4, book p. 254, verbatim): for `c(z-a)^n dz`, `n≤-2` gives a
   single pole at `a` with residue `0` (`resAt_zpow_mul`-style, `laurentCoeffAt` of a pure power at
   the WRONG index is `0`); `n=-1` gives residue `c` at `a` and `-c` at `∞` (direct `1/(z-a)` Laurent
   expansion at `∞`, `w=1/z` chart); `n≥0` gives a POLE only at `∞` (order `≥ 2` there) with residue
   `0` (again a pure-power-at-wrong-index vanishing). Each case is a `laurentCoeffAt`/`resAt`
   computation already mechanically available from `ResidueCalculus`'s built API
   (`laurentCoeffAt_zpow_mul`, `resAt_zpow_mul`) — no NEW residue-calculus content, just bookkeeping
   ~40–60 lines. Sum over `S ∪ {∞}` (finite, `Finset.sum_congr`/`finsum` bookkeeping) to conclude.

Est. **180–230 lines total** (step 3's new Compat lemma is the biggest single piece, ~60–70 lines;
steps 1–2 and 4 are routine given the cited built machinery, ~40 lines each).

---

## 6. Junk/convention ledger

| Object | Honest domain | Junk value | Why safe |
|---|---|---|---|
| `resAtX F h x` | `MeromorphicAtX h x`, `ContMDiffAt F x` | whatever `resAt` returns for the (possibly non-meromorphic) integrand | never quoted outside these hypotheses; `resAtX_eq_of_mem_source` is the only "honest" theorem and carries both guards |
| `traceZkForm h k w` | `w ≠ 0` (inherits `traceZk`'s own convention) | `traceZkForm h k 0` literally unfolds `traceZk`'s own `h 0`-style junk (§ mtrace's junk ledger) further composed with the (possibly ill-defined, `0⁻¹=0`-convention) Jacobian factor at `0` | never stated about at `w=0`; all theorems (P4-analogue, meromorphy, Laurent coefficients) are `𝓝[≠]0`-germ notions |
| `resAtP1 R y₀` | `R` meromorphic at `y₀` (in either chart) | whatever `resAt` of a non-meromorphic integrand returns | guarded identically to `resAtX` in every "honest" theorem |
| `MeroOnP1 R`'s partial fraction (`RationalOnP1.lean`) | `hR : MeroOnP1 R` | n/a — existence statement, no junk value produced | — |

No junk value here makes a stated theorem vacuously true: every "honest" theorem above carries
its precise guarding hypothesis, matching the pattern established by `docs/design/
meromorphic-trace.md`'s own junk ledger (§6 there), which this design's objects are built
directly on top of.

---

## 7. Risks & fallbacks

1. **HIGH — the whole coefficient/residue layer (D3's `laurentCoeffAt_traceZkForm`/
   `resAt_traceZkForm`, hence P-main's central theorem) is blocked on mtrace's `laurentCoeffAt_
   traceZk` (P6), currently `sorry`'d with two documented-but-incomplete routes in mtrace's own
   file.** Mitigation, in priority order:
   (a) **Wait/coordinate.** mtrace's design doc explicitly deprioritizes P6 ("ship P5 alone... defer
   P6/`resAt_traceZk`") — if this unit's builder starts before P6 lands, build files 1 (`PairForm`,
   fully independent) and file 2's UNCONDITIONAL half (`traceZkForm`, `meromorphicAt_traceZkForm`,
   `traceZkForm_hAdapted_eq` — none gated) first; these are ~60% of file 2's content and 100% of
   file 1's, giving real, checkable progress with zero risk of wasted work when P6 lands.
   (b) **A targeted, possibly-easier re-derivation via contour integrals was considered and
   rejected as the primary fallback** (documented for completeness, not recommended): `resAt`'s
   `circleIntegral_eq_two_pi_I_mul_resAt` bridge (built, `IntegralBridge.lean`) lets one restate
   `resAt_traceZkForm` as an equality of two contour integrals related by the substitution
   `z = w^k`. Concretely this reduces to `∫_0^{2π} G(kθ)dθ` vs `k·∫_0^{2π}G(θ)dθ`-type periodicity
   reasoning where `G` involves the SAME `k`-fold-covering combinatorics (which `w`'s `k` branches
   cover which `z`) that mtrace's own P6 struggled with — i.e. this route very likely reproduces
   the SAME "geometric-sum-collapse" difficulty in integral rather than series language, with the
   ADDED cost of unverified `intervalIntegral` substitution/periodicity lemmas. **Not recommended**
   as a first attempt; noted here so a future builder does not waste time rediscovering that it is
   not obviously cheaper.
   (c) **If truly blocked long-term**: ship files 1, and file 2's unconditional half, as a
   complete, useful partial delivery (matching mtrace's OWN precedent of shipping P5 alone); state
   P-main's theorem with `laurentCoeffAt_traceZkForm`'s conclusion as an EXPLICIT hypothesis
   (mirroring mtrace's own D3 "state the argument-principle theorem with `hFne` as a hypothesis,
   pushed to the caller" fallback pattern) so `abel-weak-solutions` can still be designed/typed
   against the interface even before the proof is discharged.

2. **MEDIUM — P1's target-chart ("Y-side") lemma is genuinely new** (not a copy of an existing
   proof, unlike the X-side half). If `resAt_comp_mul_deriv`'s hypotheses prove awkward to thread
   through TWICE (once per side) without an intermediate composite-transition lemma, the fallback
   is to state `resAtX` directly relative to a FIXED, arbitrary chart pair from the start (drop the
   "preferred chart" canonical definition, make `resAtX` take `(e, e')` as explicit data with a
   SEPARATE well-definedness theorem) — costs an extra explicit-chart-pair argument everywhere but
   avoids the two-hop composition. Not needed unless P1 proves harder than budgeted (~130 lines).

3. **MEDIUM — the "entire analytic ⟹ analytic trace at branch points" Compat lemma** (P-holomorphic
   step 1) is not currently exported by mtrace and not in mathlib. Filed as a coordination request
   (§10); the local fallback (~40 lines, re-running mtrace's OWN P5 growth-bound argument with
   `q := 0`) is low-risk since it is a strict SIMPLIFICATION of an already-proved argument (no
   `zpow`/Euclidean-division bookkeeping needed when there is no pole to absorb).

4. **MEDIUM — the "entire + polynomial growth ⟹ polynomial" Compat lemma** (P-rational step 3) is
   standard but not packaged in mathlib (checked, §1) — a genuine ~60–70 line proof via Cauchy
   estimates + `iteratedDeriv` vanishing + global Taylor-series identification. Since this whole
   file is flagged non-load-bearing (§0.3/§8), if this proves more expensive than budgeted, DEFER
   `RationalOnP1.lean` entirely — zero cost to any currently-wired consumer.

5. **LOW — `Form1CoeffData`'s `compat` field for `P-holomorphic` step 3** needs the `ℙ¹`-own
   `coeChart`/`invChart` transition identity for `dz`, which is elementary (`z ↦ z⁻¹`'s derivative)
   but requires care with the SIGN/orientation convention already fixed by `Charts.lean`'s
   `coeChart_inversion_coe`/`invChart_inversion_coe` (built) — pin these down first, do not
   re-derive the transition from scratch.

6. **LOW — `mtrace`'s `FunctionTrace.lean` does not exist on disk yet** (§0.4). P-main's proof plan
   (step 1) explicitly reuses mtrace's OWN `meromorphicAtX_trace` proof shape (mtrace design §5 P7)
   rather than re-deriving it; if mtrace's eventual `trace` definition or well-definedness story
   drifts from its design doc before this unit is built, only step 1's chart-transport bookkeeping
   needs adjustment — steps 2–5 (this unit's OWN new content) are insulated, since they only ever
   consume `trace F h`'s VALUE via the `S`-indexed formula, not its definitional internals.

---

## 8. Downstream map

| Consumer | What it needs | Our export | DAG-wired? |
|---|---|---|---|
| **abel-weak-solutions** | the trace tower as a black box; per Miranda VIII.3's actual usage (§0.1 item 5), most likely `trace_eq_zero_of_holomorphic` (holomorphic pair-forms trace to `0` on `ℙ¹`, genus-`0` argument) and/or `resAtP1_trace_eq_sum` (Miranda Lemma 3.2) for its own "weak solution" residue bookkeeping | `RS.MTrace.trace` (reused unchanged, not redefined here), `resAtX`, `resAtP1_trace_eq_sum`, `trace_eq_zero_of_holomorphic` | **yes** (blueprint `Builds on:`) |
| **residue-theorem** | `Σ Res = 0` on general `X` | — (independent Stokes/PoU route, `canonical-forms`+`planar-stokes-atoms`) | **no** (§0.3 DAG audit) |
| **serre-duality-tails** | `Σ Res = 0`/the Serre residue functional | — (independent route via `laurent-tails`/`proper-map-degree`/`residue-theorem`/`serre-duality-cech`; Miranda's OWN Ch. VI development cites `Σ Res=0` as an imported black box too, §0.1) | **no** (§0.3 DAG audit) |
| **laurent-tails** | nothing from us | — (`Builds on: canonical-forms, meromorphic-trace` only) | **no** |
| **jacobian-functoriality** (not a current blueprint unit, §0.5) | projection-formula facts for period-naturality of `Jacobian.pushforward` | `trace_const_mul_pullback`, `trace_pullback_eq_degree_smul` (§4.6) | **no current unit** — forward-looking interface only |
| **`RationalOnP1.lean`'s own content** | Miranda's "algebraic proof of the residue theorem" (an ALTERNATIVE, not-chosen proof route for `residue-theorem`) | `exists_partialFraction`, `sum_resAtP1_partialFraction_eq_zero` | **no** — self-contained bonus, explicitly not required by any current unit |

---

## 9. Spike report (`scratch_ftt.lean`, project root)

Gate respected (`pgrep -cx lean` = 0 at run time; re-checked before each of two runs during
iteration). Deliberately does **not** import the still-churning `Jacobian.MeromorphicTrace`
(§0.4) — checks the two load-bearing NEW algebraic facts against the frozen, zero-sorry
`ResidueCalculus` unit only, standing in mtrace's `traceZk`/P6 abstractly as hypotheses (their
concrete forms are already fully verified by mtrace's OWN spike, `scratch_mtrace.lean`, not
re-verified here).

`lake env lean scratch_ftt.lean`: **compiles clean, exit 0** (one informational `ring`-tactic
"Try this: ring_nf" diagnostic emitted but not gating success — no `error:`-level output; both
declarations elaborate and typecheck).

1. **Fact 1 (the Jacobian-cancellation, D3's `traceZkForm_hAdapted_eq` core step)**: the pointwise
   identity `(h v * k * v^(k-1)) * (k * v^(k-1))⁻¹ = h v` (for `v ≠ 0`) closes by `field_simp` given
   `(k:ℂ) ≠ 0` and `v^(k-1) ≠ 0` — confirms the "Jacobian factor exactly cancels" claim mechanically,
   with **no hidden side conditions** beyond `k ≠ 0`/`v ≠ 0`.
2. **Fact 2 (the Laurent-coefficient shift, D3's `laurentCoeffAt_traceZkForm`, GIVEN mtrace's P6 as
   a hypothesis)**: the full derivation chain — unconditional pointwise function identity `h v *
   (k*v^(k-1))⁻¹ = k⁻¹*(v^(-(k-1))*h v)` (via `mul_inv`/`zpow_neg`, **no `v ≠ 0` needed at all**,
   since these hold at `0` too by the `0⁻¹=0` convention — a strictly weaker/cheaper hypothesis
   than Fact 1's, worth noting for the real implementation) composed with the built
   `laurentCoeffAt_const_mul`/`laurentCoeffAt_zpow_mul` and the hypothesized P6, closes the target
   index identity `k*j + (k-1) = k*j - -(k-1)` by `ring` and the scalar identity `k*(k⁻¹*X) = X`
   by `mul_inv_cancel_left₀`. **Confirms the whole derivation chain sketched in §0.1 item 2/D3 is
   mechanically sound**, not just a hand-wavy algebra sketch.
3. **Cross-check**: `resAt_comp_mul_deriv`'s hypotheses (`AnalyticAt ℂ φ w₀`, `deriv φ w₀ ≠ 0`,
   `φ w₀ = z₀`, `MeromorphicAt f z₀`) were re-read directly from `ChangeOfVariables.lean` (not
   spiked separately — its proof and the precedent `ordAtX_eq_of_mem_source` proof, both read in
   full, give high confidence in P1's proof plan without a further isolated spike).

---

## 10. Coordination notes filed

- `docs/requests/meromorphic-trace.md` (**new file**): records (a) that this unit's central
  theorem (`resAtP1_trace_eq_sum`) is blocked on `laurentCoeffAt_traceZk` (P6) landing sorry-free,
  with a request to prioritize it or to flag if the two documented routes in mtrace's own file
  remain stuck, so this unit's builder can decide between waiting and re-deriving P6's content
  independently (§7 Risk 1); (b) a request for an "analytic (not just meromorphic) `h` ⟹ analytic
  `traceZk h k` at the branch point" corollary of mtrace's own P5 proof (§7 Risk 3), needed by
  `HolomorphicVanishing.lean`'s step 1, cheap since it is a strict simplification of the existing
  P5 argument with no pole to absorb.

Nothing filed against `residue-calculus`, `mapping-degree`, `local-multiplicity`,
`projective-line`, `holomorphic-forms`, or `meromorphic-and-divisors` — all facts consumed from
these units (§1) are already built, zero-sorry, and read directly off disk; no gaps found.
