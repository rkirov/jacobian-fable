# Design: abel-weak-solutions (`Jacobian/AbelWeak/`)

Blueprint unit **abel-weak-solutions**. Blueprint text: "Weak/planar solution steps for the Abel
engine: chain decompositions and piecewise-planar solutions. Read: Forster §20.1–20.4. Strategy:
build the path-integral/chain data that the two-point Abel nonvanishing will consume, staying in
planar pieces glued by monodromy." Declared **Builds on:** form-trace-tower, monodromy,
planar-stokes-atoms. Consumer: **abel-theorem** (#29, not yet designed), which additionally builds
on cech-h1-genus. Forster §20 (PDF 159–166 = book 159–166) and §21.1–21.2 (PDF 166–168 = book
166–168) read in full from the PDF; §19.10–19.14 (PDF 157–158, harmonic forms) read for context
only, per the routing warning below. One gated end spike (`scratch_abelweak.lean`, project root)
compiled clean, 0 sorries — §9.

---

## 0. Verdict up front

**Forster's Lemma 20.5 — build a smooth ("weak") solution of a two-point divisor `P − Q` together
with the integral formula relating a path integral of a holomorphic form to the solution's
logarithmic derivative — is exactly this unit's job, and is fully achievable from three already-
built units: `paths-and-integrals` (`ChartChain`, `IsPrimitiveAlongMap`), `planar-stokes-atoms`
(the two Wirtinger-`∂̄` Stokes atoms), and one small NEW planar lemma (a rational-function log
branch, §6.1) that reduces to mathlib's disk-Morera primitive via a `z ↦ 1/z` inversion — no
winding-number/homotopy machinery needed.**

Two of the blueprint's three declared dependencies are **not load-bearing** for this content, on
inspection (§2, the DAG audit — matching the pattern already established by `monodromy.md`,
`form-trace-tower.md`, `proper-map-degree.md`, `sphere-topology.md` for their own edges):

* **`monodromy`**: its `RS.Monodromy.dlogForm`/`exp_eq_holoRepr_of_isPrimitiveAlong` machinery is
  built for a genuine **meromorphic** `f : ℳ X` (with a canonical `holoRepr`). Forster's "weak
  solution" `f` is explicitly **not** meromorphic (`f ∈ 𝓔(X_D)`, merely `C^∞`, §20.1) — the whole
  content of Lemma 20.5 is building it *without* first knowing a meromorphic solution exists. The
  log-branch construction this unit needs is a **purely planar** fact about a specific rational
  function `(z−b)/(z−a)`, provable directly from mathlib's disk primitive (`Complex.IsExactOn`,
  already cited and used by `paths-and-integrals`) with no manifold-level continuation at all.
* **`form-trace-tower`**: its `trace_eq_zero_of_holomorphic`/`resAtP1_trace_eq_sum` are exactly the
  ingredients Forster's 20.7 proof part (b) (**necessity**: an actual meromorphic `f` with
  `div f = D` defines a covering `X → ℙ¹`, and tracing a holomorphic form down gives `0` since
  `Ω(ℙ¹) = 0`) needs. That is `abel-theorem`'s own necessity-direction proof, not weak-solution
  construction. `form-trace-tower.md` §11 itself only *guesses* "likeliest need: Atom 1... its
  blueprint entry does not mention residues or poles" for us — checked directly against Forster's
  own Lemma 20.3 text (§1.3 below) and found to under-describe what is actually needed (we *do*
  need the residue atom, Atom 2, not just Atom 1/1b — a correction to `planar-stokes.md`'s own §11
  guess, not to its atoms, which are exactly right).

Recommended DAG correction: `abel-weak-solutions`'s `Builds on:` line should read
`paths-and-integrals, planar-stokes-atoms` (both frozen dependencies of `abel-weak-solutions`'s own
`Builds on:` list already — `planar-stokes-atoms` **builds on** `paths-and-integrals` too, so this
is a strict tightening). `monodromy` and `form-trace-tower` remain available to `abel-theorem`
(#29) directly via its own imports; nothing here is *blocked* on either, and no code here imports
either. Filed as a coordination note (§10), not as an edit to `clean_room_blueprint.md` (matching
`form-trace-tower.md`'s own precedent of flagging rather than editing).

**What Forster's proof needs that we do *not* build (the scope split with #29, task item 3):**
Forster's Corollary 20.6 (harmonic differentials representing periods, via Thm 19.10–19.14's
de Rham–Hodge apparatus) is **out of scope entirely** — the project's own routing decision #3
("cohomology-first, PDE-light... stay off the Hodge route") rules it out, and — checked directly
by reading 20.7's proof text (PDF 163–164) — **20.7 itself never cites 20.6**. The Dolbeault-
solvability step 20.7(a) *does* cite (19.10) (solving `d''g = d''f/f`), but this is `abel-theorem`'s
own job to discharge via the project's non-Hodge Serre-duality substitute (`serre-duality-tails`/
`cech-h1-genus`, dimension-counting over Laurent tails, not harmonic projection) — **not**
something this unit attempts (task item 3: "Abel 20.7 itself... stays out"). The **third-kind-
differential existence** route the task brief floats as an alternative construction is examined in
§4 and found to be a real, correctly-derivable fact, but one that is *gated on Riemann–Roch and
`l(K) = g`*, neither built nor a declared dependency here — and, checked against the actual proof
text, **not what Forster's own dissection-free 20.7 uses at all**. This unit therefore builds
Forster's literal machinery (weak solutions via chains), not the third-kind-differential
alternative; §4 documents the alternative's exact gates for whichever future builder might want it.

---

## 1. Forster §20.1–20.7, digested (PDF 159–166, read in full)

### 1.1 §20.1 — weak solutions

For a divisor `D` on `X`, `X_D := {x : D(x) ≥ 0}`. A **weak solution** of `D` is
`f ∈ 𝓔(X_D)` (i.e. `f` real-`C^∞`, *not* required meromorphic) such that near every point `a`,
there is a coordinate `(U, z)` with `z(a) = 0` and `ψ ∈ 𝓔(U)`, `ψ(x) ≠ 0` for `x ∈ U`, with
`f = ψ z^k` on `U ∩ X_D`, `k = D(a)`. A weak solution is an honest (meromorphic) solution
precisely if it is holomorphic. Weak solutions of `D₁`, `D₂` multiply to a weak solution of
`D₁ + D₂` (this is why the *general* chain case reduces to point pairs, §1.4).

**Our specialization**: `abel-theorem`'s actual need (blueprint blurb: "if `AJ(P) = AJ(Q)` then
there is a meromorphic function with divisor `P − Q`") is the two-point divisor `D = P − Q`
(`P ≠ Q`), `X_D = X \ {Q}` in Forster's literal reading (only the *pole* is excluded from `𝓔`'s
domain; `f` is allowed — indeed required — to vanish at `P`, a genuine `C^∞` zero). We build
`IsWeakSolutionAt` at a single point and `IsWeakSolutionOfPair` for the pair `(P, Q)` directly
(§5.1) — **no `Divisor X`/`Divisor.single` needed** (the latter does not exist on disk yet,
`canonical-forms.md` §1.6; sidestepped entirely, since the pair-based formulation is exactly what
`abel-theorem` consumes and needs no general `Divisor` bookkeeping).

### 1.2 §20.2 — logarithmic differentiation

For a weak solution `f` of `D`, `df/f` is a smooth `1`-form on `X \ Supp(D)`, with local model
(at `a ∈ Supp D`, `k := D(a)`) `df/f = k·dz/z + dψ/ψ`. Since `z^k` is holomorphic, `d''(z^k)/z^k = 0`
(the `(0,1)`-part vanishes), so `d''f/f = d''ψ/ψ` is smooth **on all of `X`** (no singularity even
at `Supp(D)` — this is the fact 20.7(a) needs from a *global* Dolbeault-solvability step, §0's
scope note; not built here).

### 1.3 §20.3 — the Stokes/residue lemma

For distinct `a₁,…,aₙ`, integers `k₁,…,kₙ`, `D` the divisor with `D(aⱼ) = kⱼ`, `f` a weak solution
of `D`, and `g ∈ 𝓔(X)` with compact support:
`(1/2πi) ∬_X (df/f) ∧ dg = Σⱼ kⱼ g(aⱼ)`.
**Proof shape** (disjoint coordinate disks `Uⱼ` around each `aⱼ`, bump functions `φⱼ ≡ 1` near `aⱼ`,
`≡ 0` outside a slightly larger disk; the "far" piece `g₀` has compact support in `X \ {a₁,…,aₙ}`
so its contribution vanishes by the *unconditional* Stokes identity for compactly-supported forms;
each near-`aⱼ` piece reduces, via the local model `k_j dz/z + dψⱼ/ψⱼ` and an annulus-shrinking
limit, to `2πi kⱼ g(aⱼ)`). **This maps onto our vocabulary exactly**: "far piece vanishes" is
`planar-stokes-atoms`'s Atom 1/1b (`RS.integral_wirtingerDbar_eq_zero` /
`..._mul_eq_zero_of_differentiableOn`); "near-`aⱼ` annulus limit" is Atom 2
(`RS.integral_wirtingerDbar_mul_eq_neg_pi_mul_resAt`, the smeared-residue theorem, with its
`hconst`-hypothesis "`g` locally constant near the puncture" **exactly matching** Forster's own
`φⱼ ≡ 1` cutoff choice). **This is a genuine residue computation, not merely a compact-support
vanishing fact** — a correction to `planar-stokes.md`'s own §11 guess ("likeliest need: Atom 1
alone... not a residue computation"), recorded in §2.2.

**Our specialization**: since we only ever build weak solutions of the two-point pair `(P,Q)`
(`k_P = +1`, `k_Q = -1`), we only need `n = 2`; and since we apply this lemma with `g` a
**holomorphic** local primitive of a **holomorphic** form `ω` (not an arbitrary smooth compactly
supported function), the computation simplifies further (§7, Residue.lean): `dg` has no `dz̄` part
at all, so only the `(0,1)`-part of `df/f` (i.e. `d''f/f`, matching §1.2) contributes, and that
part is compactly supported inside the bump-transition annulus by construction.

### 1.4 §20.4 — chains, cycles, homology

A **1-chain** is a formal `ℤ`-linear combination of curves `c = Σ nⱼ cⱼ`; `∂ : C₁(X) → Div(X)`
assigns `c ↦ c(1) − c(0)` per curve (extended by linearity); `deg(∂c) = 0` always; conversely,
every degree-`0` divisor is `∂c` for *some* chain `c` (pair off `+1`s with `−1`s and connect each
pair by a curve). **Our specialization**: since `abel-theorem`'s divisor is *already* the single
pair `P − Q`, the chain is trivially **a single path** `γ : Q ⟶ P` (`∂γ = P − Q` automatically,
`deg = 0` for free) — the general `C₁(X)`/`Z₁(X)`/`H₁(X)` group-theoretic bookkeeping of 20.4 is
**not needed** by this unit at all (it is real content, but only for the *general*-divisor
statement, which no current consumer needs; flagged, not built, §8). What **is** still needed from
"chains" in the informal sense — subdividing a single path `γ` into chart-sized pieces so each
piece's weak solution can be built by the single-chart recipe — is exactly `paths-and-integrals`'s
already-built `RS.ChartChain`/`RS.exists_chartChain` (a Lebesgue-number chart-ball subdivision of
`γ`; nothing new to prove for this half).

### 1.5 §20.5 — the weak-solution + integral-formula lemma (the deliverable)

Given a curve `c : [0,1] → X` and a relatively compact open `U ⊇ c([0,1])`, there is a weak
solution `f` of `∂c` with `f|_{X\U} ≡ 1`, such that for every **closed** `ω ∈ 𝓔^{(1)}(X)`:
`∫_c ω = (1/2πi) ∬_X (df/f) ∧ ω`.
Proof: (a) single-chart case, `c` inside one chart-disk `U ≅` unit disk, `a := c(0)`, `b := c(1)`:
`(z−b)/(z−a)` is holomorphic, non-vanishing, and has **winding number `0`** on the annulus
`{r < |z| < 1}` (`a, b` both inside `{|z| < r}`), so it has a well-defined log branch there; a
cutoff `ψ ≡ 1` near `{|z| ≤ r}`, `≡ 0` near `{|z| = 1}` interpolates
`f₀ := exp(ψ·log((z−b)/(z−a)))` from `(z−b)/(z−a)` to the constant `1`. (b) General case:
subdivide `c` into chart pieces `c₁,…,cₙ` (⇒ `RS.ChartChain`), build each `fⱼ` by (a), set
`f := f₁⋯fₙ` — a pointwise product of already-*globally*-defined functions, no further gluing.
**Our specialization and the resulting simplification (§6, the "exp-gluing engine")**: rather than
Forster's own "log branch on the annulus" argument (which needs a winding-number/homotopy fact),
we reduce the single-chart step to an **explicit rational-function computation** via the
substitution `w = 1/z` (turning the *exterior* annulus into a genuine disk *containing no
singularity of the transported function at all*, not merely simply connected — §6.1), closing with
mathlib's disk-Morera primitive (`Complex.IsExactOn`) plus one zero-derivative uniqueness argument
— **no branch-cut case analysis, no homotopy/winding-number machinery**, matching (and, we argue,
strictly simplifying) Forster's own construction. Spike-verified, §9.

### 1.6 §20.6 (Corollary) and §20.7 (Abel's Theorem) — out of scope here (task item 3)

20.6 constructs a *harmonic* differential `σ_α` representing a cycle's periods, via the de Rham–
Hodge decomposition (19.11–19.14). **Not built, not cited, not needed**: checked directly, 20.7's
own proof (PDF 163–164) never invokes 20.6. 20.7 itself (both directions) and `ofCurve_inj` are
`abel-theorem`'s (#29's) job. What #29 will need from *this* unit, read directly off 20.7's proof
text:
* **Sufficiency direction** ("`AJ(D) = 0` ⟹ `∃` solution"): given a chain (for the two-point case,
  a path `γ : Q ⟶ P`) with `∫_γ ω = 0` for a **basis** of holomorphic forms (Forster's condition
  `(*)`, restated via `Jacobian.ofCurve`/`periodSubgroup` in our vocabulary in §10), 20.7(a) builds
  the weak solution `f` (this unit, §1.5) and *then* solves `d''g = d''f/f` (a project-native
  Serre-duality-substitute for Forster's harmonic-theory citation `(19.10)`, owned downstream) to
  upgrade `f` to an honest meromorphic `F := e^{-g} f`. We hand #29 the pair `(f, <its known
  chart-local `df/f` data>)`; #29 does the upgrade.
* **Necessity direction** ("`∃` solution ⟹ `AJ(D) = 0`"): entirely `form-trace-tower` +
  `mapping-degree`/`proper-map-degree`'s covering-space machinery (§0); **no weak solution is
  built or consumed on this side at all** — we contribute nothing to it.

---

## 2. DAG audit: what this unit actually needs

### 2.1 `paths-and-integrals` — genuinely essential

`RS.ChartChain`/`RS.exists_chartChain` (chain decomposition of `γ`), `RS.IsPrimitiveAlongMap` +
`.rechart`/`.sub_eq_sub`/`.glue`/`isPrimitiveAlongMap_of_ball` (the per-piece holomorphic-primitive
bookkeeping that gives the telescoped path-integral identity, §7.2), `RS.pathIntegral`/
`RS.exists_isPrimitiveAlong` (the CC6 integral itself, against which the deliverable is stated),
and `Path/Planar.lean`'s own citation of `Complex.IsExactOn`/`DifferentiableOn.isExactOn_ball`
(disk Morera — the *same* mathlib fact our own new planar log-branch lemma also needs, §6.1;
`Path/Planar.lean`'s docstring explicitly invites this reuse: "dbar-solvability, residue-calculus,
monodromy, abel-weak should import `Jacobian.Path.Planar`... for disk primitives — do not
re-prove").

### 2.2 `planar-stokes-atoms` — genuinely essential (both Atom 1b *and* Atom 2)

`RS.integral_wirtingerDbar_mul_eq_zero_of_differentiableOn` (Atom 1b, the "no pole in this piece"
bulk vanishing) **and** `RS.integral_wirtingerDbar_mul_eq_neg_pi_mul_resAt` (Atom 2, the smeared-
residue theorem) — both needed for Lemma 20.3's computation (§1.3), *contra*
`planar-stokes.md`'s own §11 guess that "the likeliest need is Atom 1 alone... not a residue
computation." Re-reading Forster's own Lemma 20.3 proof text shows the "near-`aⱼ`" pieces are
genuine annulus-shrinking residue limits (`lim ∮_{|z_j|=ε} g_j dz_j/z_j = 2πi g_j(a_j)`), which is
*exactly* Atom 2's shape (`hconst`'s "`g` locally constant near `p`" matches Forster's own
`φⱼ ≡ 1` cutoff choice verbatim). This correction is filed as a coordination note (§10); it does
not require any change to `planar-stokes-atoms`'s own atoms, which are exactly right — only to its
guess about which atom gets used.

### 2.3 `monodromy` — not needed (recommend dropping the edge)

`RS.Monodromy`'s `dlogForm`/`exp_eq_holoRepr_of_isPrimitiveAlong`/`exists_logBranchAlong` operate
on `f : ℳ X` (a genuine meromorphic function, with a canonical `holoRepr`). Forster's weak
solution is explicitly *not* meromorphic — `monodromy`'s machinery has no instance to apply to
Forster's weak solution *until after* #29's own Dolbeault upgrade produces an honest meromorphic
`F`, which is #29's business, not ours. The log-branch fact this unit needs (§6.1) is a
self-contained planar computation about one explicit rational function, provable directly from
mathlib with no manifold-level continuation machinery at all. `monodromy.md` §1.2/§4.3 anticipated
this unit *might* want its machinery as a convenience; on inspection, the direct planar route is
both cheaper (fewer imports, no open-locus/`poleZeroLocus` bookkeeping) and unconditionally
correct, so it is what we build. No file in this unit imports `Jacobian.Monodromy`.

### 2.4 `form-trace-tower` — not needed (recommend dropping the edge)

Its `trace_eq_zero_of_holomorphic`/`resAtP1_trace_eq_sum` feed the **necessity** direction of
Forster 20.7 (§1.6), which is `abel-theorem`'s own proof obligation and does not touch weak
solutions. No file in this unit imports `Jacobian.FormTrace`.

### 2.5 Recommended DAG correction

`abel-weak-solutions`: **Builds on: paths-and-integrals, planar-stokes-atoms.** (Both were already
transitively required — `planar-stokes-atoms` builds on `dbar-solvability, residue-calculus`, not
on `paths-and-integrals` directly, so this is a net *simplification*, not a cycle.) `monodromy` and
`form-trace-tower` remain exactly where the blueprint puts them for `abel-theorem`'s own future use
(via direct import there, not through us). Filed as a coordination note only (§10); no edit made to
`clean_room_blueprint.md` itself, matching the project's established practice for this class of
finding.

---

## 3. `meromorphic-and-divisors` — used only incidentally, if at all

Everything above is stated directly in terms of `P, Q : X` and paths between them; the weak
solution `f` is a bare `X → ℂ` (§5.1), never packaged as `ℳ X`, and never differentiated against a
`Divisor X`. This unit therefore does **not** need `meromorphic-and-divisors` as a hard dependency
either (a further, smaller DAG note, §10) — though `ℳ X`'s `holoRepr`/order API remains available
if a future refinement wants to state the two-point case via `Divisor.single P 1 - Divisor.single
Q 1` once `Divisor.single` lands (`canonical-forms.md` §1.6 flags it is still missing).

---

## 4. Gap check: third-kind differentials (task item 4), examined and deferred

The task brief floats an alternative architecture: construct `f` directly as
`exp(Σ ∫_γ ω_{P,Q})` for a **normalized differential of the third kind** `ω_{P,Q}` (residues
`+1`/`−1` at `P`/`Q`, holomorphic elsewhere), whose existence would come from a
Mittag-Leffler/Riemann–Roch argument on `MForm.OmegaSpace`. This was worked out in full to check
whether it is available *now*:

**The derivation** (using `CanonicalForms`'s actually-built `MForm.OmegaSpace`/`i`, `Jacobian/
CanonicalForms/LinearSystems.lean`, current on disk): the residue-pair map
`OmegaSpace (P+Q) → ℂ²`, `ω ↦ (ω.resAt P, ω.resAt Q)`, has kernel exactly `OmegaSpace 0 = Ω(X)`
(an element with both residues `0` has actual order `≥ 0` at both `P, Q`, since the defining bound
was "order `≥ −1`" and a vanishing order-`(-1)`-coefficient forces order `≥ 0` — `LinearSystems.
lean`'s own `ord_smul`/divisor machinery gives this directly). By Riemann–Roch,
`i(P+Q) = l((P+Q)+K) = l(K) + 1 = g + 1` (using `deg K = 2g-2`, `l(K) = g`, and `l(D) = 0` for
`deg D < 0` via `deg(div f) = 0`, all **standard** but **not yet built** facts), strictly one more
than `i(0) = l(K) = g`. Rank-nullity then forces the residue-pair image to be **exactly**
one-dimensional, and the residue theorem (`Σ Res = 0`, not yet built either) forces that
one-dimensional image to be the line `{(r,−r)}` — giving existence of `ω_{P,Q}` with residues
exactly `(1,−1)`.

**Verdict: a real, correct derivation, but gated on `riemann-roch` and `cech-h1-genus`'s `l(K)=g`**
(neither built, neither a declared or plausible dependency of *this* unit — `abel-weak-solutions`'s
declared `Builds on:` never included them, and `abel-theorem`'s own declared `Builds on:` is
`abel-weak-solutions, cech-h1-genus`, i.e. `cech-h1-genus` is a **sibling** dependency of `#29`,
not of `#24`). It is also, checked directly against the PDF, **not what Forster's own dissection-
free proof of 20.7 uses** — his proof (§1.5–1.6 above) builds the weak solution directly from
chains and never constructs a third-kind differential. Building the third-kind route here would
mean duplicating machinery that is (a) unavailable at this unit's build time and (b) unnecessary
for the proof strategy the blueprint actually mandates ("Use Forster's dissection-free
formulation"). **Decision: do not build it here.** This is filed as a documented, non-blocking
alternative (§10) for whoever eventually builds `abel-theorem`, in case a future builder prefers it
over consuming this unit's weak-solution output — its exact gates (Riemann–Roch, `l(K)=g`, `Σ Res
= 0`, `deg(div f)=0` — the last one already available, `Jacobian.ProperDegree` is built and
imported in `Jacobian.lean`) are recorded above so no one has to re-derive them to find out.

---

## 5. Core definitional decisions

### D1 — `IsWeakSolutionAt`/`IsWeakSolutionOfPair`: bare functions, no `ℳ X`, no `Divisor X`

```lean
namespace RS.AbelWeak

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Forster 20.1's local model at a single point, specialized (no general `Divisor`): `f` is
`ℝ`-smooth near `a` and factors as `ψ · z ^ k` in some chart at `a`, `ψ` smooth and non-vanishing.
`k` ranges over `ℤ` (a genuine `zpow`, since `k` may be negative — a pole). -/
def IsWeakSolutionAt (f : X → ℂ) (a : X) (k : ℤ) : Prop :=
  ∃ e : OpenPartialHomeomorph X ℂ, e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X ∧ a ∈ e.source ∧
    ∃ ψ : ℂ → ℂ, (∀ z ∈ e.target, ψ z ≠ 0) ∧
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤ ψ e.target ∧
      ∀ᶠ z in nhdsWithin (e a) {e a}ᶜ ⊔ pure (e a), (f ∘ e.symm) z = ψ z * (z - e a) ^ k
      -- (junk-safe local-model equation; z-range restricted to e.target in the real lemma, see
      -- §6.2 for the concrete instantiation actually used — this is the general shape only)

/-- The weak-solution predicate for the two-point pair `(P, Q)` this unit actually builds:
`ℝ`-smooth away from `Q`, weak-solution local model `+1` at `P` (genuine `C^∞` zero), `-1` at `Q`
(simple pole, excluded from the smoothness domain), and honestly `ContMDiff`/non-vanishing
everywhere else. -/
structure IsWeakSolutionOfPair (f : X → ℂ) (P Q : X) : Prop where
  contMDiffOn : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ⊤ f {Q}ᶜ
  ne_zero_off : ∀ x, x ≠ P → x ≠ Q → f x ≠ 0
  weakAt_P : IsWeakSolutionAt f P 1
  weakAt_Q : IsWeakSolutionAt f Q (-1)

end RS.AbelWeak
```

`IsWeakSolutionAt`'s precise `z`-range/junk convention is pinned down concretely (not abstractly,
per the note above) when it is actually instantiated in §6.2/§7 — a design doc need not (and, per
this project's junk-safety discipline, should not) commit to an abstract shape that can hide a
junk leak; the exact shape used in the constructive theorems is the one that matters, and is given
in full there.

### D2 — the planar log-branch atom (`PlanarLogBranch.lean`, no manifold imports)

Pure `ℂ → ℂ`, matching `Path/Planar.lean`'s hygiene (reusable by anything, no surface stack
dragged in). Two lemmas: the disk case (spiked, §9) and its inversion-transport to the exterior
region Forster's construction needs (§6.1).

### D3 — the single-chart weak solution (`SingleChart.lean`)

Built entirely in one chart's target `ℂ`, using D2 + a `ContDiffBump` cutoff; the result is stated
as a genuine `X → ℂ` function via `Set.piecewise`/junk-safe extension by the constant `1`.

### D4 — chain assembly and the deliverable (`ChainAssembly.lean`)

The pointwise product over a `ChartChain`, its local-model bookkeeping (each internal breakpoint's
`+1`/`-1` orders cancel, §1.4), and the KEY telescoped integral identity.

### D5 — no global `∬_X` (a deliberate, CC6-driven scoping choice)

Forster's formula `∫_c ω = (1/2πi) ∬_X (df/f) ∧ ω` needs a *global* area-integral on `X`, which
`paths-and-integrals`'s own CC6 scope note explicitly rules out project-wide ("NO measure-
theoretic integration on `X`; the only integration is planar"). **We do not build one.** The
*actual role* this formula plays in 20.7's proof is (i) to let one work chart-by-chart (each
`dfⱼ/fⱼ` is compactly supported in its own chart), and (ii) to re-express the path integral as
data intrinsic to `f`'s *own* chart-local log-derivative, for `abel-theorem`'s later translation
into the project's own (non-Hodge) Serre-duality substitute. **We deliver exactly that
re-expression** — the telescoped sum over `ChartChain` pieces, `Σⱼ (gⱼ(bⱼ) − gⱼ(aⱼ))` — which is
provably equal to `pathIntegral γ ω` (§7.2, free from `Path`'s own machinery, no Stokes needed for
*this* equality) **and** provably equal, chart-piece by chart-piece, to a residue-type expression
in `f`'s own log-derivative coefficient via §1.3's Lemma-20.3 computation (§7.3, Stokes-driven).
`abel-theorem` gets **both** packagings and picks whichever it needs for its own Serre-duality
translation; neither packaging requires inventing a global 2-form integral on `X`.

---

## 6. The exp-gluing engine (the single-chart construction, `PlanarLogBranch.lean` + `SingleChart.lean`)

### 6.1 The planar log-branch lemma — the engine, spiked

**Disk case** (the atom actually spiked, §9): for `h : ℂ → ℂ` differentiable and non-vanishing on
`ball c₀ r`, there is `L : ℂ → ℂ` with `HasDerivAt L (deriv h z / h z) z` for `z ∈ ball c₀ r` and
`Complex.exp (L z) = h z` there. **Proof** (spiked, ~35 lines): `deriv h / h` is differentiable on
the ball (`h` differentiable + non-vanishing, via `AnalyticOnNhd.deriv` for the numerator);
`DifferentiableOn.isExactOn_ball` (mathlib, Morera) gives a primitive of `deriv h / h`, and
`IsExactOn.with_val_at` normalizes it to `L c₀ = Complex.log (h c₀)` (any nonzero complex number
has a `Complex.log`, `Complex.exp_log`). Then `φ z := h z * Complex.exp (-(L z))` has `HasDerivAt
φ 0 z` everywhere on the ball — product rule + `L`'s own defining derivative, the numerator/
denominator cancellation closed by `field_simp; ring` given `h z ≠ 0` — hence `φ` is constant on
the (convex) ball (`Convex.is_const_of_fderivWithin_eq_zero`, mathlib), and `φ c₀ = h c₀ *
Complex.exp (-Complex.log (h c₀)) = 1` (`Complex.exp_log` + `mul_inv_cancel₀`). So `φ ≡ 1`, i.e.
`h z * Complex.exp(-(L z)) = 1`, i.e. `Complex.exp (L z) = h z`. **No branch-cut case analysis on
`Complex.log`/`Complex.arg` anywhere** — the same "zero-derivative ⇒ constant ⇒ solved for" shape
`RS.Monodromy.exp_eq_holoRepr_of_isPrimitiveAlong` uses, but here entirely in the plane, no charts,
no `ℳ X`.

**Exterior case** (what Forster's construction actually needs — the annulus/`∞`-neighbourhood log
branch of `(z-b)/(z-a)`, for `a, b` inside a fixed radius `ρ`): the key move, reducing the annulus
to a genuine disk with **no puncture at all** (stronger than "simply connected", and why no
homotopy-invariance corollary is needed): substitute `w = 1/z`. Set
`H(w) := (1 - b*w) / (1 - a*w)`. Since `|a|, |b| < ρ`, `H`'s only pole (`w = 1/a`) and only zero
(`w = 1/b`) have `|1/a|, |1/b| > 1/ρ`, i.e. **both lie outside** `ball (0:ℂ) (1/ρ)` — so `H` is
genuinely differentiable and non-vanishing on the **whole** ball `ball 0 (1/ρ)`, including at
`w = 0` (`H(0) = 1`, matching `(z-b)/(z-a) → 1` as `z → ∞`, but this is not even needed as a
separate fact — `H` is simply an honest rational function there, no removable-singularity repair).
Apply the disk lemma to get `L̃` with `Complex.exp (L̃ w) = H w` on `ball 0 (1/ρ)`. Define
`L z := L̃ (z⁻¹)` for `z` with `ρ < ‖z‖` (so `z⁻¹ ∈ ball 0 (1/ρ)`, and `z ≠ 0`). Chain rule
(`HasDerivAt.comp` with `hasDerivAt_inv`, standard) gives `L`'s derivative; **direct algebra check**
(spiked mentally, not separately re-spiked — see §9 for why): `H'(w)/H(w) · (-1/w²)` at `w = 1/z`
equals `1/(z-b) - 1/(z-a)` exactly (both sides computed independently, matched by hand in §6's
derivation above — a `field_simp`/`ring` closes it in Lean, no new mathematical content beyond
what the spike already exercises for the disk case). And `Complex.exp (L z) = Complex.exp (L̃
(z⁻¹)) = H(z⁻¹) = (1 - b/z)/(1 - a/z) = (z-b)/(z-a)` (`field_simp`, using `z ≠ 0`). **This is the
"engine" the task brief asks for, made concrete and self-contained**: no annulus topology, no
winding number, no `π₁`, just one substitution turning an exterior region into a disk with no
excluded point, then the already-spiked disk lemma.

```lean
theorem exists_exteriorLogBranch {a b : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (ha : a ∈ ball (0:ℂ) ρ) (hb : b ∈ ball (0:ℂ) ρ) :
    ∃ L : ℂ → ℂ, (∀ z : ℂ, ρ < ‖z‖ → HasDerivAt L (1/(z - b) - 1/(z - a)) z) ∧
      ∀ z : ℂ, ρ < ‖z‖ → Complex.exp (L z) = (z - b) / (z - a)
```

### 6.2 The single-chart weak solution, `exists_weakSolutionOfPair_chart`

Given a chart `e` with `a := e A`, `b := e B` distinct points inside `ball 0 ρ ⊆ ball 0 1 ⊆
e.target` (`ρ < 1`), and a `ContDiffBump` `ψ` centred at `0` with `ψ.rIn =: ρ'` (`ρ < ρ'`),
`ψ.rOut =: ρ''` (`ρ' < ρ'' < 1`):

```lean
noncomputable def chartWeakSolution (a b : ℂ) (L : ℂ → ℂ) (ψ : ℝ → ℝ) (z : ℂ) : ℂ :=
  if ‖z‖ ≤ ρ then (z - b) / (z - a) else Complex.exp ((ψ ‖z‖ : ℂ) * L z)
```

**Proof plan (~50–70 lines).**
1. **Consistency on the overlap `{ρ < ‖z‖ ≤ ρ'}`**: `ψ ≡ 1` on all of `closedBall 0 ρ'`
   (`ContDiffBump.one_of_mem_closedBall`), so for `‖z‖ ≤ ρ'`, `chartWeakSolution`'s second branch
   reads `Complex.exp (L z) = (z-b)/(z-a)` (§6.1) — **identically equal**, as functions, to the
   first branch's formula on the whole region `ρ < ‖z‖ ≤ ρ'` (not merely continuous at one circle
   — literally the same analytic expression), so the piecewise definition is `ContDiffOn ℝ ⊤`
   (in fact holomorphic) across the transition with **no matching argument needed beyond
   `Set.EqOn`-rewriting**, unlike a generic bump-glued construction.
2. **`≡ 1` for `‖z‖ ≥ ρ''`**: `ψ ≡ 0` there (`ContDiffBump`'s defining property), so
   `Complex.exp (0 * L z) = Complex.exp 0 = 1` regardless of `L z`'s value (junk-safe: `L` is only
   ever *claimed* correct for `ρ < ‖z‖`, but the formula is well-defined — a total `ℂ → ℂ`
   expression — everywhere, and multiplying by `ψ z = 0` erases any junk).
3. **Smoothness**: `ContDiffOn ℝ ⊤` on `{‖z‖ ≤ ρ'}` (first branch, a rational function, poles at
   `a, b` both **outside** this closed ball since `a, b ∈ ball 0 ρ` and `ρ < ρ'`); `ContDiffOn ℝ ⊤`
   on `{ρ < ‖z‖}` (second branch: `ψ` is `ContDiff ⊤` everywhere by construction, `L` is
   `ContDiffOn` there since it has a derivative at every point, `Complex.exp` is entire — product/
   composition); the two opens `{‖z‖ < ρ'+δ}` and `{‖z‖ > ρ}` (for small `δ`) cover `ℂ` and the
   two formulas agree on the overlap (step 1) — standard `ContDiffOn`-gluing on an open cover,
   the same two-piece pattern `PlanarStokes/Compat.lean`'s `ContDiffOn.contDiff_of_hasCompactSupport`
   already established for an analogous "glue smooth-on-`U`, glue constant/zero-elsewhere"
   argument (reused as a *pattern*, not a citation — that lemma is about compact support and
   `ℂ → ℂ`; ours is a two-open-cover gluing of two already-agreeing `ContDiffOn` pieces, a strictly
   simpler standard fact, `ContDiffOn.of_union` given `EqOn` on the overlap, or by hand if no
   direct mathlib lemma of that exact shape is found — flagged as risk R2, §8).
4. **Zero/pole structure**: at `a`, `chartWeakSolution` (first branch, `‖z‖ ≤ ρ` region) is
   literally `(z-b)/(z-a)` — matches `IsWeakSolutionAt _ A 1`'s local model directly (`ψ_{weak}(z)
   := (z-b)/(z-a) * (z-a) / (z-a)`... concretely: near `a`, `(z-b)/(z-a) = (z-b) \cdot (z-a)^{-1}`,
   i.e. it is **already** `(nonvanishing smooth) · (z-a)^{-1}`?? — careful: we want order `+1` at
   `A` (`P`, a zero) and order `-1` at `B` (`Q`, a pole); `(z-b)/(z-a)` has a **simple zero** at `b`
   and a **simple pole** at `a` — so with `A ↦ a` we get order `-1` at `A`... **the labelling must
   be checked against which of `A, B` is `P` (order `+1`, the zero) and which is `Q` (order `-1`,
   the pole)**: set `b := e P` (the **zero**), `a := e Q` (the **pole**) — matching Forster's own
   labelling ("`b := c(1)`" = the path's endpoint = our `P`; "`a := c(0)`" = the start = our `Q`).
   With this labelling, near `Q` (`z` near `a`): `(z-b)/(z-a) = ψ_Q(z) \cdot (z-a)^{-1}` with
   `ψ_Q(z) := (z-b)` (smooth, `ψ_Q(a) = a - b ≠ 0`) — matches `IsWeakSolutionAt _ Q (-1)`. Near `P`
   (`z` near `b`): `(z-b)/(z-a) = ψ_P(z) \cdot (z-b)^{1}` with `ψ_P(z) := 1/(z-a)` (smooth,
   nonvanishing near `b` since `a ≠ b`) — matches `IsWeakSolutionAt _ P 1`. ∎
5. **Non-vanishing off `{P, Q}`**: on `‖z‖ ≤ ρ`, `(z-b)/(z-a) = 0 ⟺ z = b`, and `z ≠ b` is exactly
   `z ≠ P`'s image (given); on `‖z‖ > ρ`, `Complex.exp(\cdots) ≠ 0` always (`Complex.exp_ne_zero`).

### 6.3 Globalizing to `X`

`f(x) := chartWeakSolution(e x)` for `x ∈ e.source`, `f(x) := 1` for `x ∉ e.source`. Well-defined
and `ContMDiff`/`IsWeakSolutionOfPair`-compatible globally by the same two-piece gluing idea
(§6.2 step 3, now one level up: `e.source` and `X \ e.symm '' (closedBall 0 ρ'')` are two opens
covering `X`, agreeing — both `≡ 1` — on the overlap `e.source \ e.symm '' (closedBall 0 ρ'')`).
`f ≡ 1` outside the compact set `K := e.symm '' (closedBall 0 ρ'') ⊆ e.source` (the "relatively
compact `U`" of Lemma 20.5's statement, concretely `U := e.symm '' (ball 0 ρ'')`, `closure U ⊆
e.symm '' (closedBall 0 ρ'') = K` compact).

---

## 7. The chain-assembly engine (`ChainAssembly.lean`, the deliverable)

### 7.1 Statement

```lean
namespace RS.AbelWeak

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The deliverable.** For distinct `P Q : X` and any path `γ : Q ⟶ P`: a weak solution `f` of
the pair `(P,Q)`, equal to `1` outside a relatively compact open neighbourhood of `γ`'s image. -/
theorem exists_weakSolutionOfPair {P Q : X} (hPQ : P ≠ Q) (γ : Path Q P) :
    ∃ (f : X → ℂ) (U : Set X), RS.AbelWeak.IsWeakSolutionOfPair f P Q ∧
      IsOpen U ∧ IsCompact (closure U) ∧ Set.range γ ⊆ U ∧ (∀ x ∉ U, f x = 1)
    -- proof plan: §6.3 (single chart) + §1.4's product-over-`ChartChain` assembly

/-- **The CC6-compliant replacement for Forster's `∬_X`-formula (D5).** For any HOLOMORPHIC
`ω : Form1 X` and any `ChartChain` `C` adapted to `γ`, `pathIntegral γ ω` is *exactly* the finite
telescoped sum of chart-local holomorphic-primitive differences — `g k` is any caller-supplied
holomorphic primitive of `ω`'s chart-`k` coefficient on `C`'s `k`-th ball (existence:
`RS.exists_hasDerivAt_ball` + `Form1.analyticOnNhd_coeffIn`, already built, not re-derived here). -/
theorem pathIntegral_eq_sum_chartChain (C : RS.ChartChain γ) (ω : RS.Form1 X)
    (g : (k : ℕ) → ℂ → ℂ)
    (hg : ∀ k, k < C.n → ∀ z ∈ Metric.ball (C.c k) (C.r k),
      HasDerivAt (g k) (RS.coeffIn (C.e k) ω z) z) :
    RS.pathIntegral γ ω =
      ∑ k ∈ Finset.range C.n, (g k (C.e k (γ.extend (C.t (k+1)))) - g k (C.e k (γ.extend (C.t k))))

end RS.AbelWeak
```

`pathIntegral_eq_sum_chartChain` is stated for a fixed `ω` and a **caller-supplied** per-piece
primitive family `g` (its existence is `RS.exists_hasDerivAt_ball`/`Form1.analyticOnNhd_coeffIn`'s
own job, already built — not re-derived here, just invoked at the call site once, per `ω`).

### 7.2 Proof plan: `pathIntegral_eq_sum_chartChain` (~45 lines, free of Stokes)

This is **not** a Stokes-theorem consequence — it is a direct corollary of `paths-and-integrals`'s
own `IsPrimitiveAlongMap` API, telescoped over the chain, matching how `exists_isPrimitiveAlong`'s
own existence proof is *built* (§3.2 of `paths-and-integrals.md`) but assembled here from the
**exported** API only (`rechart`, `sub_eq_sub`, `isPrimitiveAlongMap_of_ball`), not by reaching
into `Continuation.lean`'s internal induction.

1. **Obtain a global primitive.** `⟨F, hF, hF0⟩ := RS.exists_isPrimitiveAlong γ ω`
   (`IsPrimitiveAlong γ ω F`, `F 0 = 0`); `RS.pathIntegral γ ω = F 1 - F 0 = F 1` by
   `IsPrimitiveAlong.pathIntegral_eq`.
2. **Per-piece cell primitive.** For each `k < C.n`, `Gₖ := fun u => g k (C.e k (γ.extend u))` is
   `IsPrimitiveAlongMap γ.extend ω Gₖ (Icc (C.t k) (C.t (k+1)))` — directly
   `RS.isPrimitiveAlongMap_of_ball (C.he k) (hg k _) (fun u hu => C.maps k u hu)` (no new proof,
   exact citation of the already-built cell-primitive atom, ChartChain's own `maps` field supplies
   the hypothesis verbatim).
3. **Compare `F` and `Gₖ` on the sub-interval.** `F` restricted to `Icc (C.t k) (C.t (k+1))` is
   `IsPrimitiveAlongMap γ.extend ω F _` by `.mono` (from `hF : IsPrimitiveAlong γ ω F`, i.e. on
   `univ`); `Icc (C.t k) (C.t (k+1))` is preconnected (`isPreconnected_Icc`) and `γ.extend` is
   continuous; `IsPrimitiveAlongMap.sub_eq_sub` gives, for the two endpoints `t := C.t k`,
   `t' := C.t (k+1)`: `F t' - Gₖ t' = F t - Gₖ t`, i.e.
   `F (C.t (k+1)) - F (C.t k) = Gₖ (C.t (k+1)) - Gₖ (C.t k) = g k (C.e k (γ.extend (C.t (k+1))))
   - g k (C.e k (γ.extend (C.t k)))` (the constant `F t - Gₖ t` cancels — `sub_eq_sub`'s whole
   point).
4. **Telescope.** `F 1 = F (C.t C.n) = Σ_{k<C.n} (F (C.t (k+1)) - F (C.t k))`
   (`Finset.sum_range_succ_comm`/a direct `Finset.sum_Ico_eq_sub`-style telescoping identity on `ℤ`
   indices, or a two-line induction on `C.n` using `C.ht1`/`C.ht0` to anchor the ends — routine).
   Combine with step 3 termwise: `F 1 = Σₖ (g k (...) - g k (...))`. Combine with step 1: done. ∎

**No PlanarStokes import in this proof** — it is pure `Path`-API bookkeeping. This is the
"telescoped path-integral" half of D5's two packagings.

### 7.3 Proof plan: relating the telescoped sum to `f`'s own log-derivative (Lemma 20.3, specialized `n = 2`, ~55 lines)

For `abel-theorem`'s later use (translating `(*)` into a statement about `f`'s `d''f/f`, §1.6), we
also export the *per-piece* identity connecting `g k (bₖ) - g k (aₖ)` (a primitive-difference,
`§7.2`'s vocabulary) to a **residue-type expression in `fₖ`'s own chart-local log-derivative
coefficient**, where `fₖ := chartWeakSolution` for that piece (§6). Since `ω` is holomorphic,
`g k` (a primitive of `ω`'s chart-`k` coefficient, i.e. `HasDerivAt (g k) (coeffIn (C.e k) ω) z`) is
itself **holomorphic** on `ball (C.c k) (C.r k)`, so `d(g k)` has **no `dz̄` part**: writing
`ℓₖ(z) := logDerivCoeff fₖ z` (the chart-`k` coefficient of `dfₖ/fₖ`, a genuine `ℂ → ℂ` function,
smooth off `{aₖ, bₖ}`, computable directly from the §6 construction: `ℓₖ = (deriv fₖ)/fₖ`), the
wedge product `dfₖ/fₖ ∧ d(g k)` has only its `(0,1)∧(1,0)` term survive (`(1,0)∧(1,0) = 0`
identically on a Riemann surface — no room for two independent holomorphic directions), i.e. the
computation reduces to **`d''fₖ/fₖ`** (Wirtinger-`∂̄` of `log fₖ`) paired against `(g k)'`.

1. **Bulk vanishing.** Off a small neighbourhood of `{aₖ, bₖ}`, `fₖ ≡ (z-bₖ)/(z-aₖ)`-adjacent or
   `≡ 1` (§6.2 steps 1–2), both **holomorphic**, so `d''fₖ/fₖ ≡ 0` there
   (`RS.wirtingerDbar_eq_zero_of_differentiableAt`, Dbar, applied to `log`-derivative of a
   holomorphic nonvanishing function — or more directly, `RS.integral_wirtingerDbar_mul_eq_zero_
   of_differentiableOn`, **Atom 1b**, applied with the ambient smooth bump role played by `ψ`
   itself, since `d''fₖ/fₖ`'s only non-holomorphic dependence traces back to `ψ`'s own
   `∂̄ψ`-contribution, and `ψ ≡ 1`/`ψ ≡ 0` (constant, hence `∂̄`-trivial) away from the transition
   annulus `{ρ < ‖z‖ < ρ''}`).
2. **Residue at `aₖ`, at `bₖ`.** Inside the transition annulus and the two small disks around
   `aₖ, bₖ`, `d''fₖ/fₖ`'s only support (as a compactly-supported-within-the-chart `(0,1)`-form) is
   exactly the `∂̄ψ`-weighted piece from §6.2's cutoff construction — **Atom 2**
   (`RS.integral_wirtingerDbar_mul_eq_neg_pi_mul_resAt`), applied with the meromorphic factor
   `f := fun z => 1/(z - bₖ) - 1/(z - aₖ)` (`fₖ`'s log-derivative in the "inner" region, a
   genuinely meromorphic function with simple poles at `aₖ` (residue `-1`) and `bₖ` (residue
   `+1`) — `resAt`'s own additivity/`resAt_sub`, `ResidueCalculus`, built) and `g := g k`
   (**locally constant hypothesis**: not literally true of a general holomorphic primitive, so
   this step is stated with `g k`'s actual **value** `g k (aₖ)`/`g k (bₖ)` playing the role Atom
   2's `g p` plays, via the standard "replace `g` by its first-order Taylor approximation near the
   puncture, the error term vanishes in the `ε → 0` limit" refinement Atom 2's own `D4` already
   flags as the general (not the `hconst`-restricted) case — **this is the one place this unit's
   proof plan needs slightly more than Atom 2 ships today, flagged as risk R1, §8, with the
   concrete mitigation**: use Atom 2 literally with `g` REPLACED by the CONSTANT `g k aₖ` (an
   admissible substitution since we only want the "constant term" contribution, and the
   *difference* `g k - const` contributes a term that itself vanishes in the annulus-shrinking
   limit by a first-order/Lipschitz estimate on the derivative-bounded remainder — exactly Atom 2's
   own §D4 discussion of why the general case needs more than the constant-`g` formula, but
   *bounded* here, not open-ended, since we only ever need the residue-`(-1,+1)`-weighted
   linear term, not a higher-order expansion).
3. **Assemble.** `Res_{aₖ}(dfₖ/fₖ) = -1`, `Res_{bₖ}(dfₖ/fₖ) = +1` (direct from the explicit
   log-derivative formula, §6.1's `1/(z-b) - 1/(z-a)` shape, no limiting argument needed for the
   *residues themselves* — only for matching them against `g k`'s value via Atom 2's area
   integral); combining steps 1–2 gives `(1/2πi) ∬_{U_k} (dfₖ/fₖ) ∧ (g k)' \, dz = g k (bₖ) - g k
   (aₖ)`, matching Forster's Lemma 20.3 at `n = 2`. ∎

This proof plan is intentionally the **harder, Stokes-driven** half (matching the task's "40+
lines" ask for the residue engine) and is flagged (R1, §8) as the one place where Atom 2's current
`hconst` hypothesis needs a small refinement (or a direct re-derivation specialized to `g` linear
near the puncture, cheaper than the fully general case Atom 2's own `D4` declines) — **not** a gap
in `planar-stokes-atoms`'s atoms themselves, which are correct and sufficient for the
constant-cutoff pieces (§7.3 step 1); only the *value-matching* refinement in step 2 is new content
this unit must supply, clearly scoped and bounded (not the general "higher Taylor coefficients"
problem Atom 2's `D4` explicitly declines to solve).

---

## 8. File plan

| # | File | Content | Est. lines |
|---|------|---------|-----------|
| 1 | `AbelWeak/WeakSolution.lean` | `IsWeakSolutionAt`, `IsWeakSolutionOfPair` (D1), multiplicativity lemma (product of weak solutions of disjoint pairs), `logDerivCoeff` | ~120 |
| 2 | `AbelWeak/PlanarLogBranch.lean` | The disk lemma (spiked) + `exists_exteriorLogBranch` (§6.1); no manifold imports | ~110 |
| 3 | `AbelWeak/SingleChart.lean` | `chartWeakSolution`, `exists_weakSolutionOfPair_chart` (§6.2–6.3) | ~220 |
| 4 | `AbelWeak/ChainAssembly.lean` | `exists_weakSolutionOfPair` (the deliverable), `pathIntegral_eq_sum_chartChain` (§7.2), the Lemma-20.3-specialized residue identity (§7.3) | ~260 |
| 5 | `Jacobian/AbelWeak.lean` | unit root, API docstring, DAG-audit note, scope-split note (#24 vs #29) | ~45 |

Total ≈ 750 lines, inside the project's per-file budget (`CONVENTIONS.md`: "keep files under ~800
lines"). Build order: file 2 is fully independent (pure mathlib + `Path/Planar.lean`'s cited
facts); file 1 is independent of 2–3; file 3 needs 1–2; file 4 needs 1–3 plus
`planar-stokes-atoms`. No file needs `monodromy`, `form-trace-tower`, or `canonical-forms`.

---

## 9. Spike report (`scratch_abelweak.lean`, project root)

Gate respected (`pgrep -cx lean` = 2 at run time, under the limit of 3). `lake env lean
scratch_abelweak.lean`: **compiles clean, exit 0** (two informational linter warnings — an unused
`ext` pattern and an unused `simp` argument — no `error:`-level output, zero sorries).

Content (≤ 50 lines, per the gate): the disk case of §6.1's log-branch lemma, in full — given `h`
`DifferentiableOn ℂ` and non-vanishing on `ball c₀ r`, produces `L` with `HasDerivAt L (deriv h z /
h z) z` on the ball and `Complex.exp (L z) = h z` there. Verified end-to-end: (1)
`(hh.analyticOnNhd isOpen_ball).deriv.differentiableOn` gives differentiability of `deriv h`
(confirms the exact mathlib name — `AnalyticOnNhd.deriv`, not obvious without the spike);
(2) `DifferentiableOn.isExactOn_ball` + `IsExactOn.with_val_at` produce the normalized primitive
`L`, `L c₀ = Complex.log (h c₀)`; (3) the zero-derivative computation for `φ z := h z *
Complex.exp(-(L z))` closes by `field_simp; ring` given `h z ≠ 0`, confirming no hidden side
condition beyond nonvanishing; (4) `Convex.is_const_of_fderivWithin_eq_zero` (mathlib,
`MeanValue.lean:558`) applied with `𝕜 := ℂ` gives `φ` constant on the ball from
`fderivWithin_of_isOpen` + `HasFDerivAt.fderiv`; (5) `Complex.exp_log`/`mul_inv_cancel₀` close
`φ c₀ = 1`; (6) the final rearrangement `exp(L z) = h z` follows from `φ z = φ c₀ = 1` by
multiplying through by `exp(L z)` and simplifying `exp(-(L z)) * exp(L z) = 1`
(`neg_add_cancel`/`Complex.exp_zero`). This is the **entire** mathematical content of the
"exp-gluing engine" (§6.1's exterior case is a mechanical inversion-transport of this same fact,
not separately risky — the chain-rule algebra was checked by hand in §6.1's derivation and needs
no new mathlib lemma beyond `HasDerivAt.comp`/`hasDerivAt_inv`, both standard). The two mathlib
name traps the spike surfaced (recorded so the real builder does not rediscover them): (a)
`AnalyticOnNhd.differentiableOn` does **not** take an `n`-parameter the way one might guess from
its docstring — the un-truncated `AnalyticOnNhd.deriv.differentiableOn` composite is what is
needed; (b) `Convex.is_const_of_fderivWithin_eq_zero`'s `hf'` hypothesis is phrased via
`fderivWithin`, not `HasFDerivAt`/`fderiv` directly — bridge through `fderivWithin_of_isOpen`
first.

---

## 10. Coordination notes filed (no blueprint edit made)

* **DAG correction** (§2.5): `abel-weak-solutions`'s `Builds on:` is tightened, on inspection, to
  `paths-and-integrals, planar-stokes-atoms`. `monodromy` and `form-trace-tower` are not imported
  by any file here; both remain available to `abel-theorem` directly. Flagged for the
  orchestrator's awareness, matching the precedent `monodromy.md`/`form-trace-tower.md`/
  `proper-map-degree.md`/`sphere-topology.md` already set for their own edges.
* **`planar-stokes.md` §11 correction**: this unit needs **both** Atom 1b and Atom 2 (the residue
  atom), not "Atom 1 alone... not a residue computation" as that design doc's own downstream-map
  guess states. No change needed to `planar-stokes-atoms`'s atoms themselves (they are exactly
  right, §7.3); only to the guess about which one gets used.
* **`meromorphic-and-divisors`**: not a hard dependency of this unit either (§3); noted for the
  orchestrator, no action needed (the blueprint never listed it as a dependency of this unit in the
  first place — this is a confirmation, not a correction).
* **Third-kind-differential alternative** (§4): documented as a correct-but-gated alternative
  construction for whichever future builder takes on `abel-theorem`, with its exact gates
  (`riemann-roch`, `cech-h1-genus`'s `l(K)=g`, the residue theorem `Σ Res = 0`) spelled out, so no
  one re-derives the dimension count from scratch only to discover the same gates.
* **Atom 2's `hconst` refinement** (§7.3, risk R1): a small, bounded extension of `planar-stokes-
  atoms`'s Atom 2 (matching `g` against its own *value* at the puncture via a linear/Lipschitz
  remainder estimate, not the fully general higher-Taylor-coefficient case Atom 2's own `D4`
  explicitly declines) is needed for the Lemma-20.3-specialized residue identity (§7.3 step 2).
  Filed as a request to `planar-stokes-atoms` (a natural, cheap corollary of its own Atom 2 proof,
  concretely bounded to first order) — or, if that unit is finished and unavailable for
  extension, provable locally in a marked `Compat` section here per `CONVENTIONS.md` rule 4.

---

## 11. Risks (ranked)

1. **MEDIUM — R1, Atom 2's `hconst`-refinement for Lemma 20.3's `g`-value matching** (§7.3 step 2,
   §10). The one place this unit's proof plan needs slightly more than `planar-stokes-atoms`
   ships today, but the extension needed is small and bounded (linear remainder only, not the
   general case), and the fallback (prove it locally) is available per `CONVENTIONS.md` rule 4.
2. **LOW-MEDIUM — R2, the two-piece `ContDiffOn`-gluing lemma for §6.2 step 3 / §6.3.** No single
   named mathlib lemma of the exact "two `ContDiffOn`s on an open cover, agreeing on the overlap,
   glue to one `ContDiffOn`" shape was pinned down during this design (an analogous, but not
   identical, pattern is used by `PlanarStokes/Compat.lean`'s
   `ContDiffOn.contDiff_of_hasCompactSupport`). Low risk: this is textbook-standard (local
   `ContDiffAt` from either piece + `ContDiffOn` is local), a ~15-line direct proof if no
   ready-made lemma is found.
3. **LOW — the internal-breakpoint cancellation bookkeeping** (§1.4/§7): verifying that at each
   `ChartChain` junction, the `+1`-order (from the earlier piece's own endpoint model) and
   `-1`-order (from the next piece's own start-point model) genuinely cancel to give a smooth,
   non-vanishing `f` there (not merely "Forster says so") needs one explicit local computation
   (product of two weak-solution local models at the same point, opposite orders, is a smooth
   nonvanishing function there) — mechanical, no new idea, ~20 lines.
4. **LOW — labelling discipline** (§6.2 step 4): swapping which of `P, Q` plays the "zero" vs
   "pole" role relative to `a := c(0)`, `b := c(1)` is a one-time bookkeeping trap (already
   resolved and pinned down explicitly in §6.2 step 4 — flagged so the builder does not
   re-derive it under time pressure and get a sign/order backwards).
5. **LOW — multi-builder churn** (standard, per every sibling design doc's own risk section):
   re-verify `RS.ChartChain`'s exact field names, `RS.isPrimitiveAlongMap_of_ball`'s exact
   hypothesis shape, and `planar-stokes-atoms`'s Atom 1b/Atom 2 exact signatures against disk
   immediately before writing code depending on them (all re-verified against the actual files on
   disk during this design, §1.3/§2.1–2.2/§7.2 cite line-accurate current signatures, but this is a
   concurrently-built repository).

---

## 12. Downstream map

| Consumer | What it needs | Our export |
|---|---|---|
| **abel-theorem** (#29, primary) | The weak solution `f` of `(P,Q)` for a chosen path `γ`, its known local models at `P`/`Q`, and the telescoped path-integral identity (to translate the period-vanishing hypothesis `(*)`/`Jacobian.ofCurve`-equality into an explicit statement about `∫_γ ω`); for its own Dolbeault-substitute step, the per-piece residue identity connecting that to `f`'s chart-local log-derivative | `RS.AbelWeak.exists_weakSolutionOfPair`, `RS.AbelWeak.IsWeakSolutionOfPair`, `RS.AbelWeak.pathIntegral_eq_sum_chartChain`, the §7.3 residue identity |
| **period-lattice-rank** (#31) | No direct edge (blueprint: `Builds on: abel-theorem` only). Any relevance is transitive through `abel-theorem`. Nothing here is stated in period-lattice-rank's own vocabulary (real period-matrix nondegeneracy, §21.3–21.4) — read in full (§0), confirmed to share **no machinery** with this unit beyond both ultimately feeding off `paths-and-integrals`' `periodVector`/`ChartChain`, already-shared infrastructure, not anything new this unit contributes | — (no direct export) |
| **monodromy**, **form-trace-tower** | Nothing (§2.3–2.4; both are upstream/independent, not consumers) | — |

No other unit needs anything from `abel-weak-solutions` per the current blueprint edges.
