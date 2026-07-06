# Design: canonical-forms (`Jacobian/CanonicalForms/`)

Blueprint unit **canonical-forms**. Blueprint text: "Meromorphic 1-form systems and the
**canonical divisor `K`**: removable singularities, differentials of canonical forms, and — via
the χ ledger — **existence of a nonconstant meromorphic function** and a nonzero `ω₀`. Strategy:
`χ(D) → ∞` with `deg D` forces `L(D)` nonzero, giving the first nonconstant meromorphic function;
its differential seeds `K`." ⚠ "Existence of `ω₀`/nonconstant `f` is a *consequence* of
finiteness + χ, not an assumption; this is where finiteness pays off." **Builds on:**
finiteness-and-chi, residue-calculus. References: Forster §16 (PDF 132–137, Riemann–Roch/divisors),
§17.4 (PDF 140, the sheaves `Ω_D ≅ O_{D+K}`); Miranda Ch. V.3 (PDF 158, `L`/`L⁽¹⁾`/Lemma 3.11),
Ch. VI (PDF 181–206, Laurent tails).

One gated end spike (`scratch_canon.lean`, project root) compiled clean — §8.

---

## 0. The representation call (read first)

The blueprint has **no existing type** for a general meromorphic 1-form. Two places already touch
the question and both explicitly punt it here:

- `docs/design/holomorphic-forms.md` §5 (downstream consumers): "`Form1` stays HOLOMORPHIC;
  meromorphic 1-forms are later pairs `(f, η)` ~ `f • η` — only `Form1.smulFun` and `coeffIn`
  transition data are consumed from here. Do not add meromorphic sections to this unit."
- `docs/design/form-trace-tower.md` D1: "Meromorphic 1-forms have no type yet (owned by
  canonical-forms). Building that general system here would be badly out of scope... this does
  not give a way to trace `h·ω` for an arbitrary meromorphic `ω`... that would need
  canonical-forms's future general system."

**The naive reading of holomorphic-forms.md's `f • η` remark is wrong as a *definition*.** `f • η`
for a *fixed* reference `η` presupposes a nonzero global reference already exists — but genus-0
surfaces have `Form1 X = 0` (no nonzero *holomorphic* forms at all; e.g. `dz` on `ℙ¹` has a double
pole at `∞`, so the reference itself must be allowed poles), and more importantly *this unit's own
job* is to manufacture the first reference from nothing but finiteness + χ. A type that already
needs a chosen nonzero form to be stated cannot be the definition used to prove one exists.

**Decision (mirrors dbar's `Form01`, generalized to allow poles):** a meromorphic 1-form is a
**point-indexed (`chartAt`) coefficient family**, exactly `Form01`'s shape
(`docs/design/dbar-solvability.md` D5, D8 — read in full, §1.1 below), with:
- `AnalyticOnNhd`/`ContDiffOn` (Form1/Form01) replaced by `MeromorphicOn` (mathlib, allows poles);
- the transition rule `deriv τ` (no conjugate — 1-forms are type `(1,0)`, unlike `Form01`'s
  `(0,1)`, so the transition matches `Form1.coeffIn_trans`, not `Form01`'s `conj (deriv τ)` rule).

This is `MForm X` (§2 D1). It reuses **zero** of Form1's bundled-section machinery (checked: a
bundle section is a *total* function into the Hom-bundle; a coefficient with a pole has no value
to put there — `Form1.smulFun`, quoted above, only ever multiplies a holomorphic reference by a
holomorphic scalar, which is why it stays inside `Form1`; it cannot represent an actual pole). The
chart-family/structure route is the *only* workable one, confirming the task brief's own
steer and dbar's already-established, spike-verified pattern (`Form01` design, not yet built on
disk — `Jacobian/Dbar/` has only the planar `Wirtinger`/`CauchyKernel`/`SolveDisk` files at design
time; `MForm` mirrors its *design*, does not depend on its code).

**The one genuinely new technical wrinkle** (absent from Form1/Form01, which have no poles):
`compat`, as a literal pointwise equation of coefficient *values*, must still hold **at points
where the coefficient has a pole** (not just on the open dense complement). §2 D6/§5 P1 resolve
this: `deriv` is `0`-junk off `DifferentiableAt`, and differentiability-*failure* is chart-
invariant (composing with a biholomorphic transition can't create or destroy it), so `compat`'s
two sides collapse to the *same* junk `0` at poles, and to the honest chain rule elsewhere. This
lemma is spike-verified (§8, item 4) and is the riskiest single piece of the unit.

---

## 1. Facts relied on (verified against files on disk)

### 1.1 The `Form01` design pattern (dbar-solvability, design-only — mirror, not import)

`docs/design/dbar-solvability.md` §D5/§D8 (`Jacobian/Dbar/Form01.lean`, not yet on disk):
```lean
structure Form01 (X) [...] where
  coeffAt : X → ℂ → ℂ
  coeffAt_zero_off : ∀ x, ∀ z ∉ (chartAt ℂ x).target, coeffAt x z = 0
  contDiffOn_coeffAt : ∀ x, ContDiffOn ℝ ∞ (coeffAt x) (chartAt ℂ x).target
  compat : ∀ x y, ∀ z ∈ chartAt ℂ y '' ((chartAt ℂ x).source ∩ (chartAt ℂ y).source),
    coeffAt y z = conj (deriv (chartAt ℂ x ∘ (chartAt ℂ y).symm) z) * coeffAt x (chartAt ℂ x (...))
```
Point-indexed (not atlas-indexed): "every consumer works through `chartAt`... a plain `X`-indexed
Pi avoids `∀ e ∈ atlas` dependent-family friction." `Form01CoeffData`/`Form01.ofCoeffs` mirror
`Form1CoeffData`/`Form1.ofCoeffs` with `AnalyticOnNhd ↦ ContDiffOn ℝ ∞`. `MForm` transcribes this
with `ContDiffOn ↦ MeromorphicOn`, `conj (deriv τ) ↦ deriv τ` (no conjugate).

### 1.2 `Jacobian/Forms/` (holomorphic-forms, BUILT, zero sorries — verified at source)

- `RS.Form1 X` (`Basic.lean:33`, `abbrev`), `AddCommGroup`/`Module ℂ` instances (TC-found).
- `RS.coeffIn (e) (η) (z) : ℂ` (`Coeffs.lean:45`), `RS.coeffAt (x) (η) := coeffIn (chartAt ℂ x) η
  (chartAt ℂ x x)` (`:52`); `coeffIn_add/smul/zero/neg/sub`, `Form1.ext_coeffAt` (`:201`).
- `RS.coeffIn_trans {e e'} (he he' : mem maximalAtlas) (η) {z} (hz : z ∈ e' '' (e.source ∩
  e'.source)) : coeffIn e' η z = deriv (e∘e'.symm) z * coeffIn e η (e (e'.symm z))`
  (`Coeffs.lean:234`) — **THE transition rule `MForm`'s own `compat` mirrors.**
- `RS.differentiableAt_trans {e e'} (he he') {z} (hzt : z ∈ e'.target) (hzs : e'.symm z ∈
  e.source) : DifferentiableAt ℂ (e∘e'.symm) z` (`Coeffs.lean:212`) — the transition's own
  differentiability, spike-reused for `MForm`'s `deriv`-through-poles lemma (§5 P1).
- `RS.Form1.analyticOnNhd_coeffIn (η) {e} (he : mem maximalAtlas) : AnalyticOnNhd ℂ (coeffIn e η)
  e.target` (`Coeffs.lean:214`ish, §2.2 design) — spike-verified composes with mathlib's
  `AnalyticOnNhd.meromorphicOn` to give `MeromorphicOn`, the `d : Form1 ↪ MForm` bridge input.
- `RS.Form1CoeffData X ι` (chart/mem_maximalAtlas/exists_mem/coeff/analyticOnNhd/compat,
  `OfCoeffs.lean:35`), `RS.Form1.ofCoeffs`, `RS.Form1.coeffIn_ofCoeffs` (`:139`),
  `RS.Form1.coeffAt_ofCoeffs` (`:155`) — the exact shape `MFormCoeffData`/`MForm.ofCoeffs` mirror.
- `RS.mdifferential (f) (hf : ContMDiff ω f) : Form1 X`, `coeffIn_mdifferential`
  (`MDifferential.lean:50/63`) — the HOLOMORPHIC special case of `MForm.d`; ours drops the global
  `ContMDiff` hypothesis and allows `f` to be merely meromorphic.
- `RS.genus`, `genus_eq_zero_iff_subsingleton` (`Genus.lean`) — consumed by §7's `l K = g` export
  (owned by cech-h1-genus, we only supply the bridge).

### 1.3 `Jacobian/Meromorphic/` (meromorphic-and-divisors, BUILT, zero sorries — verified)

- `RS.MeromorphicAtX/MeromorphicOnX`, `RS.ordAtX`, chart invariance `RS.ordAtX_eq_of_mem_source`
  (`Predicates.lean:272`, proof template §5 P4 mirrors), `RS.meromorphicAtX_iff_of_mem_source`
  (`:250`), propagation `RS.eventually_ordAtX_eq_top`(`:231`)/`eventually_ordAtX_eq_zero` (`:314`,
  proof template §5 P2's local-finiteness step mirrors), `ContMDiffAt.meromorphicAtX/ordAtX_nonneg`.
- `RS.ℳ X := MeroGermOn X Set.univ` (`GermSpace.lean:69`), `MeroGermOn.mk/mk_eq_mk/exists_rep/ind`,
  ring/algebra ops, `MeroGermOn.restrict` (AlgHom, `:194`).
- `RS.MeroGermOn.ord (x) : WithTop ℤ` (`OrderEval.lean:37`), `RS.MeroGermOn.evalAt` (`:111`),
  `RS.MeroGermOn.holoRepr := fun x => φ.evalAt x` (`:225`) — **canonical, choice-free, total**
  representative; `holoRepr_eventuallyEq_nhdsNE` (`:229`, agrees with ANY representative on
  `𝓝[≠] x`), `meromorphicOnX_holoRepr` (`:297`, itself `MeromorphicOnX`, even though its *value* at
  poles is the junk `0` of `evalAt_of_not_nonneg`, `:144`), `mk_holoRepr` (`:305`).
- `RS.Divisor X := Function.locallyFinsuppWithin (Set.univ : Set X) ℤ` (`Divisor.lean:129`),
  `Function.locallyFinsuppWithin.degree` (`:30`, needs `[T2Space][CompactSpace]`),
  `MeroGermOn.divisorOn` (`:134`, `toFun x := (φ.ord x).untop₀`; local-finiteness proof via
  `eventually_ordAtX_eq_top/eq_zero` — **the exact template `MForm.divisor`'s own local-finiteness
  mirrors**, §5 P2), `RS.divisor : ℳ X → Divisor X` (`:195`), `divisor_mul/inv/smul/algebraMap`,
  `finite_support_divisor` (`:277`).
- `RS.LinSys D : Submodule ℂ (ℳ X)` (`LinearSystem.lean:52`), `RS.l D := finrank ℂ (LinSys D)`
  (`:98`), `mem_linSys_iff` (`:70`), `linSys_mono` (`:101`), `linSys_zero_eq_span_one` (`:139`),
  `l_zero` (`:162`), `LinSysOn` (`:222`).
- `RS.linSysMulEquiv [ConnectedSpace X] {φ : ℳ X} (hφ : φ ≠ 0) (D) : LinSys D ≃ₗ[ℂ]
  LinSys (D - divisor φ)` (`LinSysMulEquiv.lean:34`) — **the model** for `MForm`'s own
  ℳ(X)-multiplication equivalence (§2 D8/§4.5).
- `RS.instFieldMero [T2Space X][ConnectedSpace X] : Field (ℳ X)` (`Field.lean:82`),
  `Mero.ord_eq_top_iff` (`:58`, the **zero-class dichotomy** on a connected surface — the model
  for `MForm`'s own dichotomy, §2 D5/§5 P3).
- `RS.MeromorphicOnX.eventuallyEq_zero_or_forall_ordAtX_ne_top [T1Space][ConnectedSpace]`
  (`CodiscreteBridge.lean:110`) — **the exact clopen/connectedness proof skeleton** `MForm`'s own
  zero-dichotomy transcribes (§5 P3).
- `MeromorphicAt.deriv [CompleteSpace E] (h : MeromorphicAt f x) : MeromorphicAt (deriv f) x`
  (mathlib, `Analysis/Meromorphic/Basic.lean:372`) — **the `df` meromorphy input**, spike-verified.
- `AnalyticOnNhd.meromorphicOn`/`AnalyticAt.meromorphicAt` (mathlib, `Basic.lean:475/40`).

### 1.4 `Jacobian/ResidueCalculus/` (residue-calculus, BUILT, zero sorries — verified)

- `RS.resAt (f : ℂ → ℂ) (z₀ : ℂ) : ℂ := laurentCoeffAt f z₀ (-1)` (`Residue.lean:37`),
  `resAt_congr/fun_add/const_mul/fun_sum/neg/sub` (linearity, all built).
- `RS.resAt_comp_mul_deriv {φ} (hφ : AnalyticAt ℂ φ w₀) (hφ' : deriv φ w₀ ≠ 0) (hφ₀ : φ w₀ = z₀)
  (hf : MeromorphicAt f z₀) : resAt (fun w => f (φ w) * deriv φ w) w₀ = resAt f z₀`
  (`ChangeOfVariables.lean:37`) — **THE chart-invariance atom for `MForm.resAt`** (§5 P4).
- `RS.MeromorphicAt.resAt_deriv_div (hf : MeromorphicAt f z₀) : resAt (deriv f / f) z₀ =
  ((meromorphicOrderAt f z₀).untop₀ : ℂ)` (`Residue.lean:142`, junk-robust, no side condition) —
  **item 4's target fact**, the argument-principle atom feeding `MForm.resAt_dlog` (§4.3).
- `RS.MeromorphicAt.resAt_deriv (hf) : resAt (deriv f) z₀ = 0` (`Residue.lean:99`) — a
  by-product sanity check (`resAt (d f) x = 0` unless `f` itself has a pole contributing via the
  compound `dlog`, consistent with `resAt_deriv_div`'s `f := 1`-free reading).
- `RS.principalPartAt f z₀ : ℂ → ℂ`, `RS.MeromorphicAt.exists_principalPart_add_analyticAt`
  (`PrincipalPart.lean:31/100`) — the chart-local Laurent-tail vocabulary for §4.6's ML-form
  wrapper.
- `RS.PrincipalPartData U` (planar, `U : Set ℂ`), `Realizes`, `toFun`, `totalRes`,
  `ofMeromorphicOn`, `Realizes.add/smul/sub_orderAt_nonneg`, `realizes_zero_iff`
  (`MittagLeffler.lean`, **semi-frozen** per its own docstring: "laurent-tails' designer may
  extend, not change, this interface") — §4.6 wraps this at the `MForm`/`X` level per
  `residue-calculus.md`'s own scope note: "canonical-forms (§17.4) needs the *vocabulary* of
  principal parts on charts and `resAt` bookkeeping... `PrincipalPartData` for §17-flavored
  bookkeeping" (`residue-calculus.md:782`).

### 1.5 `Jacobian/Finiteness/` (finiteness-and-chi, AUTHORITATIVE, IN FLIGHT — per its own doc)

Exact exports we consume, `docs/design/finiteness-and-chi.md` §4.7/§12 (their own downstream note
names us directly: *"canonical-forms (direct dependent): `chi_zero_add_degree_le_l` +
`exists_ne_zero_mem_linSys`... Forster 16.11 pattern runs on divisors `n • single P 1` with
`degree` linear... They own nonconstant-function extraction."*):
```lean
noncomputable def h1 (D : Divisor X) : ℕ
noncomputable def chi [ConnectedSpace X] (D : Divisor X) : ℤ := (l D : ℤ) - (h1 D : ℤ)
theorem chi_zero_add_degree_le_l (D) : chi 0 + D.degree ≤ (l D : ℤ)        -- the Riemann seed
theorem exists_ne_zero_mem_linSys (h : 0 < chi 0 + D.degree) : ∃ f ∈ LinSys D, f ≠ 0
instance finiteDimensional_linSys [ConnectedSpace X] (D) : FiniteDimensional ℂ (LinSys D)
theorem l_mono (h : D ≤ D') : l D ≤ l D'
```
⚠ `Chi.lean`/`H1Finite.lean` are gated behind cech's Skyscraper fragment at *their* design time;
`chi_zero_add_degree_le_l` is listed as the frozen export we consume regardless of gate status
(their §12 downstream map commits to this shape). If it lands with a different name/shape, only
`Existence.lean` §5 P-exist needs a one-line adjustment — no other file is affected.

### 1.6 A genuine gap: no `Divisor.single` on disk yet

`docs/design/meromorphic-and-divisors.md` §4.6 planned `degree_single`/a point-divisor
constructor, but **grepping `Jacobian/Meromorphic/Divisor.lean` finds no `single` definition** —
only `degree`, `divisorOn`, `divisor`, and their algebra. mathlib's own
`Function.locallyFinsupp.single` (`Topology/LocallyFinsupp.lean:153`, unrestricted domain) is
*not* the restricted `locallyFinsuppWithin univ` we need, though `mk_of_mem_addSubgroup`
(`:322`, `(f) (hf : f ∈ locallyFinsuppWithin.addSubgroup U) : locallyFinsuppWithin U Y`) gives a
three-line Compat route: `Pi.single P n` has finite (singleton) support, hence trivially satisfies
both the membership and local-finiteness side conditions. **Action**: file
`docs/requests/meromorphic-and-divisors.md` (this fact is generically useful, not
canonical-forms-specific — laurent-tails/riemann-roch will want it too) AND provide the ~12-line
Compat definition locally in `Existence.lean` (§4.4), matching CONVENTIONS.md's "prove it locally
in a clearly marked `Compat` section" rule.

---

## 2. Core definitional decisions

### D1 — `MForm X`: point-indexed `chartAt` coefficient families, `MeromorphicOn`, no conjugate

```lean
namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- A meromorphic 1-form on `X`: the meromorphic analogue of `Form1`'s `coeffIn` API and
`Form01`'s chart-family structure, generalized to allow poles. -/
structure MForm (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] where
  coeffAt : X → ℂ → ℂ
  coeffAt_zero_off : ∀ x, ∀ z ∉ (chartAt ℂ x).target, coeffAt x z = 0
  meromorphicOn_coeffAt : ∀ x, MeromorphicOn (coeffAt x) (chartAt ℂ x).target
  compat : ∀ x y : X, ∀ z ∈ ⇑(chartAt ℂ y) '' ((chartAt ℂ x).source ∩ (chartAt ℂ y).source),
    coeffAt y z = deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) z *
      coeffAt x (chartAt ℂ x ((chartAt ℂ y).symm z))
```
Spike-verified (§8, item 1) — the bare shape elaborates. `MeromorphicOn f U := ∀ x ∈ U,
MeromorphicAt f x` (mathlib) is the *unconditional* generalization of Form01's `ContDiffOn ℝ ∞`:
no side condition, allows poles, matches the project's existing `MeromorphicOnX`/`MeromorphicOn`
vocabulary exactly (CC3, mathlib-inventory). The transition factor is `deriv τ` (not `conj (deriv
τ)`, as `Form01` needs for `(0,1)`-forms) — matching `Form1.coeffIn_trans`'s own orientation, since
a meromorphic 1-form is still type `(1,0)`.

### D2 — Algebra: `AddCommGroup`/`Module ℂ`, pointwise, no new instance-diamond risk

`Zero/Add/Neg/Sub/SMul ℂ` are pointwise on `coeffAt`; each structure field is closed under the
operations exactly as `Form01`'s own instances are (§1.1: "each structure field is closed under
the operations (compat is ℂ-linear in the coefficients, `zero_off` trivially preserved)") — the
ONLY difference is closure of `MeromorphicOn` under `+`/`neg`/`c•` (mathlib: `MeromorphicAt.add/
neg/smul`, all built, unconditional). `MForm.ext` compares `coeffAt` on targets only (mirrors
`Form1.ext_coeffAt`/`Form01.ext`).

### D3 — `MFormCoeffData`/`MForm.ofCoeffs`: the arbitrary-chart-family constructor

Mirrors `Form1CoeffData`/`Form1.ofCoeffs` (`OfCoeffs.lean`) verbatim, `AnalyticOnNhd ↦
MeromorphicOn`. Used by: `d` (§D6, trivial instantiation with holomorphic data), and available for
any future consumer that builds an `MForm` from covering Laurent/principal-part data (laurent-
tails' likely use). **Not** used by `MForm.d`/`dlog` themselves (§D6) — those are simplest as
direct `chartAt`-indexed structure literals, since `chartAt` already **is** the natural covering
family and going through `ofCoeffs`'s `idx : X → ι` choice machinery would be pure overhead.

### D4 — `ord`, `resAt`: primary definition via `chartAt`, invariance as a corollary

```lean
noncomputable def MForm.ord (ω : MForm X) (x : X) : WithTop ℤ :=
  meromorphicOrderAt (ω.coeffAt x) (chartAt ℂ x x)
noncomputable def MForm.resAt (ω : MForm X) (x : X) : ℂ :=
  RS.resAt (ω.coeffAt x) (chartAt ℂ x x)
```
Exactly CC3's own pattern for `ordAtX` (`ordAtX f x := meromorphicOrderAt (f ∘ chart.symm) (chart
x)`) — reading via the FIXED `chartAt` needs **no invariance proof to be well-defined** (there is
no ambiguity to resolve: `chartAt ℂ x` is a definite choice). The "read in any maximal-atlas
chart" **corollary** (`MForm.ord_eq_of_mem_source`/`MForm.resAt_eq_of_mem_source`, §4.2) is
supplied because downstream consumers (residue-theorem's PoU pieces, laurent-tails' truncations)
may want it, and it is exactly the fact the task brief names ("chart-invariant via the BUILT
`resAt_comp_mul_deriv`!") — but per `docs/design/dbar-solvability.md`'s own remark ("cech's
`IsChartDisk` charts ARE `chartAt`s"), **no currently-designed consumer is DAG-required to have
it**; it is offered as a documented, non-blocking convenience (§4.2, proof plan §5 P4).

### D5 — The global zero-dichotomy (connectedness-dependent, feeds D7's ratio construction)

```lean
theorem MForm.eq_zero_or_forall_ord_ne_top [T1Space X] [ConnectedSpace X] (ω : MForm X) :
    ω = 0 ∨ ∀ x, ω.ord x ≠ ⊤
```
Transcribes `MeromorphicOnX.eventuallyEq_zero_or_forall_ordAtX_ne_top`'s clopen/connectedness
proof (§1.3, `CodiscreteBridge.lean:110`) with `ordAtX f` replaced by `ω.ord` throughout (§5 P3).
**Not** needed for `divisor`'s local finiteness (D6 below — that is a purely *local* fact,
mirroring `divisorOn`'s own proof, connectedness-free); needed *only* for the one-dimensionality
ratio (D7): to know a fixed nonzero reference `ω₀` has `ord ≠ ⊤` **everywhere**, not just off its
own (a priori possibly infinite, without this) zero set.

### D6 — `divisor : MForm X → Divisor X`; local finiteness is connectedness-free

```lean
noncomputable def MForm.divisor [T2Space X] [CompactSpace X] (ω : MForm X) : Divisor X where
  toFun x := (ω.ord x).untop₀
  supportWithinDomain' := by trivial   -- support ⊆ univ
  supportLocallyFiniteWithinDomain' := ...   -- §5 P2
```
Local finiteness mirrors `MeroGermOn.divisorOn`'s proof (§1.3, `Divisor.lean:134`) **exactly**,
point for point: at `z`, either `ω.ord z = ⊤` (propagates to a whole neighborhood via an
`MForm`-level `eventually_ord_eq_top`, itself mirroring `eventually_ordAtX_eq_top`'s one-chart
argument, §5 P2) giving empty local support, or `ω.ord z ≠ ⊤` (propagates to `ord = 0` on a
*punctured* neighborhood via `eventually_ord_eq_zero`, mirroring `eventually_ordAtX_eq_zero`)
giving local support `⊆ {z}`. **No connectedness, no global dichotomy** — this is why `divisor`
only needs `[T2Space][CompactSpace]`, matching `divisorOn`'s own hypotheses. `MForm.degree`
(`:= ω.divisor.degree`) needs the same instances.

### D7 — `d`/`df`/`dlog`: the differentials, and the `deriv`-through-poles lemma

```lean
noncomputable def MForm.ofForm1 (η : Form1 X) : MForm X            -- d : Form1 X →ₗ[ℂ] MForm X
noncomputable def MForm.d (f : ℳ X) : MForm X                      -- df, meromorphic f allowed
noncomputable def MForm.smul (h : ℳ X) (ω : MForm X) : MForm X     -- the ℳ(X)-module action h • ω
noncomputable def MForm.dlog (f : ℳ X) : MForm X := MForm.smul f⁻¹ (MForm.d f)
```
`MForm.ofForm1 η` uses `η`'s own `coeffIn (chartAt ℂ x) η` (already `AnalyticOnNhd` by
`Form1.analyticOnNhd_coeffIn`, hence `MeromorphicOn` by `AnalyticOnNhd.meromorphicOn`, spike-
verified §8 item 2); its `compat` is *exactly* `coeffIn_trans` (no new work — Form1's own
transition rule literally **is** `MForm`'s `compat` equation, since holomorphic forms have no
poles to worry about). This is item 3(d)'s bridge object (used again in §4.5/§6 for the
`Form1 ≃ {ω | divisor ω ≥ 0}` theorem).

`MForm.smul h ω` (chart-locally `(h • ω).coeffAt x z := h.holoRepr ((chartAt ℂ x).symm z) *
ω.coeffAt x z`) needs **no new subtlety**: `h.holoRepr` is the ALREADY-CANONICAL, choice-free,
total representative (§1.3); its `compat`'s "own-chart" factor is literally the SAME base point
`p := (chartAt ℂ y).symm z` evaluated by `h.holoRepr` on both sides (trivial equality, no chain
rule involved for that factor), multiplied against `ω`'s own `compat` for the other factor.

`MForm.d f` is the genuinely new piece: `coeffAt x z := if z ∈ target then deriv (f.holoRepr ∘
(chartAt ℂ x).symm) z else 0`. `meromorphicOn_coeffAt` follows from `meromorphicOnX_holoRepr` +
`meromorphicAtX_iff_of_mem_source` + mathlib's `MeromorphicAt.deriv` (all built, spike-verified
items 2/3, §8) — **no case split needed here**, `MeromorphicAt.deriv` is unconditional. `compat`
DOES need a case split (§5 P1, the unit's central new lemma, spike-verified item 4, §8): at a
point where `f.holoRepr` is classically differentiable through both charts, the identity is the
*exact* chain-rule computation `coeffIn_trans` already performs (mirror it verbatim, `f.holoRepr`
in place of a `Form1`); at a pole (where `f.holoRepr` is *not* differentiable — it is literally
discontinuous there, artificially patched to `0` by `evalAt_of_not_nonneg`, while blowing up on
the punctured neighborhood, `tendsto_holoRepr_cobounded_iff`), BOTH sides of `compat` collapse to
`0` because differentiability-failure transports across a biholomorphic chart transition (proved,
not assumed — `differentiableAt_trans` composed both ways, spike-verified item 4).

### D8 — One-dimensionality: `MForm ≅ ℳ(X) · ω₀`

```lean
theorem MForm.exists_unique_smul_of_ne_zero [T1Space X] [T2Space X] [ConnectedSpace X]
    {ω₀ : MForm X} (h₀ : ω₀ ≠ 0) (ω : MForm X) :
    ∃! h : ℳ X, ω = MForm.smul h ω₀
```
Chart-local division (§5 P5): at each `x`, `ω₀.coeffAt x` is meromorphic and, by D5 (applied to
`ω₀`), `≠ ⊤`-order at every point of `X` — so `ω.coeffAt x / ω₀.coeffAt x` is `MeromorphicOn`
target (mathlib `MeromorphicAt.div`, unconditional on the denominator being merely `MeromorphicAt`,
not "nonzero everywhere" — division by a meromorphic function with isolated zeros is itself
meromorphic, poles exactly at those zeros). These LOCAL quotients satisfy `MForm`'s own `compat`
identity (the `deriv τ` factors cancel between numerator and denominator — direct algebra, no new
lemma), hence assemble (via `MeroGermOn.exists_glue`, §1.3-adjacent, `Gluing.lean` — reused
directly, since the local quotients ARE literally `MeromorphicOnX`-compatible data on the
`chartAt`-source cover) into a single class `h ∈ ℳ X` with `h.holoRepr` chart-locally equal to the
quotient off the (locally finite) zero set of `ω₀`. Uniqueness: `MForm.smul` is `ℳ(X)`-linear
(`smul_add`/`add_smul` style, cheap) and `ω₀ ≠ 0` means (D5) `ω₀` is *generically* nonzero, so
`MForm.smul h ω₀ = MForm.smul h' ω₀ ⟹ MForm.smul (h - h') ω₀ = 0 ⟹ h = h'` chart-locally off the
zero set, then everywhere by the identity theorem (`Mero.ord_eq_top_iff`-style). Full plan: §5 P5.

### D9 — Existence chain (the unit's raison d'être)

```lean
theorem exists_nonconstant_mero [T2Space X] [CompactSpace X] [ConnectedSpace X] :
    ∃ f : ℳ X, ∀ c : ℂ, f ≠ algebraMap ℂ (ℳ X) c
theorem exists_ne_zero_mform [T2Space X] [CompactSpace X] [ConnectedSpace X] :
    ∃ ω : MForm X, ω ≠ 0
```
`exists_nonconstant_mero` (§5 P-exist): pick any `P : X`; choose `n` with `chi (0:Divisor X) + n ≥
2` (arithmetic on `ℤ`, always possible since `n` is free); `chi_zero_add_degree_le_l` at `D_n :=
n • Divisor.single P 1` (Compat, §1.6) gives `l D_n ≥ 2`; `LinSys 0 ≤ LinSys D_n`
(`linSys_mono`, `0 ≤ D_n`) has `l 0 = 1` (`l_zero`, spanned by constants, `linSys_zero_eq_span_one`)
— so `l D_n ≥ 2 > 1 = l 0` forces some `f ∈ LinSys D_n` outside the span of `1`, i.e. not a
constant. This is *literally* Forster 16.11 / finiteness-and-chi's own §12 downstream note ("their
'χ(D) → ∞ forces L(D) ≠ 0'... runs on divisors `n • single P 1`"). `exists_ne_zero_mform` is then
`⟨MForm.d f, ...⟩` where nonzero-ness is: a nonconstant meromorphic function has nonzero
differential (if `d f = 0` then `f.holoRepr` has `deriv = 0` on every chart target, hence is
locally constant off the codiscrete pole set, hence — connectedness + `f.holoRepr`'s own
continuity/identity-theorem behavior — globally constant, contradicting nonconstancy). Full plan
folded into §5 P-exist (the two theorems share the same setup).

### D10 — The canonical divisor `K`, well-defined up to linear equivalence

```lean
/-- `K` seeded by an explicit nonzero reference (no silent `Classical.choice`-baked default —
"a" canonical divisor, matching the classical vocabulary; downstream fixes one via
`exists_ne_zero_mform.choose` when a definite `K` is needed for a numerical statement). -/
noncomputable abbrev canonicalDivisorOf (ω₀ : MForm X) : Divisor X := ω₀.divisor

theorem canonicalDivisorOf_linearEquiv [T1Space X] [T2Space X] [ConnectedSpace X]
    {ω₀ ω₀' : MForm X} (h₀ : ω₀ ≠ 0) (h₀' : ω₀' ≠ 0) :
    ∃ f : ℳ X, f ≠ 0 ∧ canonicalDivisorOf ω₀' = canonicalDivisorOf ω₀ + divisor f
```
Direct from D8: `ω₀' = h • ω₀` for a unique `h ≠ 0` (nonzero since `ω₀' ≠ 0`); `divisor` of a
`smul` decomposes as `divisor h + divisor ω₀` chart-locally (`ord_mul`-style additivity of
`meromorphicOrderAt`, transported through `MForm.smul`'s own definition) — cheap, ~15 lines. This
is exactly Forster 16.7-style "`K` is well defined up to linear equivalence."

### D11 — The `L(D)`/`Ω(D)` bridge (Miranda `L⁽¹⁾(D)`, Forster's `Ω_D`)

```lean
/-- Meromorphic 1-forms with divisor `≥ -D` (Miranda's `L⁽¹⁾(D)`/Forster's `Γ(X, Ω_D)`, D+K
convention fixed by `Ω_iso_linSys` below). -/
def MForm.OmegaSpace (D : Divisor X) : Submodule ℂ (MForm X) where
  carrier := {ω | ω = 0 ∨ ω.divisor ≥ -D}
  ...
noncomputable def i (D : Divisor X) : ℕ := Module.finrank ℂ (MForm.OmegaSpace D)   -- index of speciality

/-- The bridge (Forster 17.4/Miranda's `Ω_D ≅ O_{D+K}`): multiplication by a fixed nonzero
reference `ω₀` (with `K := canonicalDivisorOf ω₀`) is a linear equivalence `Ω(D) ≅ L(D+K)`. -/
theorem Ω_iso_linSys [T1Space X] [T2Space X] [ConnectedSpace X] {ω₀ : MForm X} (h₀ : ω₀ ≠ 0)
    (D : Divisor X) : MForm.OmegaSpace D ≃ₗ[ℂ] LinSys (D + canonicalDivisorOf ω₀)
theorem i_eq_l_add_canonicalDivisorOf [...] (h₀) (D) :
    i D = l (D + canonicalDivisorOf ω₀)
```
Via D8's `ω = h • ω₀` bijection: `ω.divisor = divisor h + K` (D10's additivity), so `ω.divisor ≥
-D ⟺ divisor h ≥ -D - K = -(D+K) ⟺ h ∈ LinSys (D+K)`. Mirrors `linSysMulEquiv`'s own construction
(`LinearEquiv.ofLinear` two mutually-inverse `smul` maps, §1.3) almost verbatim. Full plan: §5 P6.
**This is the statement bank laurent-tails/serre-duality-cech consume for their `Ω_D`/duality
bookkeeping** — the exact-signature deliverable the task brief's item 3(c) asks for.

### D12 — The `Form1 ↔ MForm` bridge (BUILT `Form1` ↔ chart-family `MForm`, item 3(d))

```lean
/-- Holomorphic MForm coefficients assemble into a genuine `Form1` (via `Form1.ofCoeffs`) and
back (via `MForm.ofForm1`, D7); the two maps are mutually inverse. -/
noncomputable def Form1.toMForm : Form1 X →ₗ[ℂ] MForm X := ⟨MForm.ofForm1, ...⟩   -- = D7's `ofForm1`
noncomputable def holomorphicMFormsEquiv [T2Space X] :
    Form1 X ≃ₗ[ℂ] ↥(MForm.OmegaSpace (0 : Divisor X))
```
The REAL proof obligation (task brief flags this correctly): forward direction is D7 (analytic
coefficients are meromorphic with `ord ≥ 0` everywhere, i.e. land in `OmegaSpace 0`); backward
needs `holomorphic MForm coefficients ⇒ analytic ⇒ a Form1 via ofCoeffs` — an `ω` with `ω.divisor
≥ 0` has `MeromorphicOn` coefficients with **nonnegative order everywhere**, hence (mathlib
`MeromorphicOn.analyticOnNhd_of_order_nonneg`-flavored bridge — check exact name at build time,
fallback: `holoRepr`'s own `holoRepr_contMDiffOn` proof technique, `evalAt`-rigidity, §1.3) is
literally `AnalyticOnNhd`, so `Form1.ofCoeffs` applies with `D.coeff x := ω.coeffAt x` directly (no
repair needed — `ω`'s coefficients are ALREADY honest analytic functions, not germ classes needing
`holoRepr`). Full plan: §5 P6 (folded with D11's proof, same machinery). Hence `genus X =
Module.finrank ℂ ↥(MForm.OmegaSpace 0)` — the export cech-h1-genus/riemann-roch use for `l(K) = g`
(NOT proved here — that needs Serre duality, owned downstream; we export only the bridge and the
`i D = l (D+K)` dictionary that makes `l(K) = g` a one-line corollary once `i 0 = h1 0` lands).

### D13 — Mittag-Leffler distributions of forms (task item 5, Forster §17.1–17.2)

```lean
/-- A form-level Mittag-Leffler datum: at finitely many points of `X`, a principal part read
in the preferred chart (the FORM-level wrapper `residue-calculus.md` flags as canonical-forms'
job: "the FORM-level wrapper here if serre-duality-cech's blueprint entry needs it"). -/
structure MLFormData (X) [...] where
  pts : Finset X
  data : ∀ x ∈ pts, PrincipalPartData ((chartAt ℂ x).target)     -- reuse residue-calculus's planar type

def MLFormData.Realizes (μ : MLFormData X) (ω : MForm X) : Prop :=
  ∀ x ∈ μ.pts, ∀ k < 0, laurentCoeffAt (ω.coeffAt x) (chartAt ℂ x x) k = (μ.data x ‹_›).coeff (chartAt ℂ x x) k
noncomputable def MLFormData.totalRes (μ : MLFormData X) : ℂ := ∑ x ∈ μ.pts, (μ.data x ‹_›).coeff (chartAt ℂ x x) (-1)
```
This is a **thin X-level wrapper** around residue-calculus's ALREADY-BUILT, semi-frozen
`PrincipalPartData` (§1.4) — one datum per point, read in that point's own preferred chart, no new
planar content. Serre-duality-cech's own design (not yet written) will state its residue-
functional obstruction against this shape; we do not anticipate the pairing statement itself
(out of DAG scope per the blueprint's `Builds on:` edges — no current unit is DAG-required to
consume `MLFormData`, flagged non-blocking exactly as form-trace-tower flags its own analogous
bonus content, `form-trace-tower.md` §0.3).

---

## 3. File plan

| # | File | Content | Est. | Imports beyond stdlib/mathlib |
|---|------|---------|------|-------------------------------|
| 1 | `CanonicalForms/MForm.lean` | `MForm` (D1), ext, `Zero/Add/Neg/Sub/SMul ℂ`/`AddCommGroup`/`Module ℂ` (D2), `MFormCoeffData`/`MForm.ofCoeffs` (D3) | ~260 | `Jacobian.Forms`, `Jacobian.Meromorphic` |
| 2 | `CanonicalForms/OrdRes.lean` | `MForm.ord`/`resAt` (D4), chart-invariance corollaries, `divisor`/`degree` + local finiteness (D6), the zero-dichotomy (D5) | ~320 | file 1, `Jacobian.ResidueCalculus.{ChangeOfVariables,Residue}` |
| 3 | `CanonicalForms/Differential.lean` | `MForm.ofForm1`, `MForm.smul` (ℳ-module), `MForm.d`, the `deriv`-through-poles lemma, `dlog`, `resAt_dlog` (D7) | ~340 | files 1–2 |
| 4 | `CanonicalForms/OneDimensional.lean` | `MForm.exists_unique_smul_of_ne_zero` (D8) | ~260 | files 1–3, `Jacobian.Meromorphic.Gluing` |
| 5 | `CanonicalForms/Existence.lean` | `Divisor.single` Compat (§1.6), `exists_nonconstant_mero`/`exists_ne_zero_mform` (D9), `canonicalDivisorOf`/linear-equivalence (D10) | ~220 | files 1–4, `Jacobian.Finiteness` |
| 6 | `CanonicalForms/LinearSystems.lean` | `OmegaSpace`/`i`/`Ω_iso_linSys` (D11), `holomorphicMFormsEquiv` (D12), `MLFormData` (D13) | ~300 | files 1–5 |
| 7 | `Jacobian/CanonicalForms.lean` | unit root, API docstring | ~30 | all |

Build waves: file 1 is fully independent of finiteness-and-chi's gate status (only needs BUILT
`Forms`/`Meromorphic`) — build it first. Files 2–4 need only file 1 plus already-BUILT
`ResidueCalculus`/`Meromorphic.Gluing`, also gate-independent. File 5 is the ONLY file gated on
finiteness-and-chi's `Chi.lean` landing (§1.5's ⚠) — everything else can and should be built and
checked (`scripts/check.sh`) before that gate clears. File 6 needs file 5's `canonicalDivisorOf`
only for its *statements*' `K`-dependent shape (D11/D12's `K` argument) — its `holomorphicMFormsEquiv`
half (D12) is gate-independent and can be built/proved first, with the `Ω_iso_linSys` half added
once file 5 lands.

---

## 4. Exports — exact signatures

Everything in `namespace RS` unless noted. Standing variables:
```lean
open scoped ContDiff Manifold
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
```
`[T1Space X]` enters wherever `holoRepr`/order-propagation lemmas are used (mirrors their own
hypotheses); `[T2Space X][CompactSpace X]` enters at `divisor`/`degree`/the existence chain;
`[ConnectedSpace X]` enters at the zero-dichotomy, one-dimensionality, and existence chain
(exactly where `ℳ X`'s own `Field`/dichotomy needs it, §1.3).

### 4.1 `MForm.lean`

```lean
structure MForm (X) [...] where                                                    -- D1
  coeffAt : X → ℂ → ℂ
  coeffAt_zero_off : ∀ x, ∀ z ∉ (chartAt ℂ x).target, coeffAt x z = 0
  meromorphicOn_coeffAt : ∀ x, MeromorphicOn (coeffAt x) (chartAt ℂ x).target
  compat : ∀ x y, ∀ z ∈ ⇑(chartAt ℂ y) '' ((chartAt ℂ x).source ∩ (chartAt ℂ y).source),
    coeffAt y z = deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) z *
      coeffAt x (chartAt ℂ x ((chartAt ℂ y).symm z))

@[ext] theorem MForm.ext {ω η : MForm X}
    (h : ∀ x, ∀ z ∈ (chartAt ℂ x).target, ω.coeffAt x z = η.coeffAt x z) : ω = η
instance : Zero (MForm X) ; instance : Add (MForm X) ; instance : Neg (MForm X)
instance : Sub (MForm X) ; instance : SMul ℂ (MForm X)
instance : AddCommGroup (MForm X) ; instance : Module ℂ (MForm X)
@[simp] theorem coeffAt_add/coeffAt_neg/coeffAt_sub (ω η : MForm X) (x z) : ...
@[simp] theorem coeffAt_smul (c : ℂ) (ω : MForm X) (x z) : (c • ω).coeffAt x z = c * ω.coeffAt x z
@[simp] theorem coeffAt_zero (x z) : (0 : MForm X).coeffAt x z = 0

structure MFormCoeffData (X) [...] (ι : Type*) where                               -- D3
  chart : ι → OpenPartialHomeomorph X ℂ
  mem_maximalAtlas : ∀ i, chart i ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X
  exists_mem : ∀ x : X, ∃ i, x ∈ (chart i).source
  coeff : ι → ℂ → ℂ
  meromorphicOn : ∀ i, MeromorphicOn (coeff i) (chart i).target
  compat : ∀ i j, ∀ x ∈ (chart i).source ∩ (chart j).source,
    coeff j (chart j x) = deriv (⇑(chart i) ∘ ⇑(chart j).symm) (chart j x) * coeff i (chart i x)

noncomputable def MForm.ofCoeffs {ι} (D : MFormCoeffData X ι) : MForm X
theorem MForm.coeffAt_ofCoeffs {ι} (D : MFormCoeffData X ι) {x i} (hx : x ∈ (D.chart i).source)
    {z : ℂ} (hz : z ∈ ⇑(chartAt ℂ x) '' ((D.chart i).source ∩ (chartAt ℂ x).source)) :
    (MForm.ofCoeffs D).coeffAt x z =
      deriv (⇑(D.chart i) ∘ ⇑(chartAt ℂ x).symm) z * D.coeff i (D.chart i ((chartAt ℂ x).symm z))
```

### 4.2 `OrdRes.lean`

```lean
noncomputable def MForm.ord (ω : MForm X) (x : X) : WithTop ℤ :=
  meromorphicOrderAt (ω.coeffAt x) (chartAt ℂ x x)
noncomputable def MForm.resAt (ω : MForm X) (x : X) : ℂ :=
  RS.resAt (ω.coeffAt x) (chartAt ℂ x x)

/-- Convenience (task item: "chart-invariant via the BUILT `resAt_comp_mul_deriv`"), NOT
DAG-required by any current unit — offered non-blocking. -/
theorem MForm.ord_eq_of_mem_source {ω : MForm X} {x : X} {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hx : x ∈ e.source) :
    ω.ord x = meromorphicOrderAt (fun z => deriv (⇑(chartAt ℂ x) ∘ ⇑e.symm) z *
      ω.coeffAt x (chartAt ℂ x (e.symm z))) (e x)                       -- §5 P4
theorem MForm.resAt_eq_of_mem_source {ω : MForm X} {x : X} {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hx : x ∈ e.source) :
    ω.resAt x = RS.resAt (fun z => deriv (⇑(chartAt ℂ x) ∘ ⇑e.symm) z *
      ω.coeffAt x (chartAt ℂ x (e.symm z))) (e x)                       -- §5 P4, uses resAt_comp_mul_deriv

theorem MForm.eventually_ord_eq_top {ω : MForm X} {x : X} (h : ω.ord x = ⊤) :
    ∀ᶠ y in nhds x, ω.ord y = ⊤
theorem MForm.eventually_ord_eq_zero {ω : MForm X} {x : X} (h : ω.ord x ≠ ⊤) :
    ∀ᶠ y in nhdsWithin x {x}ᶜ, ω.ord y = 0
theorem MForm.eq_zero_or_forall_ord_ne_top [T1Space X] [ConnectedSpace X] (ω : MForm X) :
    ω = 0 ∨ ∀ x, ω.ord x ≠ ⊤                                              -- D5, §5 P3

noncomputable def MForm.divisor [T2Space X] [CompactSpace X] (ω : MForm X) : Divisor X    -- D6
@[simp] theorem MForm.divisor_apply [T2Space X] [CompactSpace X] (ω : MForm X) (x : X) :
    ω.divisor x = (ω.ord x).untop₀
noncomputable def MForm.degree [T2Space X] [CompactSpace X] (ω : MForm X) : ℤ := ω.divisor.degree
@[simp] theorem MForm.divisor_zero [T2Space X] [CompactSpace X] : (0 : MForm X).divisor = 0
```

### 4.3 `Differential.lean`

```lean
noncomputable def MForm.ofForm1 (η : Form1 X) : MForm X                                  -- D7
theorem MForm.ofForm1_ord_nonneg (η : Form1 X) (x : X) : 0 ≤ (MForm.ofForm1 η).ord x
noncomputable def Form1.toMForm : Form1 X →ₗ[ℂ] MForm X := ⟨⟨MForm.ofForm1, ...⟩, ...⟩

noncomputable def MForm.smul (h : ℳ X) (ω : MForm X) : MForm X                            -- D7
scoped infixr:73 " • " => MForm.smul     -- (or a genuine `SMul (ℳ X) (MForm X)` instance)
instance : SMul (ℳ X) (MForm X) := ⟨MForm.smul⟩
@[simp] theorem coeffAt_smul_mero (h : ℳ X) (ω : MForm X) (x : X) {z}
    (hz : z ∈ (chartAt ℂ x).target) :
    (h • ω).coeffAt x z = h.holoRepr ((chartAt ℂ x).symm z) * ω.coeffAt x z
theorem smul_add/add_smul/smul_smul/one_smul (h h' : ℳ X) (ω ω' : MForm X) : ...          -- module laws

noncomputable def MForm.d (f : ℳ X) : MForm X                                             -- D7
theorem coeffAt_d (f : ℳ X) (x : X) {z} (hz : z ∈ (chartAt ℂ x).target) :
    (MForm.d f).coeffAt x z = deriv (f.holoRepr ∘ (chartAt ℂ x).symm) z
theorem MForm.d_add (f g : ℳ X) : MForm.d (f + g) = MForm.d f + MForm.d g                 -- [T1Space X]
theorem MForm.d_const (c : ℂ) : MForm.d (algebraMap ℂ (ℳ X) c) = 0
theorem MForm.d_eq_zero_iff [T2Space X] [ConnectedSpace X] {f : ℳ X} :
    MForm.d f = 0 ↔ ∃ c, f = algebraMap ℂ (ℳ X) c                                        -- §5 P-exist half

noncomputable def MForm.dlog (f : ℳ X) : MForm X := MForm.smul f⁻¹ (MForm.d f)
theorem MForm.resAt_dlog [T1Space X] (f : ℳ X) (hf : f ≠ 0) (x : X) :
    (MForm.dlog f).resAt x = ((f.ord x).untop₀ : ℂ)                       -- item 4, via resAt_deriv_div
```

### 4.4 `Existence.lean`

```lean
/-- Compat (§1.6; file `docs/requests/meromorphic-and-divisors.md`). -/
noncomputable def Divisor.single [DecidableEq X] (P : X) (n : ℤ) : Divisor X :=
  Function.locallyFinsuppWithin.mk_of_mem_addSubgroup (Pi.single P n)
    ⟨(Set.finite_singleton P).subset Pi.support_single_subset |>.subset (Set.subset_univ _)
       |>.elim (fun _ => Set.subset_univ _),                              -- support ⊆ univ, trivial
     fun z _ => ⟨Set.univ, Filter.univ_mem,
       (Set.finite_singleton P).subset (fun w hw => by simp_all [Pi.single_apply])⟩⟩
theorem Divisor.degree_single [T2Space X] [CompactSpace X] [DecidableEq X] (P : X) (n : ℤ) :
    (Divisor.single P n).degree = n

theorem exists_nonconstant_mero [T2Space X] [CompactSpace X] [ConnectedSpace X] :
    ∃ f : ℳ X, ∀ c : ℂ, f ≠ algebraMap ℂ (ℳ X) c                                     -- D9, §5 P-exist
theorem exists_ne_zero_mform [T2Space X] [CompactSpace X] [ConnectedSpace X] :
    ∃ ω : MForm X, ω ≠ 0                                                             -- D9

noncomputable abbrev canonicalDivisorOf [T2Space X] [CompactSpace X] (ω₀ : MForm X) :
    Divisor X := ω₀.divisor                                                          -- D10
theorem canonicalDivisorOf_linearEquiv [T1Space X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] {ω₀ ω₀' : MForm X} (h₀ : ω₀ ≠ 0) (h₀' : ω₀' ≠ 0) :
    ∃ f : ℳ X, f ≠ 0 ∧ canonicalDivisorOf ω₀' = canonicalDivisorOf ω₀ + divisor f     -- D10
```

### 4.5 `LinearSystems.lean`

```lean
def MForm.OmegaSpace [T2Space X] [CompactSpace X] (D : Divisor X) : Submodule ℂ (MForm X)   -- D11
theorem mem_omegaSpace_iff [T2Space X] [CompactSpace X] {ω : MForm X} {D : Divisor X} :
    ω ∈ MForm.OmegaSpace D ↔ ω = 0 ∨ -D ≤ ω.divisor
noncomputable def i [T2Space X] [CompactSpace X] (D : Divisor X) : ℕ :=
  Module.finrank ℂ (MForm.OmegaSpace D)                                                   -- index of speciality

theorem Ω_iso_linSys [T1Space X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    {ω₀ : MForm X} (h₀ : ω₀ ≠ 0) (D : Divisor X) :
    MForm.OmegaSpace D ≃ₗ[ℂ] LinSys (D + canonicalDivisorOf ω₀)                            -- D11
theorem i_eq_l_add_canonicalDivisorOf [...] {ω₀} (h₀) (D) :
    i D = l (D + canonicalDivisorOf ω₀)

noncomputable def holomorphicMFormsEquiv [T1Space X] [T2Space X] [CompactSpace X] :
    Form1 X ≃ₗ[ℂ] ↥(MForm.OmegaSpace (0 : Divisor X))                                     -- D12
theorem genus_eq_finrank_omegaSpace_zero [T1Space X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] : genus X = Module.finrank ℂ ↥(MForm.OmegaSpace (0 : Divisor X))

structure MLFormData (X) [...] where                                                      -- D13
  pts : Finset X
  data : ∀ x ∈ pts, PrincipalPartData (chartAt ℂ x).target
def MLFormData.Realizes (μ : MLFormData X) (ω : MForm X) : Prop
noncomputable def MLFormData.totalRes (μ : MLFormData X) : ℂ
theorem MLFormData.Realizes.resAt_eq (h : μ.Realizes ω) (x) (hx : x ∈ μ.pts) :
    ω.resAt x = (μ.data x hx).coeff (chartAt ℂ x x) (-1)
```

---

## 5. Proof plans for the hardest theorems

### P1. `MForm.d`'s `compat` (`Differential.lean`, the unit's riskiest lemma, spike-verified §8)

Goal: for `x y : X`, `z ∈ chartAt ℂ y '' ((chartAt ℂ x).source ∩ (chartAt ℂ y).source)`,
`deriv (f.holoRepr ∘ (chartAt ℂ y).symm) z = deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) z *
deriv (f.holoRepr ∘ (chartAt ℂ x).symm) (chartAt ℂ x ((chartAt ℂ y).symm z))` — write `c := chartAt
ℂ x`, `c' := chartAt ℂ y`, `p := c'.symm z`, `g := f.holoRepr` (fixed total function, §1.3).

1. **The general unconditional chain-rule-through-charts lemma** (extracted as its own reusable
   statement, since `MForm.ofCoeffs`/any future `deriv`-based `MForm` construction needs it too):
   ```lean
   theorem deriv_comp_chart_congr {g : X → ℂ} {e e' : OpenPartialHomeomorph X ℂ}
       (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω X) {z : ℂ}
       (hz : z ∈ e' '' (e.source ∩ e'.source)) :
       deriv (g ∘ ⇑e'.symm) z = deriv (⇑e ∘ ⇑e'.symm) z * deriv (g ∘ ⇑e.symm) (e (e'.symm z))
   ```
   (no hypothesis on `g` at all — this is the point.)
2. **Case split** on `DifferentiableAt ℂ (g ∘ e.symm) (e (e'.symm z))`.
3. **Regular case.** This is `coeffIn_trans`'s own computation (`Coeffs.lean:234`) with `η`'s
   bundle-level `coeffIn`/`mfderiv` replaced by the bare classical `deriv`: `differentiableAt_trans
   he he' hzt hps.1` gives `τ := e ∘ e'.symm` differentiable at `z` (`hzt`/`hps` exactly as in
   `coeffIn_trans`'s own setup, spike-verified §8 item 4's `hτ`); `g ∘ e'.symm =ᶠ[𝓝 z] (g ∘ e.symm)
   ∘ τ` on the open overlap image (spike-verified §8 item 4's `heq`, via `e'.symm =ᶠ e.symm ∘ τ`
   near `z`, the identical eventual-equality `coeffIn_trans` itself establishes at line ~249);
   `deriv_comp'`/`HasDerivAt.comp` (mathlib chain rule, needs `DifferentiableAt ℂ (g∘e.symm) (τ z)`
   — the case hypothesis — and `hτ`) plus `Filter.EventuallyEq.deriv_eq` on the congruence gives
   the claimed identity. Exactly the `hcongr`/chain-rule steps of `resAt_comp_mul_deriv`'s own
   proof shape (`ChangeOfVariables.lean`), specialized to `deriv` instead of `resAt`.
4. **Pole/non-differentiable case.** `¬ DifferentiableAt ℂ (g∘e.symm) (τ z)` — by mathlib's
   convention `deriv (g∘e.symm) (τ z) = 0`, so the RHS is `deriv τ z * 0 = 0`. For the LHS: need
   `¬ DifferentiableAt ℂ (g∘e'.symm) z`. This is the SPIKE-VERIFIED lemma (§8 item 4, stated there
   in the DifferentiableAt-transports-forward direction; the contrapositive — non-differentiability
   transports too — is the SAME lemma read backwards: if `g∘e'.symm` WERE differentiable at `z`,
   composing with `e'.symm`'s own inverse-direction transition (`differentiableAt_trans he' he ...`)
   would give `g∘e.symm` differentiable at `τ z`, contradiction). So `deriv (g∘e'.symm) z = 0` too
   (junk, non-differentiable), matching RHS `= 0`. ∎
5. **Instantiate** at `g := f.holoRepr`, `e := chartAt ℂ x`, `e' := chartAt ℂ y` to get `MForm.d
   f`'s `compat` directly — no further meromorphy-specific reasoning needed (the lemma above is
   about ANY function `g`, meromorphic or not; meromorphy of `f.holoRepr` is used only for
   `meromorphicOn_coeffAt`, a separate, easy field via `MeromorphicAt.deriv`, §2 D7).

Risk note: step 4's "backward" direction needs the SAME spike-verified argument run with `e`/`e'`
swapped — a direct symmetric application, not new content. The spike (§8 item 4) compiled the
FORWARD direction cleanly in ~15 lines; the full lemma (both directions via `by_cases` +
symmetric argument) is estimated ~45–55 lines, matching the task's "40+ lines" bar.

### P2. `MForm.divisor`'s local finiteness (`OrdRes.lean`)

Mirrors `MeroGermOn.divisorOn`'s proof (`Divisor.lean:134`) with `ordAtX f` replaced by `MForm.ord`
throughout. First the two propagation lemmas (mirroring `eventually_ordAtX_eq_top`/
`eventually_ordAtX_eq_zero`, `Predicates.lean:231/314`, whose own proofs are the template):

1. **`MForm.eventually_ord_eq_top`**: given `ω.ord x = ⊤`, i.e. `meromorphicOrderAt (ω.coeffAt x)
   (chartAt ℂ x x) = ⊤`, i.e. (mathlib `meromorphicOrderAt_eq_top_iff`) `ω.coeffAt x` is
   eventually `0` on `𝓝[≠] (chartAt ℂ x x)`. Transport through the chart
   (`eventually_nhdsNE_comp_chart_apply_iff`, built) to get `ω.coeffAt x` eventually `0` on
   `chartAt ℂ x '' (𝓝[≠] y-punctured-nbhd)` for `y` near `x`; combine with `y ∈ (chartAt ℂ
   x).source` eventually (open source) to conclude, FOR EACH SUCH `y`, `ω.ord y = ⊤` — but this
   step needs `ω.ord y` (defined via `chartAt ℂ y`, not `chartAt ℂ x`!) to be READABLE in the
   `chartAt ℂ x` chart instead — i.e. it needs `MForm.ord_eq_of_mem_source` (§4.2, P4) applied at
   `e := chartAt ℂ x`. This is exactly the extra step `eventually_ordAtX_eq_top` did NOT need
   (its `f` is one bare GLOBAL function readable in ANY chart directly by definition — `ordAtX f y
   := meromorphicOrderAt (f ∘ chartAt y) (chartAt y y)`, and `ordAtX_eq_of_mem_source` bridges to
   `chartAt x` — the SAME bridging step, just for `ω.ord` instead of `ordAtX f`). So: identical
   proof shape, with `ordAtX_eq_of_mem_source` replaced by `MForm.ord_eq_of_mem_source` (P4) at the
   one point of use.
2. **`MForm.eventually_ord_eq_zero`**: symmetric, mirroring `eventually_ordAtX_eq_zero`'s use of
   `MeromorphicAt.eventually_analyticAt` (isolated-zeros consequence) + the same chart-transport +
   `ord_eq_of_mem_source` bridge.
3. **Local finiteness**, exactly `divisorOn`'s own case split at each `z`: if `ω.ord z = ⊤`, item 1
   gives a whole neighborhood of `z` with `ord = ⊤` there too, hence support (the set `{y | ω.ord y
   ≠ ⊤ ∧ ω.ord y ≠ 0}`, i.e. `Function.support (fun y => (ω.ord y).untop₀)`) is EMPTY on that
   neighborhood; if `ω.ord z ≠ ⊤`, item 2 gives a punctured neighborhood with `ord = 0`, so support
   restricted to a (possibly smaller, intersected) neighborhood is `⊆ {z}`. Both branches close
   exactly as `divisorOn`'s own proof does (`Divisor.lean:134`, lines ~148–177), same `Set.Finite`
   API (`Set.finite_empty`/`Set.Finite.subset (Set.finite_singleton z)`).

Estimated 50–70 lines (two propagation lemmas ~20 lines each + the assembly ~20–30, matching
`divisorOn`'s own ~70-line proof body).

### P3. `MForm.eq_zero_or_forall_ord_ne_top` (`OrdRes.lean`)

Direct transcription of `MeromorphicOnX.eventuallyEq_zero_or_forall_ordAtX_ne_top`
(`CodiscreteBridge.lean:110`, read in full §1.3) with `ordAtX f`/`f` replaced by `ω.ord`/`ω`
throughout:

1. `S := {x | ω.ord x = ⊤}`. `IsOpen S` via `isOpen_iff_mem_nhds` + P2's item 1
   (`MForm.eventually_ord_eq_top`, the DIRECT analogue of `eventually_ordAtX_eq_top` this proof
   consumes).
2. `IsClosed S`: exactly the original's `mem_closure_iff_frequently` + case-split argument
   (lines ~119–150 of `CodiscreteBridge.lean`), with **one substitution**: the original's
   `MeromorphicAtX.frequently_zero_iff (hf x (mem_univ x))` (a fact about the GLOBAL function `f`
   read through `ordAtX`'s own chart) becomes, for `MForm`, a fact about `ω.coeffAt x` DIRECTLY —
   since `MForm.ord x` is BY DEFINITION `meromorphicOrderAt (ω.coeffAt x) (chartAt ℂ x x)`, the
   planar mathlib fact `MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero`/
   `meromorphicOrderAt_eq_top_iff` applies to `ω.coeffAt x` with NO chart-crossing detour needed at
   all at this step (a genuine simplification vs. the original, which had to detour through
   `ordAtX`'s own composite definition). The rest of the closedness argument (comparing `y = x` vs
   `y ≠ x` cases, combining eventualities) transcribes verbatim with `ordAtX_eq_top_iff` ↦ an
   `MForm`-level analogue `MForm.ord_eq_top_iff` (a one-line corollary of
   `meromorphicOrderAt_eq_top_iff`, no new proof).
3. `isClopen_iff` + `[ConnectedSpace X]` gives `S = ∅` or `S = univ`.
4. `S = ∅` branch: `∀ x, ω.ord x ≠ ⊤`, done (`Or.inr`).
5. `S = univ` branch: `∀ x, ω.ord x = ⊤`, i.e. `∀ x, ω.coeffAt x` is eventually `0` near `chartAt ℂ
   x x` — need to upgrade "eventually zero NEAR the center" to "IDENTICALLY zero ON ALL of
   target" (the original didn't need this step since its `f` is already one global function whose
   class-membership `f =ᶠ[codiscrete X] 0` is exactly the pointwise near-every-point statement; for
   `MForm`, `ω = 0` means `ω.coeffAt x ≡ 0` on the WHOLE target, not just near the center). This
   needs one more ingredient: `ω.coeffAt x` is `MeromorphicOn` (hence `AnalyticOnNhd` off its own
   isolated pole set, which is empty here since `ord = ⊤` means NO poles at all near the center —
   propagate via P2's `eventually_ord_eq_top`-style argument to the WHOLE connected target, using
   that meromorphic-and-locally-zero propagates by the identity theorem exactly as
   `MeromorphicOnX.eventuallyEq_zero_or_forall_ordAtX_ne_top`'s own closedness half already does,
   restricted to the single connected chart target). `MForm.ext` closes.

Estimated 60–80 lines (steps 1–4 are a close transcription, ~40 lines; step 5's extra
"near-center ⇒ whole-target" upgrade is the one genuinely new piece, ~20–30 lines, itself a
smaller copy of the SAME clopen-on-target argument).

### P4. `MForm.resAt_eq_of_mem_source` (`OrdRes.lean`)

Directly generalizes `RS.ordAtX_eq_of_mem_source` (`Predicates.lean:272`, read in full §1.3) with
the `resAt_comp_mul_deriv` chart-invariance atom (§1.4) inserted at the one place the residue
picks up a Jacobian factor that the bare order does not:

1. Fix `ω`, `x`, `e` (`he : e ∈ maximalAtlas`, `hx : x ∈ e.source`); `c := chartAt ℂ x`.
2. `analyticAt_transition he (chart_mem_maximalAtlas x) hx (mem_chart_source ℂ x) : AnalyticAt ℂ
   (c ∘ e.symm) (e x) ∧ deriv (c ∘ e.symm) (e x) ≠ 0` — call `τ := c ∘ e.symm`, `(hτ, hτ')`.
3. Set `g z := deriv (⇑c ∘ ⇑e.symm) z * ω.coeffAt x (c (e.symm z))` (the claimed RHS integrand).
   `g = fun w => (ω.coeffAt x) (τ w) * deriv τ w` up to the pointwise identity `c (e.symm z) = τ
   z` (definitional). So `RS.resAt g (e x) = RS.resAt (ω.coeffAt x) (τ (e x))` by
   **`resAt_comp_mul_deriv hτ hτ' (τ (e x) = c x, since e.symm (e x) = x by e.left_inv hx) (hf :=
   ω.meromorphicOn_coeffAt x applied at c x)`** — this IS `MForm.resAt x` by definition (`c x =
   chartAt ℂ x x`). ∎ (the order version, `ord_eq_of_mem_source`, is the SAME computation with
   `resAt` replaced by `meromorphicOrderAt`, using `meromorphicOrderAt_comp_of_deriv_ne_zero`
   (mathlib, `Order.lean:838`, already the exact atom `ordAtX_eq_of_mem_source` itself consumes) in
   place of `resAt_comp_mul_deriv`).

Estimated 25–35 lines (shorter than `resAtX_eq_of_mem_source` in form-trace-tower, since there is
only ONE chart crossing here, not two — `MForm`'s residue lives entirely on `X`, no target
manifold `Y` to cross a second time).

### P5. `MForm.exists_unique_smul_of_ne_zero` (`OneDimensional.lean`, the gluing proof)

1. **Setup.** `ω₀ ≠ 0`; by D5 (`MForm.eq_zero_or_forall_ord_ne_top`), `∀ x, ω₀.ord x ≠ ⊤`, i.e.
   `ω₀.coeffAt x` is `MeromorphicAt`-nonzero-generically at every chart center, hence (mathlib
   `MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero` at the ISOLATED-ZEROS level, applied on
   the whole target via the standard "meromorphic + not locally zero at the center ⇒ zero set is
   discrete in the target" fact) `ω₀.coeffAt x` has **isolated zeros** on `(chartAt ℂ x).target`
   (it is not identically `0` on any open subset — this is exactly what `ord x ≠ ⊤` gives at the
   center, propagated to the whole target by the SAME argument P3 uses).
2. **Local quotient.** `qFun x : ℂ → ℂ := fun z => ω.coeffAt x z / ω₀.coeffAt x z`. Meromorphic on
   target: mathlib `MeromorphicOn.div` (unconditional — a ratio of `MeromorphicOn` functions is
   `MeromorphicOn`, poles exactly where the denominator vanishes, PRECISELY the situation `L(D)`
   and `MeroGermOn` already handle routinely, e.g. `MeroGermOn.instFieldMero`'s own `Inv` instance,
   §1.3).
3. **Local compat.** For `x, y` overlapping: `ω.coeffAt`'s `compat` and `ω₀.coeffAt`'s `compat`
   both carry the SAME `deriv (c_x ∘ c_y.symm) z` factor; dividing the two equations cancels it
   (the factor is nonzero — `analyticAt_transition`'s second component, `deriv (c_x∘c_y.symm) (c_y
   y) ≠ 0` — so cross-multiplication/division is licit), giving `qFun y z = qFun x (c_x (c_y.symm
   z))` DIRECTLY (no `deriv` factor survives — this is the classical "ratio of two 1-forms is a
   function", the entire point of the construction). So the family `(qFun x)_x` is
   `MeromorphicOnX`-compatible data on the `(chartAt ℂ x).source`-cover of `X`.
4. **Glue.** `MeroGermOn.exists_glue` (`Gluing.lean:23`, built) applied to the family `φ x :=
   MeroGermOn.mk (qFun x) (...) : MeroGermOn X (chartAt ℂ x).source`, with the compat hypothesis
   from step 3 (restricted to overlaps, matching `exists_glue`'s exact hypothesis shape via
   `restrict`/`evalAt`-rigidity, mirroring `Gluing.lean`'s own internal `hagree`/`hFeq` pattern) —
   gives `h : MeroGermOn X (⋃ x, (chartAt ℂ x).source) = MeroGermOn X univ = ℳ X` (cover is `univ`
   since `chartAt` sources cover `X`) with `restrict (h at each x) = φ x`.
5. **`ω = h • ω₀`.** By `MForm.ext`: for each `x, z ∈ target`, `(h • ω₀).coeffAt x z = h.holoRepr
   (c_x.symm z) * ω₀.coeffAt x z`; since `h`'s restriction to `(chartAt ℂ x).source` agrees with
   `φ x = mk (qFun x)` (step 4), `h.holoRepr` agrees with `qFun x` off the (locally finite) zero
   set of `ω₀.coeffAt x` there (`holoRepr_eventuallyEq_nhdsNE`-style rigidity, §1.3) — giving
   `h.holoRepr (c_x.symm z) * ω₀.coeffAt x z = qFun x (c_x.symm z)⁻¹⁻¹ ...` — cleanly, since `qFun x
   := ω.coeffAt x / ω₀.coeffAt x` by construction, `h.holoRepr (c_x.symm z) * ω₀.coeffAt x z =
   ω.coeffAt x z` wherever `ω₀.coeffAt x z ≠ 0` (algebra), and at the (isolated) zeros of `ω₀.coeffAt
   x`, BOTH sides are forced equal by continuity/the identity theorem (a removable-singularity
   argument, since both `ω` and `h•ω₀`'s coefficients are meromorphic and agree off a discrete
   set — `MeromorphicAt.congr`-style). Concludes `ω = MForm.smul h ω₀`.
6. **Uniqueness.** If `MForm.smul h ω₀ = MForm.smul h' ω₀`, then chart-locally (`coeffAt_smul_mero`,
   §4.3) `(h.holoRepr - h'.holoRepr) (c_x.symm z) * ω₀.coeffAt x z = 0` for `z` in each target; off
   the (locally finite) zero set of `ω₀.coeffAt x`, `h.holoRepr = h'.holoRepr` there, hence (density
   + continuity, or directly via the meromorphic identity theorem on the connected `X`) `h = h'` as
   classes in `ℳ X` — mirrors `Mero.mul_inv_cancel`'s own zero-set bookkeeping (§1.3).

Estimated 70–90 lines total across steps 1–6 (the gluing step 4 is the bulk, reusing
`Gluing.lean`'s established `evalAt`-rigidity idiom almost verbatim), comfortably clearing the
task's "40+ lines" bar.

### P6. `Ω_iso_linSys` / `holomorphicMFormsEquiv` (`LinearSystems.lean`)

1. **`Ω_iso_linSys`.** Direct application of D8 (`exists_unique_smul_of_ne_zero`) to build the
   forward map `ω ↦ h` (`ω = h • ω₀`, `h` from D8) and backward map `h ↦ h • ω₀`
   (`LinearEquiv.ofLinear`, mirroring `linSysMulEquiv`'s own construction, `LinSysMulEquiv.lean:34`,
   almost verbatim — swap `L(D) ≃ L(D − divisor φ)` for `Ω(D) ≃ L(D + K)`, sign flipped since
   `Ω(D)`'s defining inequality is `-D ≤ ω.divisor` vs. `L(D)`'s `-D ≤ divisor f`, and `ω.divisor =
   divisor h + K` (D10) turns `-D ≤ divisor h + K` into `-(D+K) ≤ divisor h`, i.e. `h ∈ L(D+K)`).
   Both directions' well-definedness (landing in the claimed submodule) and mutual inverse-ness
   are the SAME two `Subtype.ext`+`ring`-level computations `linSysMulEquiv` already carries out —
   this file's version is that proof with `φ` renamed `ω₀`, `mul` renamed `smul`, and the extra
   additive `+ K` bookkeeping from D10 threaded through.
2. **`holomorphicMFormsEquiv` forward (`Form1 → OmegaSpace 0`).** `η ↦ MForm.ofForm1 η`; lands in
   `OmegaSpace 0` since `(MForm.ofForm1 η).ord x = meromorphicOrderAt (coeffIn (chartAt ℂ x) η)
   (chartAt ℂ x x) ≥ 0` always (analytic ⇒ nonneg order, `AnalyticAt.meromorphicOrderAt_nonneg` or
   equivalent, mathlib). Injective: `MForm.ofForm1 η = 0 ⟹ coeffIn (chartAt ℂ x) η ≡ 0 ⟹ η = 0` by
   `Form1.ext_coeffAt` (spike-verified item 2's bridge composed with `Form1.ext_coeffAt`).
3. **Backward (`OmegaSpace 0 → Form1`, the REAL proof obligation the task brief flags).** Given
   `ω` with `∀ x, 0 ≤ ω.ord x`: build `D : Form1CoeffData X X` (`ι := X`, `chart := chartAt ℂ`,
   `coeff := ω.coeffAt`) — `analyticOnNhd` field: need `ω.coeffAt x` `AnalyticOnNhd` on the WHOLE
   target, not just `MeromorphicOn` with nonneg order AT THE CENTER; upgrade via the SAME
   "nonneg-order-at-center propagates to nonneg-order-on-the-whole-connected-target" argument as
   P3/P5 (meromorphic + not-a-pole-anywhere-nearby ⇒ analytic everywhere nearby, propagated through
   the target by connectedness/openness of "the pole set is empty" — if the chart target is not
   itself connected, run the argument on each connected component separately, or note standard
   chart targets ARE balls/connected by convention, flagged as a risk in §6); `Form1CoeffData`'s
   OWN `compat` field is EXACTLY `MForm`'s `compat` (identical shape, `deriv τ` factor, no
   difference at all once coefficients are honestly analytic — literally the same equation).
   `Form1.ofCoeffs D : Form1 X`; `Form1.coeffIn_ofCoeffs` (built) gives `coeffIn (chartAt ℂ x)
   (Form1.ofCoeffs D) = ω.coeffAt x` on target, hence `MForm.ofForm1 (Form1.ofCoeffs D) = ω` by
   `MForm.ext`. Mutual inverse with step 2's map: both roundtrips are `Form1.ext_coeffAt`/`MForm.ext`
   applications on the SAME `coeffAt`/`coeffIn` data, no new computation.

Estimated 90–110 lines total (step 1 ~40, steps 2–3 ~50–70 — the "propagate nonneg order to the
whole target" lemma is shared between P3, P5, and here, so it is worth extracting as one named
lemma, `MForm.analyticOnNhd_coeffAt_of_ord_nonneg`, used three times — reducing the marginal cost
of each site to a citation).

---

## 6. Junk-value and compatibility ledger

- `MForm.coeffAt x z` off `(chartAt ℂ x).target`: literal `0` (`coeffAt_zero_off`), matching
  `Form01`'s own convention — no statement becomes vacuously true through this junk (every export
  is stated `∀ z ∈ target` or reads `ord`/`resAt` at the chart CENTER, always in-target).
  `MeromorphicOn`/`compat` are conditions ON target only, never referencing off-target values.
- `MForm.ord`/`resAt` at a point are `meromorphicOrderAt`/`resAt` of the coefficient, both already
  junk-honest per residue-calculus's own ledger (§4.3 hierarchy): `⊤`/`0` respectively for a
  locally-zero coefficient, no extra convention introduced here.
- `MForm.divisor`'s value `(ω.ord x).untop₀` reuses `WithTop.untop₀`'s existing `⊤ ↦ 0` convention,
  identical to `MeroGermOn.divisorOn`'s own (§1.3) — deliberately: a "divisor" has no way to record
  "identically zero here", and `0` is the only sane value (an honest divisor value, not junk, once
  `ω ≠ 0` is known via D5).
- `MForm.d f`'s dependence on `f.holoRepr` rather than an arbitrary representative is a DELIBERATE
  choice (§0), not junk-avoidance cosmetics: it makes `MForm.d` a genuine, `Classical.choice`-free
  function `ℳ X → MForm X` (no representative-selection ambiguity to discharge downstream).

---

## 7. Risks & fallbacks

1. **P1's chain-rule-through-poles lemma** (MEDIUM, the unit's central risk). Spike-verified in
   the FORWARD direction (§8 item 4, DifferentiableAt transports one way); the case-split's other
   half (non-differentiability transports too) is the SAME lemma applied with `e`/`e'` swapped —
   low incremental risk, but the two-sided assembly (`by_cases` + both directions +
   `Filter.EventuallyEq.deriv_eq` bookkeeping) is exactly the kind of "grind" other design docs
   (residue-calculus §7, form-trace-tower §7) flag as their own top risk, so budget accordingly.
   **Fallback**: if the junk-collapse argument resists (e.g. `deriv`'s `0`-junk convention proves
   awkward to rewrite through cleanly), restate `compat` as an `=ᶠ[𝓝[≠] point]`-level identity
   instead of a literal pointwise one (a genuine, well-motivated deviation, matching how `ℳ X`
   itself relaxes to `codiscreteWithin`-level equality) — `ord`/`resAt`/`divisor` (D4/D6, the only
   consumers) only ever need punctured-neighborhood-level information anyway, so this fallback
   costs nothing downstream, only changes `MForm`'s own internal bookkeeping shape. Flag to
   orchestrator if taken (changes `MFormCoeffData.compat`'s frozen shape too).
2. **P3/P5/P6's "nonneg/∞ order at a center propagates to the whole (possibly disconnected) chart
   target"** (LOW-MEDIUM). Standard charts in this project are typically ball-shaped (connected)
   by construction (`IsChartDisk` in cech, `Ustar`/chart-disk conventions in finiteness-and-chi),
   but `MForm`'s OWN definition does not itself require `(chartAt ℂ x).target` to be connected.
   **Fallback**: state the three affected lemmas (P3 step 5, P5 step 1, P6 step 3) with an
   explicit `IsPreconnected (chartAt ℂ x).target` hypothesis if the general case resists, and
   discharge it project-wide via a small `Compat` lemma (chart targets ARE metric balls in the
   standard atlas — check `IsManifold`'s own chart construction, likely trivial) rather than
   re-deriving per-callsite.
3. **`Divisor.single`'s Compat construction** (LOW). Verified directly against
   `Function.locallyFinsuppWithin.mk_of_mem_addSubgroup`'s exact signature (§1.6, mathlib source
   read in full) — the two membership obligations are both one-line `Set.Finite.subset` calls on
   the singleton support of `Pi.single`. If `addSubgroup`'s field names drift at the pin, the
   fallback is `Function.locallyFinsuppWithin.mk_of_mem_addSubmonoid` + a separate `Neg`
   compatibility (unlikely to be needed — `AddSubgroup` should be stable).
4. **`MeroGermOn.exists_glue`'s hypothesis shape** (P5 step 4, LOW). The compat hypothesis
   `exists_glue` demands is stated via `restrict`, not raw function agreement — §5 P5 flags this
   as "mirroring `Gluing.lean`'s own internal `hagree`/`hFeq` pattern," i.e. the SAME
   `evalAt`-rigidity idiom `Gluing.lean` already executes successfully; low risk since it is a
   direct instantiation of already-proven machinery, not new proof technique.
5. **Finiteness-and-chi's gate** (LOW, scheduling only). `Existence.lean` (file 5) is the only file
   blocked on `chi_zero_add_degree_le_l`/`exists_ne_zero_mem_linSys` landing; per §1.5, their own
   downstream map commits to this exact shape, so the risk is purely one of *timing*, not
   *interface* — build files 1–4 and 6 (the `holomorphicMFormsEquiv` half) first regardless.
6. **`MeromorphicOn.analyticOnNhd_of_order_nonneg`-style bridge name** (D12/P6, LOW). Exact
   mathlib name for "`MeromorphicOn` with nonneg order everywhere ⇒ `AnalyticOnNhd`" was not
   independently re-verified in this design pass (budget); if absent, it is a direct corollary of
   `MeromorphicNFAt`/`toMeromorphicNFOn` repair machinery ALREADY used by `MeroGermOn.holoRepr`
   (§1.3, `OrderEval.lean:225-320`, spike-verified project-wide) — worst case, reuse `holoRepr`'s
   own construction directly instead of a hypothetical named mathlib lemma.

---

## 8. Spike report (`scratch_canon.lean`, project root)

Gated per compile discipline (`pgrep -cx lean < 3`), run `lake env lean scratch_canon.lean`:
**compiles clean, exit 0** (two rounds of fixes needed, both `apply`/argument-order issues in
tactic proofs, not conceptual — recorded below for the next builder).

1. **`MForm`'s bare structure shape elaborates** exactly as stated in D1/§4.1 — `MeromorphicOn`
   (mathlib) slots into the Form01-mirrored shape with zero friction, `deriv (chartAt ℂ x ∘
   (chartAt ℂ y).symm)` (no conjugate) typechecks against the `ℂ`-valued coefficients.
2. **`Form1.analyticOnNhd_coeffIn η (chart_mem_maximalAtlas x) |>.meromorphicOn`** typechecks and
   has exactly the claimed type `MeromorphicOn (coeffIn (chartAt ℂ x) η) (chartAt ℂ x).target` —
   confirms the `d : Form1 ↪ MForm` bridge input (§2 D7) needs no adapter lemma, direct
   composition of two already-built/mathlib facts.
3. **`MeromorphicAt.deriv`** (mathlib) applies directly to `hf : MeromorphicAt f z₀` giving
   `MeromorphicAt (deriv f) z₀` with NO side condition — confirms `MForm.d`'s
   `meromorphicOn_coeffAt` field (§2 D7) is unconditional, no case split needed there (the case
   split is ISOLATED to `compat`, item 4 below).
4. **The chart-invariance-of-`DifferentiableAt` lemma** (P1's core technical step) compiles:
   given `hd : DifferentiableAt ℂ (g ∘ e.symm) (e p)`, concludes `DifferentiableAt ℂ (g ∘ e'.symm)
   (e' p)` via `differentiableAt_trans` (built, `Coeffs.lean:212`) + an `EventuallyEq`-through-the-
   transition congruence (`e'.symm =ᶠ[𝓝 (e' p)] e.symm ∘ (e ∘ e'.symm)`, the identical fact
   `coeffIn_trans` itself establishes) + `DifferentiableAt.comp`/`Filter.EventuallyEq.
   differentiableAt_iff`. **Two fix-ups needed during the spike** (recorded for the builder): (i)
   `e'.continuousAt_symm (e'.map_source hp')` must be bound via an explicit `have` BEFORE calling
   `.preimage_mem_nhds` — chaining them directly via `apply (...).preimage_mem_nhds` left a
   stray `e' p ∈ e'.target` goal from elaboration-order ambiguity (harmless once split into two
   `have`s); (ii) `differentiableAt_trans`'s two hypotheses are `hzt : z ∈ e'.target` (via
   `e'.map_source hp'` directly, NOT a `rw`-target) and `hzs : e'.symm z ∈ e.source` (via `rw
   [e'.left_inv hp']; exact hp`) — conflating them (trying to `rw` BOTH through `e'.left_inv`) is
   the wrong shape, since the first goal has no `e'.symm (e' p)` subterm to rewrite. Both are
   one-line fixes once diagnosed; no fallback needed, the lemma compiles as designed.

No other spike content attempted (all-`D`/gluing/existence-chain items are proof-plan-level,
appropriately deferred to the builder per the "one short end spike" budget — the four items above
are the ones flagged riskiest by the task brief: "the chart-family structure + Form1 bridge
constructor shapes").

---

## 9. Downstream map (who consumes what)

- **laurent-tails** (`Builds on: canonical-forms, meromorphic-trace`): `MForm`, `MForm.OmegaSpace`/
  `i D`/`Ω_iso_linSys` (D11 — their tail-space `T[D]` sits between `Ω(D)` and `L(D+K)`, this
  unit's bridge is their starting dictionary), `canonicalDivisorOf` (a concrete `K` to state the
  tail-form Riemann–Roch against), `MLFormData` (D13, likely their Laurent-tail-vs-form-principal-
  part comparison object).
- **monodromy** (`Builds on: canonical-forms, sphere-topology`): almost certainly only needs
  `MForm.d`/`dlog` is NOT their concern (they build primitives of HOLOMORPHIC forms via chains of
  charts, i.e. consume `Form1`/`mdifferential` directly, per CC6) — re-check their design doc when
  written; flagged here as a possible false dependency in the blueprint's edge (mirrors form-trace-
  tower's own §0.3-style DAG audit finding — not resolved here, left for monodromy's designer).
- **residue-theorem** (`Builds on: canonical-forms, planar-stokes-atoms`): `MForm`, `MForm.resAt`
  (D4), `resAt_eq_of_mem_source` (P4, needed if their PoU pieces read residues in non-`chartAt`
  charts), `MForm.divisor` (to state "sum over the support"), `MLFormData`/`resAt_dlog` (item 4's
  argument-principle-style facts) for their `∑ Res = 0` statement's hypotheses.
- **serre-duality-cech** (`Builds on: canonical-forms`): `MForm.OmegaSpace`/`i D` (D11, their
  dimension-counting core is stated against exactly this), `canonicalDivisorOf`/
  `canonicalDivisorOf_linearEquiv` (D10, their pairing is stated for "a" `K`, needs the well-
  definedness fact to know the numerical statement doesn't depend on which nonzero `ω₀` was
  fixed), `MLFormData`/`totalRes` (D13, per residue-calculus's own note that this is exactly their
  expected consumer).
- **riemann-roch** (`Builds on: serre-duality-tails`, indirect): `deg K = 2g − 2`/`l(K) = g` are
  NOT proved here (need Serre duality) but the export they'll rewrite through is
  `genus_eq_finrank_omegaSpace_zero` (D12) + `i_eq_l_add_canonicalDivisorOf` (D11) at `D := 0`.
- **abel-weak-solutions / abel-theorem**: indirect only, through `form-trace-tower`'s own
  consumption of `canonical-forms`'s FUTURE general system (flagged, not yet needed,
  `form-trace-tower.md` D1/§0.3) — no direct export currently required.
- **cech-h1-genus**: `genus_eq_finrank_omegaSpace_zero` (D12) is the bridge their `h1(0) = l(K) = g`
  chain needs on our side (their `h1(0) = l(K)` half is serre-duality-tails' job).

---

## 10. Coordination notes filed

- `docs/requests/meromorphic-and-divisors.md`: request `Divisor.single`/`degree_single` as a
  first-class export (currently only Compat-available here, §1.6) — flagged as generically useful
  beyond this unit (laurent-tails/riemann-roch will also want point divisors).
- No blueprint edit filed: the blueprint's `Builds on:` edges for canonical-forms
  (`finiteness-and-chi, residue-calculus`) are confirmed accurate and sufficient — no missing
  upstream dependency found (unlike form-trace-tower's/meromorphic-trace's own DAG-correction
  precedents).
