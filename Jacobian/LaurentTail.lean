import Jacobian.LaurentTail.TailSpace
import Jacobian.LaurentTail.Truncation
import Jacobian.LaurentTail.Comparison
import Jacobian.LaurentTail.RiemannRoch

/-!
# laurent-tails: Miranda's Laurent-tail calculus for `H¹(D)` (namespace `RS.LaurentTail`)

API summary (see `docs/design/laurent-tails.md`). Builds on `cech-cohomology` (BUILT) and
`meromorphic-and-divisors` (BUILT) only — the blueprint's listed `canonical-forms`/
`meromorphic-trace` edge is unused by this unit (§0 of the design doc; a DAG-imprecision note,
not a missing dependency). **NOT registered in `Jacobian.lean`** (orchestrator's job).

* **`TailSpace.lean`** (D1/D2/D4, zero sorries): `TailAt p D` (**`abbrev`**, germs at the chart
  source of `p` modulo `Cech.ordGe p (-(D p))`) + `TailAt.mk`/`mk_eq_zero_iff`/`mk_surjective`;
  `windowAt_toTailAt`/`exists_windowAt_repr` (Cech's finite window embeds, every class has *some*
  finite representative); `T D := Π₀ p, TailAt p D` (**`abbrev`**, `[DecidableEq X]`) + `T.mk`/
  `mk_apply_mem`/`mk_apply_not_mem`; `windowToT` (the finite skyscraper `Window D D'` embeds in
  `T D`, `[CompactSpace X]`). `mulTailAt`/`mulTail`/`mulTailEquiv` (design §2 D5) are **not
  built** — `serre-duality-tails` explicitly de-scopes them (their own `mulInto`, built directly
  on this file's carrier, supersedes it; a genuine scope relief, not a shortfall).
* **`Truncation.lean`** (D3, zero sorries): `alphaFinset`/`alpha`/`alphaL : ℳ X →ₗ[ℂ] T D`
  (Miranda's truncation map, `[CompactSpace X][ConnectedSpace X][T1Space X][DecidableEq X]`),
  `alpha_apply` (the pointwise-everywhere formula, not just on the witness `Finset`),
  `alpha_apply_eq_zero_iff`, `ker_alphaL_eq_linSys` (Miranda PDF 192: `L(D) = ker(α_D)`),
  `H1Tail D := T D ⧸ range(alphaL D)` + `H1Tail.mk`/`mk_surjective`/`mk_eq_zero_iff`.
* **`Comparison.lean`** (CC8's deliverable — **partially built**, see that file's own detailed
  file-end note for the exact account): `tailToH1 : T D →ₗ[ℂ] Cech.H1 D` **is fully constructed**
  (zero sorries) via a from-scratch per-point Mittag-Leffler class `mlClassAt`/`mlClassAtOf`
  (a 2-member-cover construction, proved independent of every choice via `mlClassAtOf_agree`) —
  this was the unit's hardest genuinely-new mathematical content. **Deferred**: `tailToH1_alpha`
  (gate: a new but fully-scoped multi-point combination lemma, generalizing this file's
  `mlClassAt_add` from two points to a `Finset`), hence `H1Tail.toH1`/injectivity/`H1Tail.equiv`;
  surjectivity additionally gated on `dolbeault-comparison`'s Leray theorem (not yet on disk,
  soft/non-circular dependency). Reusable byproducts for any consumer building `LinearMap`s into
  `Cech.H1 D`: a registered `AddCommGroup (Cech.H1 D)` instance (`instAddCommGroupH1`, needed
  because plain `inferInstance` does not find it through the `Module.DirectLimit` `abbrev` — see
  the file-end note), and `mlClass_congr` (transport `Cech.mlClass` along a cochain equality,
  avoiding the `rw`/`erw` "motive is not type correct" failure on `mlClass`'s dependent argument).
* **`RiemannRoch.lean`** (design §4.4 — **entirely deferred, empty of declarations**): gated on
  `finiteness-and-chi`'s `Chi.lean` (confirmed absent: only `Schwartz.lean`/`BddHolo.lean`/
  `CompactRestrict.lean`/`Chain.lean` exist in `Jacobian/Finiteness/`) *and* on `Comparison.lean`'s
  own deferred `H1Tail.equiv`. Every export it would provide (`g0`, `h1tail`, `h1tail_eq_h1`,
  `firstFormRR`, the tail-level six-term restatement) is a one-line transport once both gates
  open — no new mathematics — per that file's own completion recipe.

## Consumer notes (for `serre-duality-tails` and downstream)

The frozen bank this unit was asked to supply (`docs/design/serre-duality-tails.md` §0.1's own
audit already reconciled against these exact names): `T D`, `TailAt p D`, `alphaL D`,
`H1Tail D := T D ⧸ range(alphaL D)` are **all available now**, zero sorries, and match the frozen
shapes exactly. `H1Tail.equiv : H1Tail D ≃ₗ[ℂ] Cech.H1 D` — the comparison `serre-duality-tails`
needs to transport its residue-pairing dimension counts against `finiteness-and-chi`'s χ ledger —
is **not yet available** (see `Comparison.lean`'s file-end note for the exact multi-point gate);
`serre-duality-tails` should build everything that only needs `T D`/`TailAt p D`/`alphaL`/
`H1Tail D` now (per its own design doc §4's build-wave note: "file 1 gates only on
`TailSpace.lean`/`Truncation.lean` — NOT on `Comparison.lean`"), and revisit once `H1Tail.equiv`
lands. `mulTail`/`mulTailEquiv` are deliberately not built (see `TailSpace.lean`'s note above);
`serre-duality-tails`'s own `mulInto` supersedes them, already accounted for in that unit's design.
`firstFormRR`/`g0` (riemann-roch's eventual consumer) remain gated on `finiteness-and-chi`.
-/
