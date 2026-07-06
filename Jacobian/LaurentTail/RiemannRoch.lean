import Jacobian.LaurentTail.Comparison

/-!
# The Riemann–Roch bridge (laurent-tails, design §4.4) — DEFERRED, gated on `finiteness-and-chi`

Unit: laurent-tails (`docs/design/laurent-tails.md` §4.4, §0).

**Status: this file is empty of content.** Everything the design doc's §4.4 lists (`g0`,
`H1Tail.finiteDimensional`, `h1tail`, `h1tail_eq_h1`, `firstFormRR`, the tail-level six-term
sequence restatement) is a **transport** of `finiteness-and-chi`'s χ ledger across the comparison
`H1Tail.equiv` — genuinely no new mathematics, purely `Module.Finite.equiv`/`LinearEquiv.finrank_eq`
one-liners once both inputs exist. Neither input is available as of this build:

1. **`Jacobian/Finiteness/Chi.lean` does not exist on disk** (confirmed: `Jacobian/Finiteness/`
   contains only `Schwartz.lean`/`BddHolo.lean`/`CompactRestrict.lean`/`Chain.lean`;
   `Jacobian/Finiteness.lean`'s own root docstring records `TradeBounded.lean`/`H1Finite.lean`/
   `Chi.lean` as gated on `dolbeault-comparison`, itself still absent as a `Jacobian/
   DolbeaultComparison/` directory beyond `Leray.lean`). So `RS.Finiteness.h1`/`RS.Finiteness.chi`/
   `RS.Finiteness.chi_eq_chi_zero_add_degree`/`RS.Finiteness.finiteDimensional_H1` do not exist as
   identifiers — there is nothing to state `g0`/`h1tail_eq_h1`/`firstFormRR` *against*, let alone
   prove.
2. **`Comparison.lean`'s `H1Tail.equiv` is itself deferred** (see that file's own file-end note):
   `tailToH1 : T D →ₗ[ℂ] Cech.H1 D` is fully built, but `H1Tail.toH1`/injectivity/surjectivity/
   `H1Tail.equiv` are not yet, gated on (a) a multi-point Mittag-Leffler combination lemma
   (in-unit, fully scoped) and (b) `dolbeault-comparison`'s Leray surjectivity theorem (upstream,
   soft dependency, not circular).

`RS.l` (`Jacobian/Meromorphic/LinearSystem.lean:98`) already exists, so `firstFormRR`'s statement
*shape* is expressible the moment `RS.Finiteness.h1`/`chi_eq_chi_zero_add_degree` land — but with
`H1Tail.equiv` itself gated, restating it here now would only add an unusable stub. Per
`CONVENTIONS.md` rule 3 ("no vacuous instances", genuine explicit hypotheses only), this file is
left with no declarations rather than a placeholder that cannot be verified to have the intended
computational content.

**Completion recipe for whoever picks this up** (once both gates open): restate §4.4 of the design
doc verbatim —
```lean
noncomputable def g0 : ℕ := RS.Finiteness.h1 (0 : RS.Divisor X)
instance H1Tail.finiteDimensional (D) : FiniteDimensional ℂ (H1Tail D) :=
  Module.Finite.equiv (H1Tail.equiv D).symm
noncomputable def h1tail (D) : ℕ := Module.finrank ℂ (H1Tail D)
theorem h1tail_eq_h1 (D) : h1tail D = RS.Finiteness.h1 D := LinearEquiv.finrank_eq (H1Tail.equiv D)
theorem firstFormRR (D) : (RS.l D : ℤ) - (h1tail D : ℤ) = D.degree + 1 - (g0 : ℤ) := …
```
plus the tail-level six-term sequence (`exact_windowToT_H1Tail_mk`/`exact_H1Tail_mk_incl`,
conjugating `Cech`'s own six-term fragment by `H1Tail.equiv`) — every proof is a direct citation,
no new analysis, per the design doc §0/§6's own explicit recommendation not to re-derive
Miranda's finiteness route independently.
-/
