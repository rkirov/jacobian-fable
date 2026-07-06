import Jacobian.TailDuality.TailOps
import Jacobian.TailDuality.Pairing
import Jacobian.TailDuality.Counting
import Jacobian.TailDuality.Duality

/-!
# serre-duality-tails: Serre duality via Laurent tails (Miranda VI.3) (namespace `RS.TailDuality`)

API summary (see `docs/design/serre-duality-tails.md` and its orchestrator addendum
2026-07-08). Builds on `laurent-tails`, `canonical-forms`, `finiteness-and-chi`,
`residue-theorem` (all BUILT). **Unit COMPLETE at the tail level**: zero sorries,
`scripts/check.sh Jacobian/TailDuality` passes. **NOT registered in `Jacobian.lean`**
(orchestrator's job).

Per the orchestrator addendum, this unit works entirely at the Laurent-tail level
(`LaurentTail.T D`/`LaurentTail.H1Tail D`) and does **not** wait on `H1Tail.toH1`'s surjectivity
(the Čech comparison `H1Tail D ≃ₗ Cech.H1 D`) — that fact is classically Serre-circular and out
of scope for this challenge. Finiteness of `H1Tail D` instead comes from the unconditional
`H1Tail.toH1_injective` (laurent-tails) plus `Finiteness.finiteDimensional_H1` (an injection into
a finite-dimensional space).

## File plan

* **`TailOps.lean`**: `truncAt`/`truncT` (Miranda's `t^{D₁}_{D₂}`, surjective, compatible with
  `alphaL`), `singleT` (test-vector tails), `mulIntoAt`/`mulInto` (Miranda's `t∘μ_f`, linear in
  `f`, surjective for `f ≠ 0`), `nuL` (the packaging into `T(A-C) →ₗ T A`) + `nuL_mulInto_inv`
  (the `μ_{1/f}` inversion identity), and the `LinSys`/order bookkeeping helpers
  (`LinSys.divisor_ge`, `Mero.ord_eq_divisor`, `sub_divisor_le`).
* **`Pairing.lean`**: `readAt` (chart-read of a germ as a punctured planar germ), `pairAtData`/
  `pairAt`/`pairTailAt`/`pairT` (Miranda's `Res_ω` on `T[D]`, built on `MFormData` then descended
  to `MForm` by `Quotient.liftOn`), `pairT_trunc`/`pairT_mulInto` (the diagram compatibilities),
  `pairT_alpha` (the well-definedness `∑ Res = 0`, the **only** residue-theorem citation),
  `pairAt_tailGerm_order_ne_zero`/`pairT_ne_zero` (Miranda Thm 3.3's injectivity half), `resMap`/
  `resMap_injective` (the induced map into `Dual(H1Tail D)`, injective).
* **`Counting.lean`**: `instFiniteDimensional_H1Tail`/`h1T`/`h1T_le_h1` (finiteness + the one
  Čech-side fact Lemma 3.4 needs), `nuPairDual`/`two_l_le_h1T_of_injective`, and
  **`exists_mul_functional_eq`** (Miranda **Lemma 3.4**).
* **`Duality.lean`**: **`mem_omegaSpace_of_vanishing_ker_trunc`** (Miranda **Lemma 3.6**),
  **`exists_pairT_eq`** (Miranda Thm 3.3's surjectivity half — the endgame combining Lemma 3.4,
  the `μ_{f₁}` inversion, and Lemma 3.6 applied twice), `resMap_surjective`/`resEquiv` (`resMap`
  is a linear ISOMORPHISM `Ω(-D) ≃ₗ Dual(H1Tail D)`), and the export bank below.

## Export bank (all in namespace `RS.TailDuality`, all with no admitted steps)

* **`i_neg_eq_h1T (D) : MForm.i (-D) = h1T D`** — the frozen duality obligation, re-based at the
  tail `h¹` per the orchestrator addendum (`RS.MForm.i` is the exact name; `RS.i` as literally
  written in serre-duality-cech's D6/the design doc does not exist as a top-level export — only
  `RS.MForm.i`, since `i` lives in `namespace MForm`).
* **`l_sub_eq_h1T {ω₀} (h₀ : ω₀ ≠ 0) (D) : RS.l (canonicalDivisorOf ω₀ - D) = h1T D`** — the
  `l(K-D)` shape riemann-roch (#28) consumes directly.
* **`h1T_zero_eq_l_K {ω₀} (h₀) : h1T 0 = RS.l (canonicalDivisorOf ω₀)`**.
* **`h1T_zero_eq_genus : h1T 0 = genus X`** — cech-h1-genus (#27)'s re-based deliverable
  (`dim H¹(X,𝒪) = g` at the tail `h¹`; the Čech-`h1` version stays open, gated on
  `H1Tail.equiv`/`tailToH1`'s surjectivity, per laurent-tails' own status).
* **`h1T_canonical {ω₀} (h₀) : h1T (canonicalDivisorOf ω₀) = 1`**.
* `resEquiv (D) : ↥(MForm.OmegaSpace (-D)) ≃ₗ[ℂ] Module.Dual ℂ (H1Tail D)` — the
  functional-level isomorphism (Miranda Thm 3.3 exactly as stated, not just the dimension count);
  this is the shape `Jacobian/Abel/Sufficiency.lean`'s blocked step needs (see below).
* `chiT (D) := (RS.l D : ℤ) - (h1T D : ℤ)` — defined, but its additivity
  (`chiT D = chiT 0 + deg D`) is **NOT delivered** (honest gap; see `Duality.lean`'s file
  docstring for the precise reason and a recorded proof sketch for whoever picks it up).
  riemann-roch (#28) should combine `l_sub_eq_h1T`/`h1T_zero_eq_genus`/`RS.l_zero` with
  `Finiteness.chi_eq_chi_zero_add_degree` (Čech-level, already built) directly instead.

## Consumer notes

* **riemann-roch (#28)**: cite `l_sub_eq_h1T`, `h1T_zero_eq_genus`, `h1T_zero_eq_l_K`,
  `h1T_canonical` together with `RS.Finiteness.chi_eq_chi_zero_add_degree`/`chi_zero_add_degree_le_l`
  (already built, Čech-level) and `RS.l_zero`; the combination is pure ℤ-arithmetic (`omega`),
  exactly as design §9.1 anticipated.
* **cech-h1-genus (#27)**: re-based to `h1T_zero_eq_genus` (`finrank (H1Tail 0) = genus X`); the
  literal Čech-`H1` statement (`Finiteness.h1 0 = genus X`) is NOT produced here (would need
  `H1Tail.equiv`, gated on the same out-of-scope surjectivity) — document as open/optional.
* **`Jacobian/Abel/Sufficiency.lean`'s blocked step** (its own admitted step at line 71): its design
  (`docs/design/abel-theorem.md` §4.3) expected `RS.H1Tail.equiv` (the FULL, unconditional
  Čech comparison) composed with `resEquiv 0`. That full equivalence is **not available**
  (blocked on the same out-of-scope surjectivity as above) — only `resEquiv 0 :
  ↥(MForm.OmegaSpace 0) ≃ₗ[ℂ] Module.Dual ℂ (H1Tail 0)` (tail-level) and
  `LaurentTail.H1Tail.equiv_of_surjective` (conditional) exist. The Abel fixer's bridge needs
  restating at the tail level (through `H1Tail`, not `Cech.H1`) or needs to accept the
  conditional equivalence as a hypothesis.
-/
