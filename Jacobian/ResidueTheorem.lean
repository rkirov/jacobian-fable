import Jacobian.ResidueTheorem.RationalOnP1
import Jacobian.ResidueTheorem.MFormCompat
import Jacobian.ResidueTheorem.Calibrated
import Jacobian.ResidueTheorem.P1Assembly
import Jacobian.ResidueTheorem.Reduction

/-!
# residue-theorem (namespaces `RS`/`RS.P1`) — HEADLINE CLOSED

Unit: residue-theorem (`docs/design/residue-theorem.md`). Blueprint target: `∑_p Res_p(θ) = 0`
for a meromorphic 1-form `θ : MForm X` on a compact connected Riemann surface `X`, any genus.
Built along the §6 trace-to-`ℙ¹` route (PRIMARY per the orchestrator addendum; the PoU/Stokes
Area-Gluing atom of §3–5 was NOT built, as instructed).

## Deliverables (zero sorries)

* **THE residue theorem** — `RS.residue_sum_eq_zero_of_exists_nonconstant`
  (`Reduction.lean`):
  ```
  theorem residue_sum_eq_zero_of_exists_nonconstant
      [T2Space X] [CompactSpace X] [ConnectedSpace X]
      (hex : ∃ f : ℳ X, ∀ c : ℂ, f ≠ algebraMap ℂ (ℳ X) c) (θ : MForm X) :
      ∑ᶠ x, θ.resAt x = 0
  ```
  The hypothesis `hex` is EXACTLY canonical-forms D9's `exists_nonconstant_mero` export shape
  (`∃ f : ℳ X, ∀ c : ℂ, f ≠ algebraMap ℂ (ℳ X) c`, frozen in
  `docs/design/canonical-forms.md` §D9). `CanonicalForms/Existence.lean` is still not on disk
  (gated on the finiteness-and-chi existence chain; `Finiteness/Chi.lean` has landed but the
  D9 export has not), so per the design the theorem is stated against the hypothesis; the
  unconditional `residue_sum_eq_zero` is literally
  `residue_sum_eq_zero_of_exists_nonconstant exists_nonconstant_mero θ` once D9 lands.
* **serre-duality-tails' consumption shape** (`docs/requests/residue-theorem.md`) —
  `RS.MForm.sum_resAt_eq_zero_of_exists_nonconstant (hex) (f : ℳ X) (θ : MForm X) :
  ∑ᶠ x, (f • θ).resAt x = 0`, the well-definedness input of `RS.TailDuality.pairT_alpha`.
  Also the `Finset`-flexible `RS.residueTheorem_of_exists_nonconstant`.
* **The `ℙ¹` base case** — `RS.P1.sum_resAt_eq_zero (Θ : MForm (OnePoint ℂ)) :
  ∑ᶠ y, Θ.resAt y = 0`, UNCONDITIONAL (`P1Assembly.lean`; `ℙ¹` supplies its own coordinate
  function, no existence hypothesis needed).

## How the two previously-documented gaps were closed

1. **`ℙ¹` assembly (Gap 1)**: the junk-value blocker ("`R_mid` has order `≥ 0` at former poles
   but need not be continuous there") is repaired via mathlib's meromorphic normal form:
   `RS.P1.exists_differentiable_of_ord_nonneg` produces an ENTIRE representative of the
   principal-part remainder agreeing with it at every honest-analyticity point (in particular
   near `∞`, where honesty is forced by the two-chart `compat` identity
   `RS.P1.coeffAt_infty_eq` + meromorphy of the `∞` coefficient). The Liouville-free contour
   fact and the monomial companion-pole computations of `RationalOnP1.lean` then close the
   telescope. No weakened-radius variant was needed.
2. **General-`X` reduction (Gap 2)**: no `MForm.ofPullback` object is needed. The
   `d f`-vs-`resAtX` convention mismatch at poles is exactly the target-chart transition
   `dz = -(w²)⁻¹ dw`, handled by pushing TWO coefficient functions along `F := toP1 φ.holoRepr`
   — `h.holoRepr` over finite values and `Hinf := -(φ.holoRepr)²·h.holoRepr` over `∞` —
   matched to `(h • MForm.d φ).resAt` fibre-point-by-fibre-point
   (`RS.resAtX_toP1_eq_of_ord_nonneg` / `RS.resAtX_toP1_eq_of_ord_neg`), with the two traces
   glued into a single `MFormData (OnePoint ℂ)` by `P1.formOfCoeFn` via
   `trace_const_mul_pullback`. The `hcal` calibration hypothesis of form-trace-tower's
   `resAtP1_trace_eq_sum` is discharged by `RS.exists_fiberStack_translated`
   (`Calibrated.lean`, the existence proofs of `exists_adaptedChartsAt`/`exists_fiberStack`
   re-run with the construction-inherent "target chart is a recentered `chartAt`" conclusion
   exposed). `θ = h • d φ` comes from D8 one-dimensionality, seeded by
   `RS.MForm.d_ne_zero` (the differential of a nonconstant function is nonzero — the
   identity-theorem dichotomy).

## File map

* `RationalOnP1.lean` — the ℙ¹ atoms (previous delivery, unchanged): `formOfCoeFn`,
  the Liouville-free `resAt_neg_sq_inv_mul_comp_inv_eq_zero`, the monomial companion poles.
* `MFormCompat.lean` — `MForm.resAt_eq_zero_of_ord_nonneg`, `MForm.finite_setOf_ord_neg`,
  `MForm.finite_support_resAt` (Compat, upstream candidates for canonical-forms).
* `Calibrated.lean` — calibrated adapted charts / fiber stacks.
* `P1Assembly.lean` — the ℙ¹ base case.
* `Reduction.lean` — the bridges, `MForm.d_ne_zero`, THE theorem, the tails corollary.

## Notes for downstream consumers

* **serre-duality-tails** (the only DAG-wired consumer): consume
  `RS.MForm.sum_resAt_eq_zero_of_exists_nonconstant`, threading the same `hex` your unit
  already needs for its `θ₀ ≠ 0` reference forms — or wait for canonical-forms D9 and wrap.
  Shape confirmed against `docs/requests/residue-theorem.md` (the `(f • θ)`-finsum form).
* **canonical-forms**: `MFormCompat.lean`'s three lemmas are upstream candidates (requested
  at design time in `docs/design/residue-theorem.md` §11).
-/
