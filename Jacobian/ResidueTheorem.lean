import Jacobian.ResidueTheorem.RationalOnP1

/-!
# residue-theorem (namespace `RS`/`RS.P1`) — PARTIAL DELIVERY, read in full before building on it

Unit: residue-theorem (`docs/design/residue-theorem.md`). Blueprint target: `∑_p Res_p(θ) = 0` for
a meromorphic 1-form `θ : MForm X` on a compact connected Riemann surface `X`, any genus. Per the
orchestrator addendum on the design doc, the primary route is §6 (trace-to-`ℙ¹`, via a nonconstant
map, now that `Jacobian/FormTrace/` landed with `resAtP1_trace_eq_sum`), with the PoU/Stokes route
(§3–5, the Area-Gluing atom) explicitly NOT to be built.

**Neither the `ℙ¹` base case nor the general-`X` theorem is proved in this unit as shipped.** This
is a genuine shortfall against the task brief; read the two gap accounts below (and
`Jacobian/ResidueTheorem/RationalOnP1.lean`'s module docstring, more detailed on the first) before
extending this unit, so the next attempt does not have to rediscover either blocker.

## What IS delivered, zero sorries (`RationalOnP1.lean`, ~330 lines)

A collection of independently correct, reusable atoms toward the `ℙ¹` base case (task item 2):

* `RS.P1.formOfCoeFn` — builds a genuine two-chart `MFormData (OnePoint ℂ)` from a finite-chart
  coefficient function, given its `invChart`-transported reading is also meromorphic.
* `RS.P1.coeffAt_coe_eq_coeffAt_coe` — `ℙ¹`'s finite points all share `coeChart`, so any
  `MFormData`'s finite-chart coefficient is literally one function, not merely germ-compatible ones.
* **The Liouville-free key fact**: `RS.P1.resAt_neg_sq_inv_mul_comp_inv_eq_zero` — the residue at
  `∞` of an *entire* function's `invChart` reading is `0`, proved via Cauchy's theorem transported
  through the `z ↦ z⁻¹` contour reindexing (`RS.P1.circleIntegral_inv_eq_neg`), NOT a
  polynomial-growth/degree argument. This is cheaper than what the (superseded) non-quotient
  `form-trace-tower` design had budgeted for the same step.
* `RS.P1.meromorphicAt_neg_sq_inv_mul_sub_inv_zpow` / `RS.P1.resAt_neg_sq_inv_mul_sub_inv_zpow` —
  the single-monomial "companion pole at `∞`" computation (residue `-1` at `k = -1`, `0` otherwise).

## Gap 1: the `ℙ¹` assembly (task item 2) — a specific, well-understood blocker

Every remaining piece of the assembly (extracting the finite pole set from `θ.divisor`, building
the finite-pole-principal-part tail as a second `formOfCoeFn` instance, the order-arithmetic
argument that the remainder has order `≥ 0` at every finite point via `MeromorphicAt.orderAt_sub_
principalPartAt_nonneg` + `Finset.analyticAt_fun_sum`, and the `θ.coeffAt ∞` transition-rule
formula) was worked out and test-compiled during this build. The one step that does NOT go through
as stated: the remainder's finite-chart coefficient `R_mid`, built by bare pointwise subtraction of
two `MeromorphicAt`-only functions, is only known to have order `≥ 0` at the finitely many
former-pole points — `MeromorphicAt` does not pin down the actual *value* there (junk convention),
so `R_mid` need not be *continuous*, hence not `Differentiable ℂ R_mid` as the Liouville-free fact
above requires verbatim. Fix sketched (not attempted): weaken that fact to require differentiability
only on `closedBall 0 R₀ \ {0}` for `R₀` smaller than the nearest nonzero former pole (routine via
`Set.Finite`), since the circle-integral argument only ever needs one disk and `resAt` at `0`
doesn't care which. See `RationalOnP1.lean`'s docstring for the full account.

## Gap 2: the general-`X` reduction (task items 1, 3, 4) — a second, independent blocker

The design's §6 route reduces the general case to the `ℙ¹` base case via a nonconstant meromorphic
map `f : ℳ X` (`F := RS.MTrace.toP1 f`) and `Jacobian/FormTrace/ResidueTraceCompat.lean`'s
`resAtP1_trace_eq_sum` (BUILT, zero sorries, confirmed by reading it in full). The natural way to
feed an arbitrary `θ : MForm X` into that machinery is to write `θ = h • θ₀` for some reference
`θ₀` and `h : ℳ X` (canonical-forms' D8, `MForm.exists_unique_smul_of_ne_zero`), matching it against
`resAtX F h x` (`RS.FormTrace.resAtX`, form-trace-tower's pair-form residue, `h · F^*(dz)`).
**This does NOT work with `θ₀ := MForm.d f`** (the obvious candidate): `MForm.d f`'s coefficient at
a POLE of `f` is `deriv(f-in-chart)`, which is a genuinely different (higher-order) singularity
than `F^*(dz)`'s own coefficient there (`d(1/f)`-shaped, matching `resAtX`'s convention, checked
directly by unfolding both sides at a pole of `f`). Closing this gap needs a dedicated `MForm.
ofPullback F` construction — literally assembling the `F^*(dz)` 1-form as its own `MFormData`
object via `resAtX`'s own per-chart formula (using `IsManifold`'s maximal-atlas machinery already
built, e.g. `analyticAt_comp_chart_pair`, `analyticAt_transition`) — which is itself a
self-contained ~100–200 line task, NOT ATTEMPTED here; then the `θ = h • (F-pullback)` reduction and
the `FiberStack`-indexed sum-over-fibres bookkeeping (design §6.2, "~40–60 lines" per that design,
likely more once the pullback object's own chart-transition proof is threaded through) on top of
that. Given the `ℙ¹` base case itself (gap 1) was not finished either, `residue_sum_eq_zero_of_
exists_nonconstant` and its hypothesis-free wrapper are NOT stated at all (a hard "zero sorries"
constraint rules out stating an unproved theorem; better an honest gap than a broken signature a
downstream unit might cite).

## Notes for downstream consumers

* **serre-duality-tails** (the only unit whose frozen edge points here, confirmed by both units'
  own DAG audits): needs `∑ᶠ p, θ.resAt p = 0` (or the `Finset`-flexible form) for general `θ : MForm
  X` — see `docs/requests/residue-theorem.md`'s exact requested statement, `sum_resAt_eq_zero`, and
  its confirmation that `(f • θ).resAt` reduces to the same general fact (`coeffAt_smul_mero` is
  `rfl`). **Not available from this unit as shipped** — flagged loudly to the orchestrator; this is
  the single load-bearing consequence of the two gaps above. `serre-duality-tails`'s own risk R2
  already anticipates gating on this unit landing.
* **abel-weak-solutions**: does not need anything from this unit (confirmed absent from its frozen
  `Builds on:` edge, matching the design doc's own DAG audit at §7).
-/
