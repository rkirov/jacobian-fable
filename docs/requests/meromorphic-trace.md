# Requests for `meromorphic-trace` (from downstream designers/builders)

## From form-trace-tower (designer; see `docs/design/form-trace-tower.md`)

Read `Jacobian/MeromorphicTrace/{ToP1,OrderMultiplicity,PlanarTrace}.lean` directly off disk at
design time (2026-07-06). `PlanarTrace.lean`'s cluster-2 content (`traceZk`, `analyticAt_traceZk`
P4, `meromorphicAt_traceZk` P5) is fully proved, zero sorries — used as-is, no request there.
Two asks:

1. **`laurentCoeffAt_traceZk` (P6) is the single load-bearing external dependency of our whole
   unit.** Our central theorem (Miranda Lemma 3.2 globalized, `resAtP1_trace_eq_sum` in
   `FormTrace/ResidueTraceCompat.lean`) reduces, via a small Jacobian-factor cancellation we
   verified mechanically (`scratch_ftt.lean`, both facts spiked, exit 0), to exactly your P6 at
   the index `j = -1`. We do NOT need the general P6 for anything else (existence of meromorphy of
   our `traceZkForm` only needs your already-proved P5). If P6 remains stuck on the two routes
   your in-file comment documents (the `tsum`/`HasFPowerSeriesAt` termwise-substitution route, or
   the exact-remainder `AnalyticAt.exists_taylor_remainder` route), please flag it explicitly so we
   can decide between (a) waiting, (b) attempting P6 ourselves in coordination with you, or (c)
   shipping our unit with the coefficient-level theorems stated with P6's conclusion as an explicit
   hypothesis (no cost to us either way — see our design doc §7 Risk 1 for the fallback we've
   already planned). We looked at an alternative contour-integral/substitution route
   (`circleIntegral_eq_two_pi_I_mul_resAt` + `z = w^k` substitution) as a possible independent
   derivation and concluded it likely reproduces the same "which branch of `w` covers which arc of
   `z`" combinatorics your `tsum` route hit, just in integral language — not obviously cheaper, so
   we are not planning to pursue it as a first attempt. Happy to compare notes if useful.

2. **A "genuinely analytic `h` ⟹ genuinely analytic (not just meromorphic) `traceZk h k` at `0`"
   corollary of your P5.** Our `HolomorphicVanishing.lean` (tracing a holomorphic pair-form is
   holomorphic on `ℙ¹`, hence `≡ 0` by the already-built `RS.P1.form1_eq_zero`/`genus_onePoint`)
   needs this. It is a strict SIMPLIFICATION of your P5 proof: when `h` is analytic at `0` (order
   `n₀ ≥ 0`), the Euclidean-division quotient `q := n₀ / k` used in your growth-bound argument is
   itself `≥ 0`, so the `w^q`-factor-stripping step is unnecessary and `traceZk h k` is bounded (not
   just of controlled growth) on a punctured disk directly, giving genuine analyticity (not mere
   meromorphy) via the same removable-singularity lemma you already use
   (`Complex.differentiableOn_update_limUnder_of_bddAbove`). If you can export this as
   `analyticAt_traceZk_of_analyticAt` (or similar) alongside P5, it saves us re-deriving ~40 lines
   of near-duplicate argument; otherwise we'll prove it locally in a marked `Compat` section of
   `FormTrace/HolomorphicVanishing.lean` per `CONVENTIONS.md` rule 4 — non-blocking either way.

No other requests: everything else our design consumes from you (`traceZk`, `traceZk_comp_pow`,
`analyticAt_traceZk`, `meromorphicAt_traceZk`, and — once `FunctionTrace.lean` lands —
`RS.MTrace.trace`/`meromorphicAtX_trace`/`trace_of_regular`) is either already built or already
specified precisely enough in your design doc (D7, P7) for us to design against.
