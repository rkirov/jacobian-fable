# Requests to unit: projective-line

## From meromorphic-trace (design phase, 2026-07-06, non-blocking)

1. **DAG correction.** `clean_room_blueprint.md`'s `meromorphic-trace` entry lists
   `Builds on: jacobian-construction, residue-calculus` only. The actual design
   (`docs/design/meromorphic-trace.md` §0.2) needs `projective-line` directly (`OnePoint ℂ`,
   `coeChart`/`invChart`, `chartAt_coe`/`chartAt_infty`) for the induced map `f : X → ℂ` meromorphic
   `⇒ toP1 f : X → ℙ¹` holomorphic bridge (the argument-principle engine). Please ask the
   orchestrator to add this edge when convenient; nothing blocks on the correction itself.

2. **`Holomorphy.lean` not yet built — we did not wait.** Your design doc (§3.3) records a
   "deliverable-for-later" bridge `ℳ.toP1`/pole-and-coe constructors
   (`contMDiffAt_of_pole`, `ContMDiffAt.onePointCoe`, `meromorphicAt_coeChart_comp`) intended for
   once `ℳ X` exists. We needed an `f`-to-`ℙ¹` bridge *now* (for the argument principle), so we
   built our own raw-function version locally in `Jacobian/MeromorphicTrace/ToP1.lean`, using
   only your **already-built** `Charts.lean` (`chartAt_coe`, `chartAt_infty`,
   `coeChart_apply_coe/infty`, `invChart_apply_coe/infty`) plus local-multiplicity's general
   `X → Y` bridge (`LMCompat.contMDiffAt_iff_analyticAt_inChartAt`) — no dependency on your
   `Holomorphy.lean`.
   - If/when `Holomorphy.lean` lands with the signatures your design doc records, our
     `toP1_contMDiff` proof (`docs/design/meromorphic-trace.md` §5, P1) can likely be shortened by
     reusing your general `contMDiffAt_iff_analyticAt_of_ne_infty`/`_of_eq_infty` iff-lemmas
     instead of re-deriving the same case split by hand. This is a cosmetic simplification, not
     a correctness dependency — no action needed from you, and please don't reshape
     `Holomorphy.lean`'s signatures on our account.
   - Separately: once your own `ℳ.toP1`/`Holomorphy.lean` machinery exists, it would be natural
     for `meromorphic-trace`'s `toP1` to become a thin wrapper delegating to yours (or for the two
     to be reconciled by whichever lands second) — flagging so neither unit "owns" the final
     shape unilaterally; we are not proposing to change your recorded signature.

3. **Confirmation of exports we consume unchanged**: `chartAt_coe`, `chartAt_infty`,
   `coeChart_apply_coe`, `coeChart_apply_infty`, `invChart_apply_coe` (unconditional, `∀z`, no
   `z≠0` guard — load-bearing for our pole-case proof, please keep it unconditional per your own
   design doc's "freeze policy" note), `invChart_apply_infty`, `coeChart_mem_maximalAtlas`,
   `invChart_mem_maximalAtlas`.
