# Retrospective — the Jacobian challenge build

A post-mortem of formalizing Buzzard's Jacobians challenge, written by the orchestrating agent.

## Summary statistics

| Metric | Value |
|---|---|
| Lean code | **46,692 lines**, 212 files, 32 unit directories |
| Final state | zero `sorry`, zero extra axioms (all main items: `propext`, `Classical.choice`, `Quot.sound` only) |
| Acceptance | all 24 gist declarations witnessed verbatim (`GistAcceptance.lean`) |
| Commits | 85 |
| Wall clock | 2026-07-02 → 2026-07-07, interrupted by three usage-limit outages (one 4-day) |
| Agent runs | ~70 (3 scouts, 29 designers/design-phases, ~30 builders/finishers, 8 lost to outages and relaunched) |
| Design documents | 29 in `docs/design/`, every one with a compiled verification spike |
| Build journal | `docs/build-log.md`, 2,320 lines of per-file records and Lean gotchas |
| Verification gate | `scripts/check.sh` (unit build + sorry sweep) run by the orchestrator after every unit, never trusted from reports |
| Largest units | Abel 3,855 · Čech 3,380 · JacFunctorial 2,618 · Dbar 2,607 · CanonicalForms 2,085 |
| Machine | 4 cores / 7 GB RAM — max 3 concurrent `lean` processes via a `pgrep` semaphore |

## What worked well

1. **Design-then-build with compiled spikes.** Every unit got a design document whose riskiest
   mathlib-name and elaboration assumptions were verified by a small compiled spike *before* any
   builder started. Designs written from "compiled truth, not hope" almost never failed
   structurally; nearly all builder deviations were tactic-level.
2. **Freezing cross-cutting choices early (`docs/design/core-choices.md`).** The nine CC
   decisions (genus as bundled sections, germ-quotient `ℳ(X)`, divisors via
   `locallyFinsuppWithin`, closure-quotient Jacobian, primitive-based path integrals, …) were
   made once, centrally, and survived to the end. Units never re-litigated representations.
3. **The junk-free discipline.** The blueprint's central hazard — junk-valued representations
   silently making theorems vacuous — was enforced at every definitional site. When it was
   violated once (raw `MForm` chart families), it surfaced as a *provably false* lemma (D5)
   rather than a silent hole, and was fixed at the root with a quotient rebuild.
4. **Honest-gap protocol.** Builders were forbidden to leave silent sorries: gaps became either
   loud `TODO(blocker)` reports, unwritten files, or *named hypotheses* (`WeakSolutionUpgrade`,
   `DiscretenessHyp`) threaded through downstream statements. This let ten units build in
   parallel against unfinished dependencies and ungate automatically — the final `cechCount`
   theorem discharged four layers of gates by `inferInstance` with no downstream edits.
5. **Adversarial re-derivation caught real errors.** Builders found four false statements in
   otherwise-good designs, each with a counterexample: target-chart invariance of pair-form
   residues; `trace_eq_zero_of_holomorphic` (discontinuous at branch points); the continuous-
   cutoff smeared residue theorem (fails for poles of order ≥ 2); `multiplicity_toP1` at
   order-zero points. All were repaired by strengthening hypotheses, never by weakening claims.
6. **Gotcha propagation.** `docs/build-log.md` doubled as a shared engineering journal
   (instance-resolution walls, `ω`/`∞` identifier clashes, `Opens`-vs-`Set` coercion slowdowns,
   defeq-rejection vs timeout diagnosis). Later agents cited and reused these fixes constantly;
   the nested-`Submodule` instance post-mortem alone saved three subsequent units.
7. **Durable state across disasters.** Git commits at every milestone + the harness task DAG +
   memory files meant three hard outages (which killed up to 8 agents mid-flight) cost only the
   in-flight work — every relaunch resumed from disk within minutes.
8. **Cost tiering.** Sonnet handled ~85% of builds against strong-model designs; the strong
   model was reserved for make-or-break designs (∂̄, finiteness, tail duality) and for focused
   finishers on precisely-diagnosed hard gaps. Both tiers' outputs passed the same verification
   gate.

## What didn't work well

1. **Usage-limit outages.** Three interruptions killed whole agent fleets mid-write, losing
   final reports (the most information-dense artifact of a run). Recovery relied on
   reverse-engineering disk state; one 330-tool-use build had to be re-derived from its build-log
   entries.
2. **Stale-state decisions.** Agents read the disk at launch and reported against it: the
   residue-theorem designer recommended its fallback route because a sorry it saw had *already
   been fixed*; the laurent-tails finisher deferred to a "345-line incomplete Leray" that was
   677 lines and complete. The orchestrator caught both, but only because it tracked ground truth
   in-context.
3. **Blueprint DAG drift.** The blueprint had spurious edges (proper-map-degree "builds on
   monodromy"), missing edges (genus-headline needs proper-map-degree), and one genuinely
   missing unit (jacobian-functoriality — nobody owned building `pushforward`/`pullback` from a
   holomorphic map). Gap-analysis mandates in designer prompts caught these, but late.
4. **"Thin unit" predictions were sometimes wrong.** Riemann–Roch was frozen as "pure ℤ
   arithmetic" but actually needed the tail-χ ledger (a real six-term argument) because Čech-h¹
   and tail-h¹ are not known equal — an arithmetic subtlety the orchestrator caught by redoing
   the count by hand before launching the "thin" builder.
5. **Consolidation debt never paid.** Early parallel foundations proved duplicate bridge lemmas
   in `Compat` namespaces (`RS.LMCompat`, `RS.FormsCompat`); the planned dedupe pass never became
   priority. Harmless but untidy. Similarly, `AddCommGroup (Cech.H1 D)` was locally re-registered
   by two units before being fixed at one site.
6. **Token-expensive tails.** A few builds ran very long (Meromorphic 812k, Čech 906k, Abel
   fixer chains ~2M cumulative) — mostly *legitimate* difficulty, but some of it was agents
   grinding on elaboration walls that a mid-run consultation of the gotcha journal would have
   shortcut.
7. **One agent self-suspended** waiting on a background-build notification pattern that
   only fired late; the orchestrator couldn't message a running agent and had to wait it out.

## What I would do differently

1. **Continuous WIP commits from minute one** (a background auto-committer was added only after
   the first outage, then replaced by disciplined milestone commits — the discipline should have
   been the day-one default given interruption risk).
2. **A ground-truth facts board.** A single orchestrator-maintained `docs/STATUS.md` (what is
   proved, where, as of when) that every agent must read *last* before making routing decisions —
   eliminating the stale-state class of errors instead of catching them case by case.
3. **Interface acceptance spikes, not prose contracts.** Where two in-flight units share a
   boundary, a tiny compiled file asserting the exact expected signatures would catch drift
   mechanically; prose "frozen banks" worked but required orchestrator vigilance.
4. **Budget-boxed builders with mandatory handoff.** Cap a builder's run and make it write a
   continuation brief at the cap, rather than letting outages decide where handoffs happen.
5. **Trust the blueprint's warnings sooner.** The blueprint flagged the "Stokes-free Serre
   functional" circularity from the start; we still let the tail-comparison surjectivity be
   attempted/deferred twice before formally re-basing the architecture around it (which took
   one paragraph of arithmetic once done deliberately).
6. **Register shared instances upstream on first collision**, not after the second consumer
   hits the same wall.

## The one-line summary

Sixty-thousand-line clean-room formalizations are tractable when the mathematics is routed
correctly *in advance* (the blueprint's three routing decisions were worth more than any amount
of compute), designs are verified by compilation before building, gaps are loud and named rather
than silent, and every completion claim is re-verified by the orchestrator against the compiler
rather than taken from an agent's report.
