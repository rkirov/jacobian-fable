# jacobian-fable vs jacobian-claude: a clean-room reconstruction meets its source

[`rkirov/jacobian-claude`](https://github.com/rkirov/jacobian-claude) ("**JC**") is the original
solution to Buzzard's Jacobian challenge, built exploratively over two months. Its final commit
added a "clean-room blueprint" — a mathematics-only distillation of what it had learned. This
repository ("**JF**", jacobian-fable) was then built *from that blueprint alone*, clean-room:
no access to JC's code, only the blueprint, the textbooks (Forster, Miranda), and pinned mathlib.
The comparison below therefore measures two things at once: how the two formalizations differ,
and **what a distilled roadmap is worth** — with the caveat that JC paid the full price of
exploration and JF inherited the map, so nothing here is a like-for-like capability comparison.

## Headline numbers

| | JC (source) | JF (clean room) |
|---|---|---|
| Lean code | 72,403 lines / 251 files (peak ~111k before 9 pruning rounds) | 46,692 lines / 212 files (no pruning phase; no dead code accumulated) |
| Units | 30 | 32 (blueprint's 30 + jacobian-functoriality gap + CechCount) |
| Wall clock | ~22 working days (Apr 19 – Jun 13) | ~3 working days of compute (Jul 2, Jul 6–7), interrupted by quota outages |
| Commits | 1,462 | ~95 |
| Process | Dozens of interactive-autonomous sessions; ~30 human redirects; lean-lsp MCP; models Opus 4.7 → 4.8 → (2-day GPT-5.5 Codex detour) → Fable 5 endgame | Fully autonomous orchestrator + ~70 design/build/fix agents; spike-verified design docs; zero human mathematical input; Sonnet builders, Fable designs/finishers |
| Ported code | ~3.1% (Brsanch degree/fibre theory, tangentstorm Green's theorem) | none |
| Axioms | `propext, Classical.choice, Quot.sound` only (AuditAll.lean) | identical (GistAcceptance.lean) |
| Verification | real leanprover/comparator, CI, lean-eval leaderboard | same (harness pattern adapted from JC, post-clean-room) |
| Mathlib pin | v4.30.0 / `c5ea003` | v4.30.0-rc2 / `5483982` (main); v4.32.0-rc1 / `360da6fa` (lean-eval) |

Same-unit weight extremes (lines, JC → JF): Finiteness 9,752 → 1,964 · MappingDegree+ProperDegree
12,263 → 1,243 · MeromorphicTrace 5,823 → 1,623 · Path 4,595 → 1,923 — versus Čech 1,742 → 3,380
and ResidueCalculus 572 → 1,895, where JF deliberately invested more (see below).

## Where the two agree (mostly by design — the blueprint froze JC's wins)

- **`genus`**: byte-for-byte the same idea — bundled `ContMDiffSection` of the Hom-bundle
  `TangentSpace →L[ℂ] Trivial ℂ`, `genus := finrank ℂ`, finiteness via a hand-built Montel /
  Arzelà–Ascoli argument closed by Riesz.
- **ℙ¹** = `OnePoint ℂ` with identity/inversion charts; the challenge-typed sphere homeo via
  mathlib's `onePointEquivSphereOfFinrankEq`; genus 0 by Liouville on the two-chart atlas.
- **`Jacobian X`** = `ULift.{u}` of a `Type 0` torus `(Fin g → ℂ) ⧸ periods`, with a hand-built
  ULift-manifold transport kit in both (mathlib has none), and quotient charts via local
  homeomorphism sections.
- **Serre duality via Miranda's Laurent tails**, never Hodge theory; ∂̄ on disks via the Cauchy
  transform + Forster 13.2 exhaustion; smooth `(0,1)`-data + partitions of unity as the only
  global analytic glue.
- **Period-lattice discreteness**: Forster 21.3/21.4(a) — generic base points, local Jacobi map
  + IFT, Abel engine, residue-theorem contradiction. Structurally the same proof.
- **Period-lattice nondegeneracy**: both use a **maximum-principle / open-mapping** argument on
  the real part of a period primitive. Notably, the blueprint's own hint here ("cut-surface +
  Green's-theorem flavor") matches *neither* repo — both discovered the max-principle route.
- **Abel hard direction**: both pair the weak solution's global ∂̄-datum against holomorphic
  forms and win by a dimension count (Forster 19.10 flavor), then repair `e^{-u}·G` to a genuine
  meromorphic function via Wirtinger/CR.

## Where they genuinely diverge

**Čech H¹.** JC fixes one finite cover, proves refinement maps, choice-independence (an explicit
prism/simplicial homotopy operator), injectivity and a Leray isomorphism by hand, with
`IsLeray := every piece simply connected`. JF builds `H¹(D)` as a **directed colimit** over a
small type of finite covers (blueprint CC8), with the same Forster 12.3/12.4 content plus a
window/skyscraper six-term fragment used later by the χ ledger. JF's Čech is ~2× bigger; it buys
a cover-free H¹ object every downstream unit can cite.

**Finiteness (5× size difference).** JC hand-built two full engines: a `BddHol` Banach/Montel/
Schwartz stack (with its own open-mapping iteration and δ-net argument) *and* a skyscraper/snake
induction with an abstract two-step snake lemma — ~9.7k lines, including a 1.8k-line single file.
JF, knowing from the blueprint exactly which statement matters, collapsed Schwartz to **one
abstract Banach cospan lemma** (`u` surjective + `v` compact ⇒ finite-codimensional complement,
proved by mirroring mathlib's `exists_preimage_norm_le`) and reused the Čech unit's six-term
fragment for the χ ledger — 1,964 lines.

**The h¹ = g anchor — same obstruction, two different escapes.** Both repos hit the same wall
the blueprint's routing note #2 hints at: the tail-H¹ → Čech-H¹ comparison surjectivity is
Cousin-I, essentially circular with Serre duality. **Neither repo proves it.** JC's Čech-level
residue-pairing scaffolding survives as explicitly dead code ("deliberately no
`exists_serreDualityData`"); its actual anchor picks a large effective divisor `A` where *both*
h¹'s vanish (Čech side by a cup-product kill lemma, tail side by `deg(K−A)<0`) and subtracts the
two independent Riemann–Roch identities to equate `h¹_Čech(0) = h¹_tail(0) = g`. JF instead
proved `h¹_Čech(0) ≤ g` **directly** — transposing Forster 17.8/17.9's multiplication trick onto
the colimit (`mulH1` surjective for `f ≠ 0`, constant `h¹(nP)` for large `n`, growth
contradiction) — which makes the tail injection an isomorphism at `D = 0` by dimension and
unconditionally discharges Abel and all torus instances. Two genuinely different counting
endgames for the same theorem; JF's yields the comparison iso at `D = 0` as a corollary, JC's
never needs it.

**The residue theorem — JF completed the route JC abandoned.** JC proved `∑Res = 0` by an
802-line partition-of-unity + planar-Stokes ledger directly on `X` (with `|T′|²` change-of-
variables transport), after starting — and leaving visibly unfinished — a trace-to-ℙ¹ route in
`MeromorphicTrace.lean` (its header names theorems that exist nowhere; the residue–trace
compatibility "Lemma 3.2" was never assembled, and a comment calls the missing contour
change-of-variables "a statement Mathlib lacks"). JF took exactly that abandoned route to
completion: an **algebraic** residue calculus (Laurent coefficients from `dslope` normal forms,
chart change-of-variables reduced to three monomial cases — no contours), the residue–trace
compatibility proved with an explicit calibration hypothesis (found *false* without it), and the
ℙ¹ base case by partial fractions. JC's planar-Stokes atoms have a JF counterpart too, but they
serve only Abel, not the residue theorem.

**Residues themselves.** JC defines `resAt` as a limit of circle integrals and deliberately
avoids ever proving chart-independence (everything is computed in one canonical chart). JF
defines Laurent coefficients algebraically and proves the change-of-variables theorem — 572 vs
1,895 lines, and JF's choice is what makes its trace-route residue theorem and tail pairing
purely algebraic.

**Mapping degree (10× size difference).** JC's well-definedness goes through fibre-counts
locally constant off a finite critical set plus path-connectedness of complements of finite sets
— the route the blueprint itself flags as "most of the work" — across 48 agent-decomposed files
plus a large ported ProperDegree layer. JF's `FiberStack` argument proves the *total
multiplicity* fibre sum locally constant at **every** point (branch points included), so no
punctured-connectivity theory is needed at all: 1,009 + 234 lines.

**Path integrals.** JC integrates honestly (`intervalIntegral` of the pulled-back speed) and
keeps a separate integration-free "monodromy chain" engine for the genus-0 direction. JF has no
measure theory on `X` anywhere: the path integral *is* the endpoint difference of a
primitive-along-path (blueprint CC6), with homotopy invariance by a 2-D grid argument; the same
machinery then serves monodromy, Abel and the sphere unit.

**S² simple connectivity.** JC built a two-open van Kampen theorem from scratch (427 lines of
Lebesgue subdivision, spokes and groupoid telescoping). JF avoided van Kampen entirely: perturb
a loop off `{∞}` (a lemma it needed for Abel anyway) and contract in the remaining chart.

**Meromorphic functions.** JC keeps raw functions (`toFun` + meromorphy predicate) and quotients
junk *only at the `L(D)` level* (`lDim := finrank (L(D) ⧸ germ-zero)`), with a `holoRepr` repair
used where values matter. JF bakes the quotient into the base type: `ℳ(X)` is a subalgebra of
`Filter.Germ (codiscrete X) ℂ`, a genuine field, with `ord`/`divisor`/`evalAt` well-defined on
classes. The blueprint's "junk-free from the start" hazard note — clearly distilled from JC's
experience — pushed JF further than JC itself went.

**Meromorphic 1-forms — the same trap, sprung twice.** JC represents them as cotangent sections
with a meromorphic-coefficient predicate (raw, junk handled ad hoc); JF first built raw
chart-coefficient families, **independently rediscovered that raw representations make
"ord = ⊤ everywhere ⇒ 0" false**, and rebuilt as a germ-quotient mid-project. The hazard is
evidently intrinsic to the object, not an accident of either codebase.

**Functoriality.** Both hit the identical "genuine analytic crux" (JC's own inline words): the
trace of a holomorphic form must be extended across branch points. JC extends by local
boundedness in the `wᵉ` normal form and pushes lattice-preservation through monodromy lift
families; JF extends by meromorphic normal-form repair (`toMeromorphicNFAt`) and gets
lattice-mapping from loop perturbation off the branch locus. JC never separated this into a
unit (it lives inside MeromorphicTrace/JacobianConstruction); JF's design phase flagged it as a
missing blueprint unit and built `JacFunctorial` — including the cross-universe layer both
submissions independently needed.

**Jacobian quotient subtlety.** JC quotients by the *raw* period subgroup and proves
discreteness before any instance needs it (sequential development could afford to wait). JF
quotients by the **topological closure** so `T2Space` holds unconditionally on day one and the
manifold/compactness instances ship as theorems gated on typeclass hypotheses — a concession to
massively parallel development, discharged at the end when discreteness lands (`closure Λ = Λ`).

**Dolbeault comparison.** JC proves only an ℝ-linear statement
(`finrank ℝ H^{0,1} = 2·finrank ℂ H¹_Čech(𝒪)` — a documented `Module ℂ` limitation on sections),
which is exactly what its Abel dimension count needs. JF proves the ℂ-linear equivalence
`H¹_Čech(𝒪) ≃ₗ[ℂ] H^{0,1}` at `D = 0`, plus the Leray/trade lemmas that feed finiteness.

## The submission harness

Both repos discharge the gist and the lean-eval problem the same way — because JF adapted JC's
proven pattern (with authorization, after the clean-room phase ended): an in-repo `comparator/`
replica of the lean-eval workspace with verbatim trusted files, `verify.sh` running the real
comparator/lean4export/landrun stack, an overlay generator, and CI. Both shims independently hit
the same two harness-forced tricks: `@[implemented_by]` runtime stubs for noncomputable data
holes behind the trusted plain-`def` bridge, and a `degree` with hand-pinned minimal binders
(Lean's body-driven variable inclusion otherwise leaks instance arguments the sorried Challenge
version doesn't have).

## What the blueprint was worth — and where it was imperfect

The blueprint bought roughly a **7× wall-clock** and **1.55× code-size** reduction with zero
pruning debt, chiefly by freezing the winning representations up front (genus, ℙ¹, torus, tails)
and by its three routing warnings (no Hodge; residue theorem ≠ residue functional; Čech-first,
PDE-light), each of which demonstrably saved JF from walls JC had already paid for.

It was not gospel. Its DAG had a spurious edge (proper-map-degree "builds on monodromy") and a
genuinely missing unit (Jacobian functoriality); its §21 nondegeneracy hint names a route
neither repo used; its own source never took the colimit H¹, germ-quotient `ℳ(X)`, or
primitive-based integration that the blueprint (rightly, it turned out) recommended. And the
deepest hazards — meromorphic-form junk, the Cousin circularity, the branch-extension crux —
were rediscovered independently on the clean side, which is decent evidence they are properties
of the mathematics rather than of any one attempt.

*Written by the JF orchestrator from a five-agent structured read of JC at commit `main`
(2026-07); JC facts verified against its sources, JF facts from its own build records
(`docs/build-log.md`, `RETRO.md`).*
