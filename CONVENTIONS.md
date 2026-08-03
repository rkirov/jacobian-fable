# Project conventions (binding for every unit builder)

Goal: fill in Buzzard's Jacobian challenge v0.4 (see `docs/Jacobian_challenge.lean` for the target
API) over mathlib pinned at `905b95818eb32af7874a58b427f50c1711a5e96c` (tag `v4.32.2`; the gist's
original pin was `548398201a64f3a5127d90d83945278cfe38cac4`), following
`clean_room_blueprint.md`. ~30 units, each a directory under `Jacobian/`.

## Hard rules

1. **Read scope**: you may read ONLY files under `/home/rado/jacobian-fable` (including
   `.lake/packages/mathlib` sources and the reference PDFs in the project root). Never read other
   directories on disk, never fetch solutions from the internet. Mathlib docs pages are OK only for
   API lookup; textbook PDFs in this folder are the mathematical references.
2. **Machine limits**: 4 cores, 7 GB RAM. NEVER run two `lake build`/`lean` jobs yourself in
   parallel; never `import Mathlib` (the monolith) in project files — use targeted
   `import Mathlib.Foo.Bar` lines only. (Exception: the final `Jacobian/Challenge.lean` assembly.)
3. **No cheating**: no `axiom`, no `native_decide`, no `unsafe`, no `partial def` for logic-bearing
   definitions, no `@[implemented_by]`, no vacuous instances (e.g. defining `Jacobian X := Unit`).
   Junk-value hacks that make statements vacuously true are forbidden — the definitions must mean
   the mathematics. `sorry` is allowed *during* development only; a unit is DONE only when its files
   have zero sorries and `lake build Jacobian.<UnitRoot>` succeeds.
4. **Don't break other units**: you may read all project files but edit only your unit's directory
   (plus registering your unit's root import in `Jacobian.lean`) unless your task explicitly says
   otherwise. If you need an upstream lemma that doesn't exist, add it to
   `docs/requests/<upstream-unit>.md` and (if trivial) prove it locally in your unit in a clearly
   marked `Compat` section for later upstreaming.
5. **Verification**: `scripts/check.sh <ModulePath>` (e.g. `scripts/check.sh Jacobian/Cech`) must
   pass: builds the unit and greps for sorries. Run it before declaring anything done. Report
   results honestly.

## Style

- Lean 4 / current mathlib style: `theorem foo_bar (h : P) : Q`, naming per mathlib conventions
  (snake_case theorems, UpperCamelCase types/structures, dot-notation lemma names like
  `Foo.bar_of_baz`).
- Root namespace for the development: `RS` (Riemann Surfaces). Final challenge API lands at root
  level / `Jacobian` namespace exactly as the gist demands.
- The standing surface variables (copy verbatim where needed):
  ```lean
  open scoped ContDiff Manifold
  variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  ```
  Drop `[CompactSpace X]`/`[ConnectedSpace X]` in lemmas that don't need them when it is free to do
  so; don't chase maximal generality otherwise.
- Every file starts with a module docstring stating what it provides and which blueprint unit it
  belongs to. Keep files under ~800 lines; split when larger.
- Identifier gotchas: `ω` is the ContDiff-scope smoothness token and `∞` the OnePoint/ContDiff
  token — neither is usable as an identifier (use `θ`, `η`, `hFinf`, …). `σ` clashes with scoped
  `unitInterval.symm`.
- Prefer mathlib's existing machinery (see `docs/mathlib-inventory.md`) over hand-rolling:
  `MeromorphicAt/On`, `meromorphicOrderAt`, `Function.locallyFinsuppWithin` divisors,
  `AnalyticAt`, `ZLattice`, `SmoothPartitionOfUnity`, `IsCompactOperator`, etc.
- `codiscreteWithin`-germ representations for meromorphic objects/L(D) (junk-free; see blueprint
  hazards). The three load-bearing definitional choices (genus, L(D), multiplicity) are frozen in
  `docs/design/` — do not re-choose them locally.

## Workflow per unit

1. Read your unit's design doc `docs/design/<unit>.md`, the blueprint section, and the cited
   textbook pages (PDF page maps in `docs/refs/`).
2. Read the API summaries (top-of-file docstrings) of your dependency units.
3. Write the unit in small files; compile early and often with
   `lake env lean Jacobian/<Unit>/<File>.lean` (fast, no full build) or `scripts/check.sh`.
4. Zero sorries; then update `Jacobian.lean` to import your unit root, run `scripts/check.sh`,
   and commit: `git add -A && git commit -m "<unit>: <summary>"`.
5. Write a 5-15 line API summary as the module docstring of your unit root file
   `Jacobian/<UnitRoot>.lean` — downstream units read these first.

## Where things are

- Challenge target: `docs/Jacobian_challenge.lean` (v0.4, verbatim from the gist).
- Blueprint: `clean_room_blueprint.md` (unit descriptions, dependency DAG, routing warnings).
- Reference page maps: `docs/refs/forster-map.md`, `docs/refs/miranda-map.md`.
- Mathlib inventory: `docs/mathlib-inventory.md`.
- Design docs (frozen interfaces & proofs-on-paper): `docs/design/<unit>.md`.
- Textbooks (PDFs, read with the Read tool + `pages`): Forster GTM81, Miranda GSM5,
  Griffiths–Harris (background only — do NOT follow its Hodge-theoretic route).
