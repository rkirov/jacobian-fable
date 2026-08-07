# Jacobians of compact Riemann surfaces, in Lean 4

A complete, from-scratch formalization answering [Kevin Buzzard's "Jacobians" AI challenge
(v0.4)](https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9): build a working API
for the Jacobian of a compact Riemann surface over current Mathlib — no future algebraic
geometry, no scheme theory, no abstract sheaf-cohomology library.

**Status: complete.** Every declaration of the challenge gist is provided with **zero `sorry`s**
and no axioms beyond Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). The
library is also pooled as [`LeanPool/JacobianDiffgeo`](https://github.com/Vilin97/lean-pool/tree/main/LeanPool/JacobianDiffgeo)
in [Lean Pool](https://github.com/Vilin97/lean-pool) (merged in
[#334](https://github.com/Vilin97/lean-pool/pull/334)); see [`POOL.md`](POOL.md).

## The challenge API, as delivered

For `X` a compact connected Riemann surface (`[ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]` + T2,
compact, connected):

| Gist item | Delivered |
|---|---|
| `genus X : ℕ` | dimension of the space of global holomorphic 1-forms (`Jacobian/Forms/`) |
| `genus_eq_zero_iff_homeo` | `genus X = 0 ↔ X ≃ₜ S²` — the headline (`Jacobian/GenusSphereHeadline/`) |
| `Jacobian X : Type u` | `ℂ^g / Λ`, Λ the period lattice (`Jacobian/JacobianConstruction/`) |
| 7 instances on `Jacobian X` | `AddCommGroup`, `TopologicalSpace`, `T2Space`, `CompactSpace`, `ChartedSpace (Fin g → ℂ)`, `IsManifold ω`, `LieAddGroup` — all fire by `inferInstance` |
| `Jacobian.ofCurve` | the Abel–Jacobi map, with `ofCurve_self` and `ofCurve_contMDiff` |
| `Jacobian.ofCurve_inj` | injectivity for `0 < genus X` (Abel's theorem, `Jacobian/CechCount/Final.lean`) |
| `Jacobian.pushforward` / `pullback` | `→ₜ+` maps with holomorphy, id/comp laws (`Jacobian/JacFunctorial/` + `Jacobian/Challenge.lean`) |
| `pushforward_pullback` | `= ContMDiff.degree f hf • P` (projection formula) |
| `ContMDiff.degree` | mapping degree, `0` for constant maps (`Jacobian/ProperDegree/`) |

Entry points:
- **`Jacobian/Challenge.lean`** — the assembled API with an item-by-item provenance map and a
  self-auditing `GistCheck` section (one witness per gist item).
- **`GistAcceptance.lean`** — the acceptance test: the gist's 24 statements verbatim, each proved
  by the providing declaration, plus `#print axioms` on the six main items.

Two documented deviations from the gist's literal text, both cosmetic: the functorial
declarations put `X Y Z` in one shared `universe u` (independent universes send the
`ULift`/quotient elaborator into a verified timeout), and `ofCurve_contMDiff` carries one
auto-discharged instance-implicit argument.

## Building

```bash
lake exe cache get   # mathlib olean cache (pinned commit below)
lake build           # full project, ~3300 jobs
lake env lean GistAcceptance.lean   # acceptance test
scripts/check.sh Jacobian/<Unit>    # per-unit: builds + sorry sweep
```

Pinned toolchain: `leanprover/lean4:v4.33.0-rc2`; mathlib at
`51e6992efd06126df61a496bebf8f49482a4e129`. The gist itself specifies `v4.30.0-rc2` / mathlib
`5483982`; the development was forward-ported off that pin (v4.30.0-rc2 → v4.32.2 → v4.33.0-rc1 →
v4.33.0-rc2) with all challenge statements unchanged. The `lean-eval` branch stays at `v4.32.2` /
mathlib `905b9581`, the pin that submission was made against.

## Architecture

The development follows `clean_room_blueprint.md` (~30 units in a dependency DAG), whose three
routing decisions all proved out:

1. **Serre duality via Laurent tails (Miranda VI.3), never Hodge symmetry.** The pairing is
   purely algebraic (`resAt`-against-tails); surjectivity is Miranda's Lemma 3.4/3.6 counting
   (`Jacobian/TailDuality/`). No harmonic theory anywhere.
2. **The residue *theorem* is separate from the residue *functional*.** `∑ Res = 0` goes through
   the trace to ℙ¹ plus partial fractions (`Jacobian/ResidueTheorem/`); the one honest
   integration atom (an area pairing built from planar Stokes + partitions of unity,
   `Jacobian/Abel/AreaPairing.lean`) is paid exactly once, for Abel.
3. **Cohomology-first, PDE-light.** Čech `H¹(D)` is a directed colimit over finite covers
   (`Jacobian/Cech/`); finiteness is Schwartz's compact-perturbation argument with Montel as the
   only functional-analytic input (`Jacobian/Finiteness/`); the only PDE solved is ∂̄ on a disk
   via the Cauchy transform, with Cauchy–Pompeiu proved by polar coordinates and 1-D FTC — no
   two-dimensional Stokes theorem is ever used for it (`Jacobian/Dbar/`).

The endgame reduction: after everything else was built, the entire challenge hinged on one
dimension count, `dim H¹(X, 𝒪) ≤ g`, closed by transposing Forster's §17.8–17.9 multiplication
trick onto the Čech colimit (`Jacobian/CechCount/`). That single theorem unconditionally
discharged Abel's injectivity, the period lattice's discreteness, and thereby all manifold/
compactness instances on the Jacobian.

## Repository layout

| Unit (`Jacobian/…`) | Lines | Provides |
|---|---|---|
| `Surface/` | 795 | chart bridges, ℝ/ℂ manifold bridge, identity theorem, holomorphic IFT |
| `LocalMultiplicity/` | 1214 | `z^k·unit` normal forms, multiplicity, adapted charts |
| `Forms/` | 1567 | holomorphic 1-forms, **`genus`**, Montel, finite-dimensionality |
| `MappingDegree/` | 1009 | branched-cover degree, regular values, degree-1 ⇒ homeomorphism |
| `Path/` | 1923 | path integrals via primitives, homotopy invariance, periods, loop perturbation |
| `ResidueCalculus/` | 1895 | Laurent coefficients, residues, change of variables (algebraic) |
| `JacobianConstruction/` | 1308 | **`Jacobian`** type, torus instances, `ofCurve` |
| `ProjectiveLine/` | 724 | `ℙ¹ = OnePoint ℂ` as a Riemann surface, `≃ₜ S²`, genus 0 |
| `Meromorphic/` | 1874 | germ-quotient field `ℳ(X)`, divisors, `L(D)` |
| `MeromorphicTrace/` | 1623 | fibre traces, **argument principle** (`deg∘div = 0`) |
| `SphereTopology/` | 315 | S² simply connected (no van Kampen), backward headline |
| `Cech/` | 3380 | Čech `H¹(D)` colimit, refinement independence, six-term fragment |
| `FormTrace/` | 630 | pair-form traces, residue–trace compatibility (Miranda 3.2) |
| `Dbar/` | 2607 | Wirtinger calculus, Cauchy transform, **∂̄ solvability** (Forster 13.2) |
| `DolbeaultComparison/` | 1862 | Leray theorem, `H¹ ≅ H^{0,1}` (PDE-free) |
| `PlanarStokes/` | 1176 | compact-support Stokes, smeared residue theorem |
| `Finiteness/` | 1964 | **`dim H¹(D) < ∞`** (Schwartz + Montel), χ ledger |
| `CanonicalForms/` | 2085 | meromorphic 1-forms, canonical divisor `K`, existence theorems |
| `LaurentTail/` | 1976 | tail spaces `T[D]`, tail-`H¹`, comparison into Čech |
| `Monodromy/` | 390 | log branches along pole-avoiding paths |
| `ResidueTheorem/` | 1578 | **`∑ Res = 0`** (unconditional) |
| `SerrePairing/` | 474 | algebraic Serre pairing, injectivity core |
| `AbelWeak/` | 1559 | Forster §20 weak solutions, k-point layer |
| `ProperDegree/` | 234 | **`ContMDiff.degree`**, `deg(div f) = 0`, genus-0 finisher |
| `TailDuality/` | 1683 | **Serre duality** `l(K−D) = h¹(D)` (Miranda 3.4/3.6), tail-χ ledger |
| `H1Genus/` | 41 | `dim H¹(0) = genus` |
| `RiemannRoch/` | 75 | **`l(D) − l(K−D) = deg D + 1 − g`**, `deg K = 2g−2` |
| `Abel/` | 3855 | **Abel's theorem**, area pairing, Serre functional, `ofCurve_inj` engine |
| `GenusSphereHeadline/` | 119 | **the headline** `genus = 0 ↔ ≃ₜ S²` |
| `PeriodLattice/` | 1105 | Λ discrete, rank 2g, `IsZLattice` — instance discharge |
| `CechCount/` | 692 | the final count `h¹(0) ≤ g`; all gates closed |
| `JacFunctorial/` | 2618 | form pullback/trace, `pushforward`/`pullback`, projection formula |

**Total: 46,692 lines of Lean across 212 files.**

Supporting material: `clean_room_blueprint.md` (the roadmap), `CONVENTIONS.md` (build rules),
`docs/design/` (29 spike-verified design documents), `docs/mathlib-inventory.md`,
`docs/build-log.md` (per-file build journal with Lean gotchas), `docs/refs/` (page maps for the
reference texts: Forster GTM 81, Miranda GSM 5).

## Provenance

Built clean-room by Claude (Fable 5) orchestrating ~70 specialized design/build/fix agents over
the blueprint's DAG: only this repository, the two reference PDFs, and the pinned mathlib source
were consulted. See `RETRO.md` for a post-mortem.
