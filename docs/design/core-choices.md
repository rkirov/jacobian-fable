# Core definitional choices (FROZEN — units must not re-choose these)

Rationale in parentheses. Verified against `docs/mathlib-inventory.md` (pinned commit). If a choice
proves unworkable in practice, the discovering agent STOPS and reports back to the orchestrator
rather than silently deviating; changes here fan out everywhere.

## CC1 — Holomorphic 1-forms and `genus`  (owner: holomorphic-forms)

A holomorphic 1-form on `X` is a bundled analytic section of the Hom-bundle from the tangent
bundle to the trivial line bundle:

```lean
abbrev Form1 (X) [...] := Cₛ^ω⟮𝓘(ℂ); ℂ →L[ℂ] ℂ,
    fun x : X => TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial X ℂ x⟯
-- ContMDiffSection: instances AddCommGroup, Module ℂ exist (ContMDiffSection.lean:377,397);
-- ContMDiffVectorBundle ω for TangentSpace at IsManifold ω (Tangent.lean:336) and for Hom
-- bundles (Hom.lean:129) exist.
def genus (X) [...] : ℕ := Module.finrank ℂ (Form1 X)
```

- Provide chart-coefficient API: for a chart `e` and `ω : Form1 X`,
  `coeffIn e ω : ℂ → ℂ` (junk off `e.target`), with: `coeffIn` analytic on `e.target` iff ω is
  ω-smooth there; transition rule `coeffIn e' ω = (deriv τ) • (coeffIn e ω ∘ τ)` for the transition
  `τ = e ∘ e'.symm`; a form is determined by its coefficients; a constructor from compatible
  coefficient families. ALL downstream units use `coeffIn`, never raw bundle internals.
- `d : (X → ℂ) → Form1`-style: `mdifferential f` with `coeffIn e (mdifferential f) = deriv (f ∘ e.symm)`
  on targets, for ω-smooth f.
- Finiteness of `genus` (holomorphic-forms unit): norm `‖ω‖ := max over a fixed finite compact-
  exhausting chart family of sup of |coeffIn|`; Montel + Arzelà–Ascoli ⇒ compact unit ball ⇒
  finite-dimensional (Riesz, mathlib has `isCompact_closedBall_iff` route in
  `FiniteDimensional`); then `Module.finrank` is honest.

## CC2 — Divisors  (owner: meromorphic-and-divisors)

```lean
abbrev Divisor (X) [...] := Function.locallyFinsuppWithin (Set.univ : Set X) ℤ
```
(mathlib: lattice-ordered add. group, `finiteSupport` on compact spaces.) Degree
`Divisor.deg : Divisor X → ℤ` via `finsum`/`Finsupp` over the finite support. Point divisor
`Divisor.single P n`.

## CC3 — Meromorphic functions on X, `ℳ(X)`, and `L(D)`  (owner: meromorphic-and-divisors)

- Predicate: `MeromorphicAtX f x := MeromorphicAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)` for
  `f : X → ℂ`; `MeromorphicOnX f := ∀ x, MeromorphicAtX f x`. Prove chart-invariance (via z^k·unit
  factorization; small comp-lemmas may need to be added).
- Order: `ordAtX f x := meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) : WithTop ℤ`;
  chart-invariant.
- **`ℳ X` is a quotient** (junk-free; the blueprint's central hazard):
  `ℳ X := {f // MeromorphicOnX f} ⧸ (fun f g => f =ᶠ[Filter.codiscrete X] g)`.
  Field structure (on connected compact X), `ord`, `div : ℳ X → Divisor X` (well-defined on the
  quotient; support finite by compactness + identity theorem), evaluation germ at regular points,
  `holoRepr`: every class with `div ≥ 0` everywhere locally has an honest analytic representative
  (via mathlib `MeromorphicNFAt`/`toMeromorphicNFOn` repair).
- `L(D) := {f : ℳ X // f = 0 ∨ div f ≥ -D}` as a ℂ-submodule; `l D := Module.finrank ℂ (L D)`.

## CC4 — Local multiplicity of holomorphic maps  (owner: local-multiplicity)

For `F : X → Y` holomorphic, `x : X`: transport through charts and use mathlib's
`analyticOrderAt (chartAt (F x) ∘ F ∘ (chartAt x).symm - chartAt (F x) (F x)) (chartAt x x) : ℕ∞`.
`multiplicity F x : ℕ` := that order when finite (F nonconstant near x), junk 0 else, plus the
`z^k · unit` normal form both ways and chart-invariance. Ramified ⟺ mult ≥ 2.

## CC5 — The projective line  (owner: projective-line)

`ℙ¹ := OnePoint ℂ` (mathlib has topology: compact, T2, connected). Charts: identity on ℂ and
`z ↦ 1/z` on `(ℂ \ {0}) ∪ {∞}`; `ChartedSpace ℂ (OnePoint ℂ)`, `IsManifold 𝓘(ℂ) ω`. Meromorphic
`f` on X induces holomorphic `X → ℙ¹` (poles ↦ ∞) — the bridge lemma both headline and degree use.
Homeomorphism `ℙ¹ ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1` via inverse stereographic
(mathlib `stereographic'` charts on the sphere).

## CC6 — Integration of holomorphic 1-forms along paths  (owner: paths-and-integrals)

NO measure-theoretic integration on X. For continuous `γ : [0,1] → X` and `ω : Form1 X`:
a **primitive along γ** is `F : [0,1] → ℂ` such that near each `t`, `F = (local primitive of
coeffIn in a chart around γ t) ∘ chart ∘ γ`. Local primitives on chart disks exist by power-series
antiderivative (planar; check mathlib for an existing disk-primitive; else prove via
`FormalMultilinearSeries` integration or `Complex` primitives on convex/star domains).
`∫γ ω := F 1 - F 0` (exists by Lebesgue-number chain continuation; unique up to constant).
API: concatenation, reversal, ℂ-linearity in ω, chart-local computation
(`= intervalIntegral (coeff ∘ chart∘γ) · (chart∘γ)'` for C¹ pieces inside one chart — bridge to
mathlib `circleIntegral`/`curveIntegral` for residue computations), invariance under
reparametrization, **homotopy invariance** (grid/monodromy argument; mathlib
`IsCoveringMap`/homotopy-lifting may be used or hand-rolled grid) — homotopy invariance may also
land in the monodromy unit; coordinate.
Periods: `period γ ω` for loops; the period homomorphism `H := π₁ or loops → (Form1 X →ₗ ℂ)`.

## CC7 — The ℝ-manifold bridge  (owner: surfaces-and-charts)

Provide once: `instance : IsManifold 𝓘(ℝ, ℂ) ∞ X` (and ω) derived from `IsManifold 𝓘(ℂ) ω X`
(ℂ-analytic transitions are ℝ-analytic/smooth; `AnalyticOn.restrictScalars` + `contDiffOn` bridge).
Pin the definitional facts: `(extChartAt 𝓘(ℝ,ℂ) x : X → ℂ) = extChartAt 𝓘(ℂ) x` (should be `rfl` —
verify!), and `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x ↔ AnalyticAt ℂ (f-in-charts) (chart x)` bridge lemmas
(mathlib `ContDiffAt ℂ ω ↔ AnalyticAt` exists on the model). This unlocks
`SmoothPartitionOfUnity` on X (via ∞) for the PoU-based units. Also: holomorphic
(`ContMDiff 𝓘(ℂ) ω`) ⇒ `ContMDiff 𝓘(ℝ,ℂ) ∞` restriction lemma.

## CC8 — Čech H¹ and the tail model  (owners: cech-cohomology / laurent-tails; semi-frozen)

Guidance, final shape fixed by the cech design doc with orchestrator sign-off:
- Cochains are **germ-valued over codiscrete filters** (junk-free): a 1-cochain on cover `U i`
  assigns to `(i,j)` an element of the `ℳ`-germ space on `U i ∩ U j` with `div ≥ -D` off a
  codiscrete set... concretely the same subtype/quotient pattern as CC3 relativized to opens.
- `H¹(D)` as the directed colimit over finite chart-disk covers under refinement (mathlib
  `Module.DirectLimit`), OR cover-relative with a Leray theorem — designer picks after a spike,
  bias: colimit.
- `H⁰(D) = L(D)` must hold definitionally-easily.
- Miranda tail space `T[D] := ⨁_p (principal tails at p bounded by D)`; truncation
  `α_D : ℳ X → T[D]`; the comparison `H¹(D) ≅ T[D]/im α_D` is the laurent-tails unit's main
  deliverable (Miranda VI pp. 186–188 = PDF 198–200).

## CC9 — The Jacobian type  (owner: jacobian-construction)

`Jacobian X := (Fin (genus X) → ℂ) ⧸ (AddSubgroup of periods)` — the ℤ-span of
`{periodVector γ | γ loop}` w.r.t. a fixed basis of `Form1 X` (choice via `Module.finBasis`).
Quotient group + topology from mathlib; T2/compact/manifold/Lie instances arrive only after
period-lattice-rank proves `IsZLattice`. Structure the files so the *type and group/topology*
exist early (they don't need full rank), and the instances that need full rank are added late.
Note: `ofCurve P Q := (path integrals from P to Q of the basis forms) mod periods` — well-defined
by homotopy invariance + connectedness (path choice differences are loops).

## Cross-cutting

- Sorries: allowed only during development. `axiom`/`native_decide`/vacuous instances: never.
- Every unit: targeted imports; ≤1 lake job at a time; check with `scripts/check.sh`.
- When mathlib lacks a planar lemma (residue of 1/z, Laurent coefficients, etc.) put it in the
  unit the blueprint assigns, not wherever convenient; check `docs/requests/` first — someone may
  have already asked for it.
