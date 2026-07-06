# Design: period-lattice-rank (`Jacobian/PeriodLattice/`)

Blueprint unit **period-lattice-rank** (the final deep analytic unit). Blueprint text: "The period
lattice has a **real basis of rank `2g`** (Forster 21.3–21.4, dissection-free): discreteness via
the local Jacobi map, nondegeneracy, and the real basis — completing the `Jacobian = ℂ^g/Λ` torus.
… ⚠ Cheapest formal path is the **Riemann cut-surface + Green's-theorem** flavor of period
nondegeneracy, **not** Hodge / de Rham." Declared **Builds on:** abel-theorem.

References read IN FULL from the PDFs: Forster §21 (book 166–175 = PDF 172–181: 21.1–21.9),
Forster §19 (book 153–159 = PDF 159–165: 19.1–19.14, because 21.4(c) cites Corollary 19.8),
Forster §20 openings (PDF 165–166, for the Abel citation's exact shape). Page rule: PDF = book + 6.

One gated end spike (`scratch_plr.lean`, project root) compiled clean — results in §11.

Deliverable of this unit, in one sentence: the **two instances** that fire every gated instance in
`Jacobian/JacobianConstruction/Basic.lean`'s ledger (`ChartedSpace`/`IsManifold`/`LieAddGroup`/
`CompactSpace (Jacobian X)` in `docs/Jacobian_challenge.lean:78-89`):

```lean
instance : DiscreteTopology (RS.periodSubgroup X).topologicalClosure
instance : IsZLattice ℝ (RS.periodSubgroup X).topologicalClosure.toIntSubmodule
```

---

## 0. Mandatory reading, digested; verified project state

- `CONVENTIONS.md`: RS namespace, standing surface variables, junk-free representations, Compat
  sections + `docs/requests/` for missing upstream lemmas, ≤1 lean job, `scripts/check.sh`.
- `docs/design/core-choices.md` **CC9**: `Jacobian X := (Fin (genus X) → ℂ) ⧸ Λ`; instances that
  need full rank are added late by *this* unit. Owner jacobian-construction; CC9 is frozen — this
  unit adds instances, it does not re-choose anything.
- **`Jacobian/JacobianConstruction/` (BUILT, read: root, `Torus.lean`, `Basic.lean`,
  `Periods.lean`)**. Ground truth consumed here:
  * `RS.basis X : Basis (Fin (genus X)) ℂ (Form1 X)` := `Module.finBasis` (`Periods.lean:36`);
  * `RS.periodSubgroup X : AddSubgroup (Fin (genus X) → ℂ)` :=
    `AddSubgroup.closure (Set.range fun γ : Path P₀ P₀ => periodVector (basis X) γ)` with
    `P₀ := Classical.arbitrary X` (`Periods.lean:40`);
  * the gated instances (`Basic.lean:104-121`) keyed EXACTLY on
    `[DiscreteTopology (RS.periodSubgroup X).topologicalClosure]` and
    `[IsZLattice ℝ (RS.periodSubgroup X).topologicalClosure.toIntSubmodule]`;
  * the bridge instance `RS.discreteTopology_toIntSubmodule` (`Basic.lean:60`) — so once *this*
    unit registers discreteness of the closure, the `[DiscreteTopology …toIntSubmodule]` argument
    of the `IsZLattice` class elaborates by instance search alone;
  * root-level Compat instances `LocPathConnectedSpace X`, `PathConnectedSpace X`
    (`OfCurve.lean:36-39`) — reused by nondegeneracy's primitive construction.
- **`Jacobian/Path/` (BUILT, root + `Periods.lean`, `Planar.lean`, `LocalPrimitive.lean`,
  `Continuation.lean` read)**: `pathIntegral`, `pathIntegral_trans/symm/refl`, linearity
  (`pathIntegralₗ : Form1 X →ₗ[ℂ] ℂ`), `period`, `periodVector` (+ `_trans/_symm/_refl`),
  `RS.exists_hasDerivAt_ball` (planar primitive with prescribed value, `Planar.lean:35`),
  `RS.isPrimitiveAlongMap_of_ball` (cell primitive, `LocalPrimitive.lean:243`),
  `IsPrimitiveAlong.pathIntegral_eq` (`Continuation.lean:161`),
  `RS.nonempty_open_diff_finite` (`Perturb.lean`).
- **`Jacobian/Forms/` (BUILT)**: `Form1`, `coeffIn`/`coeffAt` (+ linearity, `coeffIn_trans`,
  `Form1.analyticOnNhd_coeffIn`, `Form1.ext_coeffAt`), `genus X := Module.finrank ℂ (Form1 X)`
  (definitional — so `Fin (genus X)` indexes `basis X` with no cast).
- **`Jacobian/ResidueCalculus/` (BUILT)**: `resAt`, `resAt_analyticAt_mul` (`Residue.lean:223`),
  `laurentCoeffAt_order_ne_zero` (`LaurentCoeff.lean:176`), `taylorCoeffAt_zero_apply` (rfl).
- **`Jacobian/Surface/` (BUILT)**: `Identity.lean` (identity theorem for holomorphic *maps* —
  NOT directly usable for form coefficients, see §6.4), `RealSmooth.lean` (PoU — NOT needed on the
  chosen route), `InverseFunction.lean` (1-dimensional; our inverse-function use is on `ℂ^g` and
  goes through mathlib directly — this file is not needed).
- **`Jacobian/Meromorphic/` + `Jacobian/CanonicalForms/` (under revision — cited by DESIGN names
  per task):** `ℳ X`, `RS.divisor : ℳ X → Divisor X`
  (`Divisor X = Function.locallyFinsuppWithin (univ) ℤ`, `single` divisors per
  `meromorphic-and-divisors.md:139`), `holoRepr`; `MForm`, `MForm.ofForm1`, `MForm.smul`
  (coeffAt = `h.holoRepr ∘ (chartAt).symm * ω.coeffAt`, `canonical-forms.md` §D7),
  `MForm.ofForm1_ord_nonneg`, `MForm.resAt`, `MForm.ord`.
- **`docs/design/residue-theorem.md` (design-stage, unit not on disk):** consumed statement
  `RS.residueTheorem (ω : MForm X) {S : Finset X} (hS : ω.PoleSet ⊆ S) : ∑ x ∈ S, ω.resAt x = 0`
  (its §2), plus its Compat `MForm.resAt_eq_zero_of_ord_nonneg`. Its §4.2 "Area-Gluing atom" is
  relevant ONLY to this unit's *fallback* nondegeneracy route (§5.3) — the primary route uses none
  of it.
- **`docs/design/abel-weak-solutions.md`** (support unit for #29): read §0–§1, §10. Confirms
  abel-theorem (#29) owns Forster 20.7 both directions and was **"not yet designed"** at that
  doc's writing; a sibling designer is producing `docs/design/abel-theorem.md` concurrently with
  this document. `docs/design/abel-theorem.md` does **not exist on disk** at this design's time of
  writing (checked). Coordination is via `docs/requests/abel-theorem.md`, filed by this design
  (§7) with the exact statement this unit consumes.
- **`docs/Jacobian_challenge.lean`**: the four gated instances (lines 78, 83, 86, 89) are the only
  challenge items gated on this unit; `ofCurve_contMDiff` (94) and the functoriality block also
  *state-level* depend on the discreteness instance per jaccon's ledger.

Verified state (searched, not assumed): `Jacobian/PeriodLattice/` does not exist;
`docs/design/abel-theorem.md` does not exist; `Jacobian/Abel*`, `Jacobian/ResidueTheorem/` do not
exist; `grep -rn sorry Jacobian/MeromorphicTrace/PlanarTrace.lean` — irrelevant to this unit
(nothing here routes through form-trace-tower).

---

## 1. Forster §21, faithful transcription (what he ACTUALLY does)

### 1.1 §21.1 Lattices (book 166–167 / PDF 172–173)

**Theorem 21.1.** `Γ ⊆ V` (real `N`-dim vector space) is a lattice (`= ℤγ₁ + ⋯ + ℤγ_N`, `γᵢ`
ℝ-independent) **iff** (i) `Γ` is discrete and (ii) `Γ` lies in no proper subspace. Proof: an
induction on `N` with a minimal-`c(γ_N)` choice in a compact parallelotope.

**We do not formalize 21.1.** Mathlib's `ZLattice` API *is* 21.1: the class
`IsZLattice K L` (`Mathlib/Algebra/Module/ZLattice/Basic.lean:435`) takes exactly Forster's (i)
(`[DiscreteTopology L]`) and (ii) (`span_top : span K (L : Set E) = ⊤`), and delivers the ℤ-basis
(`ZLattice.module_free:512`, `ZLattice.rank:525`) and — through jaccon's already-built
`RS.compactSpace_torus` — compactness of the quotient. So this unit's obligations are precisely
Forster's hypotheses (i) and (ii) for `Λ = periodSubgroup X`, nothing more.

### 1.2 §21.2 Period lattices (book 167–168 / PDF 173–174)

`Per(ω₁,…,ω_g) := {(∫_α ω₁, …, ∫_α ω_g) : α ∈ π₁(X)} ⊆ ℂ^g`, for a basis `ω₁,…,ω_g` of `Ω(X)`,
`g ≥ 1`. Project counterpart: `periodSubgroup X` = `AddSubgroup.closure` of the *range* of
`periodVector (basis X)` over based loops. Forster's `Per` is literally the range (π₁ is a group
and periods are additive under concatenation); the project's `closure` of the range equals the
range because the range is already subgroup-closed (`periodVector_trans/_symm/_refl`). This is
lemma `mem_periodSubgroup_iff` (§6.1) — needed so that a lattice element yields a SINGLE loop `γ`,
which is what step 21.4(b) consumes.

### 1.3 §21.3 Lemma, generic points (book 168 / PDF 174)

**Statement.** There are `g` **distinct** points `a₁,…,a_g ∈ X` such that any `ω ∈ Ω(X)` vanishing
at all `aⱼ` is identically zero.

**Forster's proof, verbatim structure.** For `a ∈ X` let `H_a := {ω ∈ Ω(X) : ω(a) = 0}`. Each
`H_a` is `Ω(X)` or has codimension 1 (kernel of the evaluation functional). `⋂_{a∈X} H_a = 0`
(a form vanishing everywhere is zero), `dim Ω(X) = g`, hence `g` points with
`H_{a₁} ∩ ⋯ ∩ H_{a_g} = 0` exist. □

The implicit content, made explicit for the builder (§6.2): the `g` points are picked by a strict
descending induction on `dim ⋂ H_{aⱼ}`; each step needs "a nonzero holomorphic form is nonzero at
some point NOT among the finitely many already chosen" — openness of the nonvanishing locus +
every nonempty open subset of a Riemann surface is infinite. Distinctness is FORCED (Forster
silently gets it from the same avoidance) because 21.4(a) needs disjoint coordinate neighborhoods.

**Citation trace for 21.3:** `dim Ω(X) = g` (his 17.10; ours: *definitional*, `genus X :=
finrank ℂ (Form1 X)`); the identity theorem (implicit in `⋂ H_a = 0` via `Form1.ext_coeffAt` —
pointwise, no analytic continuation needed at this step); nothing else.

### 1.4 §21.4 Theorem, `Per` is a lattice (book 168–170 / PDF 174–176)

**(a) The local Jacobi map** (PDF 174–175). Choose `aⱼ` per 21.3 and *disjoint* simply connected
coordinate neighborhoods `(Uⱼ, zⱼ)`, `zⱼ(aⱼ) = 0`. Write `ωᵢ = φᵢⱼ dzⱼ` on `Uⱼ`. By 21.3 the
matrix `A := (φᵢⱼ(aⱼ))` has rank `g` [if `∑ᵢ cᵢ φᵢⱼ(aⱼ) = 0 ∀j` then `∑ᵢ cᵢωᵢ` vanishes at every
`aⱼ`, hence is 0, hence `c = 0` — note this is invertibility of the TRANSPOSE action, and since
`A` is square, of `A` itself]. Define `F : U₁ × ⋯ × U_g → ℂ^g`,
`Fᵢ(x₁,…,x_g) := ∑ⱼ ∫_{aⱼ}^{xⱼ} ωᵢ` (integrals inside `Uⱼ`, path-independent there). `F` is
complex differentiable with Jacobian matrix `J_F(x) = (φᵢⱼ(xⱼ))`, invertible at `a = (a₁,…,a_g)`;
**hence `W := F(U₁ × ⋯ × U_g)` is a neighborhood of `F(a) = 0`** — this "hence" is the inverse
function theorem (Forster does not even name it).

**(b) Discreteness: `Γ ∩ W = 0`** (PDF 175). Suppose `t ∈ Γ ∩ (W \ 0)`. Then `t = F(x)` for some
`x = (x₁,…,x_g) ≠ a`. Renumber so `xⱼ ≠ aⱼ` for `j ≤ k` and `xⱼ = aⱼ` for `j > k`, `1 ≤ k ≤ g`.
**"By Abel's Theorem there exists a meromorphic function `f` on `X` which has a pole of first
order at `aⱼ`, `1 ≤ j ≤ k`, a zero of first order at `xⱼ`, `1 ≤ j ≤ k`, and is holomorphic
otherwise."** [Unpacked: `t ∈ Γ` means `t` is the period vector of a single `α ∈ π₁(X)`; the
1-chain `c := ∑ⱼ(path aⱼ→xⱼ in Uⱼ) − α` has `∂c = D := ∑ⱼ≤k(xⱼ − aⱼ)` and `∫_c ωᵢ = Fᵢ(x) − tᵢ
= 0` for all `i`, hence `∫_c ω = 0` for all `ω ∈ Ω(X)` by linearity; Abel 20.7(⇐) gives `f` with
`(f) = D`.] Let `cⱼzⱼ⁻¹` be the principal part of `f` at `aⱼ`; `cⱼ ≠ 0` for `j ≤ k`. **By the
Residue Theorem (10.21):** `0 = Res(fωᵢ) = ∑ⱼ₌₁ᵏ cⱼφᵢⱼ(aⱼ)` for `i = 1,…,g` — contradicting
rank `A = g`. So `Γ ∩ W ⊆ {0}`: `Γ` is discrete. □

**Citation trace for (b):** Abel 20.7, sufficiency direction ONLY, for a `k ≤ g`-point divisor
(NOT just two points — this is load-bearing for the request in §7); Residue Theorem 10.21; the
inverse function theorem on `ℂ^g` (implicit); 21.3.

**(c) Nondegeneracy** (PDF 175–176). If `Γ` lay in a proper real subspace of `ℂ^g`, there would be
a nontrivial real linear form vanishing on `Γ`; every real linear form is the real part of a
complex linear form, so one gets `(c₁,…,c_g) ∈ ℂ^g \ 0` with
`Re(∑ⱼ cⱼ ∫_α ωⱼ) = 0` for every `α ∈ π₁(X)`. **"But from Corollary (19.8) it then follows that
`ω := c₁ω₁ + ⋯ + c_gω_g = 0`, a contradiction!"** □

**Citation trace for (c):** Corollary 19.8 and nothing else. So the entire nondegeneracy content
lives in §19 — dissected next.

### 1.5 The 19.8 dependency chain, dissected (book 153–157 / PDF 159–163)

**Cor 19.8:** `ω ∈ Ω(X)` with `Re(∫_γ ω) = 0` for every closed curve `γ` ⟹ `ω = 0`. Forster's
proof is three citations: `Re(ω)` is exact **(Thm 10.15**: a closed 1-form with vanishing periods
has a global primitive**)**; exact harmonic forms vanish **(Cor 19.7**, from the orthogonal
decomposition: `dE(X) ⊥ Harm¹(X) = Ω(X) ⊕ Ω̄(X)` w.r.t. `⟨ω₁,ω₂⟩ := ∬_X ω₁ ∧ *ω̄₂`, positive
definite by the local computation `ω ∧ *ω̄ = 2(|f|² + |g|²) dx∧dy` (19.5), orthogonality via
`∬_X dη = 0` for compactly supported `η` (Thm 10.20)**)**; and `Re(ω) = 0 ⟹ ω = 0` for
holomorphic `ω` **(Thm 19.4** uniqueness half: locally `ω = df` with `f` holomorphic of constant
real part, hence constant**)**.

**The reconciliation the task demands.** Forster's §21 is genuinely **dissection-free**: no cut
surface, no fundamental polygon, no `H₁` basis anywhere in 21.3–21.4 (his `H₁(X) ≅ ℤ^{2g}` in 21.5
is a *consequence*, not an input). But it is NOT free of surface integration: through 19.5–19.8 it
uses the L²-inner-product `∬_X ω ∧ *ω̄` — i.e. a chart-independent integral of 2-forms on `X`
(his §10.18 machinery) — plus compact-support Stokes (10.20). The blueprint's ⚠ ("cut-surface +
Green's-theorem flavor, NOT Hodge") names a THIRD route (classical Riemann bilinear relations via
dissection — where dissection usually enters, as the task brief notes). What must be avoided per
the ⚠ is Hodge/de Rham (19.9–19.14, harmonic decomposition of `E^{0,1}` etc.); Forster's 19.8
chain stops short of those (it needs only 19.4–19.7), but it still rests on `∬_X` for smooth
2-forms — machinery **this project does not have** (verified: no design doc defines a
chart-independent 2-form integral on `X`; residue-theorem's §4.2 Area-Gluing atom is the only
approximation, is specialized to `wirtingerDbar`-pairings against `MForm` coefficients, and is not
built). §5 resolves this with a route that is *strictly cheaper than all three*: the maximum
principle. §5.3 records the Green/PoU route (the blueprint's "cheapest formal path") as the
documented fallback, made concrete.

### 1.6 §21.5–21.9 (context, out of scope)

21.5 (`H₁(X) ≅ ℤ^{2g}`), 21.6 (`Jac(X)`, `Pic`), 21.7 (Jacobi inversion: `j : Pic₀ ≅ Jac`,
re-using 21.4(a)'s `F`), 21.8–21.9 (`X^g → Jac(X)` surjective, via RR): none is a challenge
obligation; none is designed here. (`ofCurve_inj` is abel-theorem's; the challenge does not ask
for inversion/surjectivity.)

---

## 2. What this unit must produce (statement bank)

Standing context throughout (CONVENTIONS):

```lean
open scoped ContDiff Manifold
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
```

Abbreviate `P₀ := Classical.arbitrary X` (the basepoint frozen by `RS.periodSubgroup`) and
`V := Fin (genus X) → ℂ`. Namespace `RS` throughout.

```lean
-- (Membership; §6.1)
theorem mem_periodSubgroup_iff {t : Fin (genus X) → ℂ} :
    t ∈ periodSubgroup X ↔ ∃ γ : Path (Classical.arbitrary X) (Classical.arbitrary X),
      periodVector (basis X) γ = t

-- (Generic points, Forster 21.3; §6.2)  [gated on nothing new]
theorem exists_genericPoints (hg : 1 ≤ genus X) :
    ∃ a : Fin (genus X) → X, Function.Injective a ∧
      ∀ η : Form1 X, (∀ j, coeffAt (a j) η = 0) → η = 0

-- (Local Jacobi + Abel + residues, Forster 21.4(a)(b); §6.3)  [GATED: abel-theorem, residue-theorem]
theorem exists_isolating_nhds_periodSubgroup (hg : 1 ≤ genus X) :
    ∃ W ∈ 𝓝 (0 : Fin (genus X) → ℂ), ∀ t ∈ periodSubgroup X, t ∈ W → t = 0

-- (Discreteness discharge; §6.3, §8)
theorem discreteTopology_periodSubgroup : DiscreteTopology (periodSubgroup X)
theorem periodSubgroup_topologicalClosure_eq :
    (periodSubgroup X).topologicalClosure = periodSubgroup X
instance instDiscretePeriodClosure : DiscreteTopology (periodSubgroup X).topologicalClosure

-- (Nondegeneracy, Forster 21.4(c) ⇽ 19.8 replacement; §5, §6.4–6.5)  [ungated: mathlib + built units]
theorem form1_eq_zero_of_re_period_eq_zero {η : Form1 X}
    (h : ∀ γ : Path (Classical.arbitrary X) (Classical.arbitrary X), (period γ η).re = 0) :
    η = 0

-- (Full rank discharge; §6.6, §8)
theorem span_real_periodSubgroup :
    Submodule.span ℝ ((periodSubgroup X : Set (Fin (genus X) → ℂ))) = ⊤
instance instIsZLatticePeriodClosure :
    IsZLattice ℝ (periodSubgroup X).topologicalClosure.toIntSubmodule

-- (Bonus, the blueprint's "real basis of rank 2g", free from mathlib once the instances exist)
theorem finrank_int_periodSubgroup :
    Module.finrank ℤ (periodSubgroup X).topologicalClosure.toIntSubmodule = 2 * genus X
```

All statements are genus-unconditional except the two internal `hg : 1 ≤ genus X` theorems; the
instances handle `genus X = 0` by the subsingleton argument (§6.7). With the two instances
registered, jaccon's `Jacobian.instChartedSpace/instIsManifold/instLieAddGroup/instCompactSpace`
fire with **no further code** (their ledger says so, verified against `Basic.lean:104-121`).

---

## 3. Dependency/gate map (each gate NAMED)

| Ingredient | Source | Status |
|---|---|---|
| `periodSubgroup`, `basis`, torus instances, `toIntSubmodule` bridge | jacobian-construction | **BUILT** |
| `pathIntegral` algebra, planar primitives, cell primitive, `nonempty_open_diff_finite` | paths-and-integrals | **BUILT** |
| `coeffIn/coeffAt` algebra, `coeffIn_trans`, analyticity, `ext_coeffAt`, `genus` | holomorphic-forms | **BUILT** |
| `resAt`, `resAt_analyticAt_mul`, `laurentCoeffAt_order_ne_zero`, `taylorCoeffAt_zero_apply` | residue-calculus | **BUILT** |
| `analyticAt_transition` (chart transitions, nonvanishing deriv) | local-multiplicity `ChartBridge.lean` | **BUILT** |
| `ℳ X`, `RS.divisor`, `single` divisors, `holoRepr`, ord API | meromorphic-and-divisors | built, **under revision** — cite design names |
| `MForm`, `MForm.ofForm1`, `MForm.smul`, `MForm.resAt/ord`, `ofForm1_ord_nonneg` | canonical-forms (D7) | **GATE (design-frozen, unit mid-build)** |
| `RS.residueTheorem` (+ `resAt_eq_zero_of_ord_nonneg`) | residue-theorem §2 | **GATE (design-stage)** |
| Abel sufficiency, k-point path form | abel-theorem (#29, sibling designing now) | **GATE — request filed, §7** |
| IFT `HasStrictFDerivAt.map_nhds_eq_of_equiv`, `toContinuousLinearEquivOfDetNeZero`, `AnalyticAt.pi`, `AnalyticAt.hasStrictFDerivAt` | mathlib (pin-verified §11) | ready |
| `AddSubgroup.isClosed_of_discrete`, `discreteTopology_iff_isOpen_singleton_zero`, `IsZLattice`, `ZLattice.rank`, `Submodule.exists_dual_map_eq_bot_of_lt_top`, `AnalyticAt.eventually_constant_or_nhds_le_map_nhds`, `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` | mathlib (pin-verified §11) | ready |

**NOT needed on the primary routes** (explicitly, to prevent scope creep): planar-stokes-atoms,
PoU (`RS.exists_smoothPartitionOfUnity`), residue-theorem's Area-Gluing atom, monodromy,
form-trace-tower, Surface/InverseFunction.lean, any 2-form integration, any harmonic-form theory.
Gate summary: **discreteness** is gated on abel-theorem + residue-theorem (+ canonical-forms);
**nondegeneracy and the `IsZLattice` span content are gated on nothing unbuilt** (the `IsZLattice`
*instance* still waits for discreteness, because mathlib's class carries `[DiscreteTopology L]`).

---

## 4. Routing call #1 (discreteness): follow Forster 21.4(a)–(b) exactly

No alternative is viable: a finitely generated subgroup of `ℂ^g` need not be discrete, so no
soft argument exists; the H₁-pairing route is dissection; Forster's local-Jacobi + Abel + residues
route is the dissection-free one and every ingredient is either built or already an in-flight
design obligation of an upstream unit. Design in §6.2–§6.3.

## 5. Routing call #2 (nondegeneracy) — the make-or-break call

**Statement to prove** (the exact reduction of Forster 21.4(c), see §6.6 for the linear-algebra
shell): `form1_eq_zero_of_re_period_eq_zero`: if all periods of `η ∈ Form1 X` at the basepoint
have vanishing real part, then `η = 0`.

### 5.1 PRIMARY: the maximum-principle route (no integration at all)

Mathematical content, in full (this replaces Forster's 19.4+19.5+19.7+10.15 chain):

1. **Global real primitive.** Define `F : X → ℝ`,
   `F x := (pathIntegral (PathConnectedSpace.somePath P₀ x) η).re`. For ANY path `σ : Path x y`:
   `F y − F x = (pathIntegral σ η).re`, because
   `((somePath P₀ x).trans σ).trans (somePath P₀ y).symm` is a loop at `P₀` and the hypothesis
   kills the real part of its period (`pathIntegral_trans/_symm`). [This replaces Forster's
   Thm 10.15; no smooth-form monodromy needed — only holomorphic path integration, all built.]
2. **Local form.** Fix `x₀`; let `e := chartAt ℂ x₀` (∈ maximal atlas), pick `r > 0` with
   `ball (e x₀) r ⊆ e.target`, and a planar primitive `g` of `coeffIn e η` on the ball
   (`exists_hasDerivAt_ball`, prescribed value `g (e x₀) = 0`). For `x ∈ e.symm '' ball (e x₀) r`,
   the in-chart segment path `σ : Path x₀ x`, `σ t := e.symm (lineMap (e x₀) (e x) t)`, stays in
   the ball; `isPrimitiveAlongMap_of_ball` + `IsPrimitiveAlong.pathIntegral_eq` give
   `pathIntegral σ η = g (e x) − g (e x₀) = g (e x)`. With step 1:
   **`F x = F x₀ + (g (e x)).re` on the (open) chart-ball neighborhood.** In particular `F` is
   continuous (each `g` continuous, `e` continuous).
3. **Maximum.** `X` compact, nonempty (`ConnectedSpace`): `F` attains a maximum at some `p`
   (`isCompact_univ.exists_isMaxOn` + `IsMaxOn.isLocalMax`). By step 2 at `x₀ := p`,
   `w ↦ (g w).re` has a **local max at `e p`** (transport the neighborhood through the
   homeomorphism `e`).
4. **Open mapping dichotomy.** `g` is differentiable on the ball (`HasDerivAt`), hence
   `AnalyticAt ℂ g (e p)`. Apply `AnalyticAt.eventually_constant_or_nhds_le_map_nhds`
   (mathlib, `Analysis/Complex/OpenMapping.lean`):
   * if `𝓝 (g (e p)) ≤ map g (𝓝 (e p))`: the local-max set `{u | u.re ≤ (g (e p)).re}` would be a
     neighborhood of `g (e p)`, yet it excludes `g (e p) + ε/2` for every small real `ε > 0` —
     contradiction (spiked, §11 item 5);
   * hence `g` is eventually constant at `e p`, so `deriv g = coeffIn e η` vanishes on an open
     neighborhood of `e p` inside the ball (`eventually` of `=` on an open set ⟹ constant there
     ⟹ zero derivative; `HasDerivAt.deriv` identifies `deriv g` with `coeffIn e η`).
5. **Identity theorem.** `coeffIn e η ≡ 0` near `e p` ⟹ `η = 0` (§6.4, the clopen chart-ball
   propagation lemma `form1_eq_zero_of_eventually_coeffIn_zero` — self-contained in this unit,
   ~70 lines, from `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` +
   `coeffIn_trans`).

Faithfulness audit: this proves exactly Forster's Cor 19.8 (holomorphic case) — the hypothesis
"loops at the one basepoint `P₀`" suffices for step 1, which is where Forster's "every closed
curve" is consumed. Steps 3–4 replace the L²-orthogonality (19.5–19.7) by the maximum principle
(the classical "no nonconstant harmonic function on a compact surface" argument, localized so that
even global constancy of `F` is never needed); step 5 replaces 19.4. **No Hodge, no de Rham, no
dissection, no cut surface, no Green/Stokes, no partition of unity, no 2-form integral.** Every
ingredient is BUILT or pin-verified mathlib (§11).

### 5.2 Why not transcribe Forster's 19.5–19.8 literally

His route needs `∬_X` of smooth 2-forms as a chart-independent functional (§10.18) plus
compact-support Stokes (10.20) plus the `*`-operator algebra (19.1–19.2, 19.5–19.6). The project
has none of these; building them honestly is the Area-Gluing atom (residue-theorem §4.2)
generalized from `MForm`-coefficient pairings to arbitrary `(0,0)×(1,0)` products, plus a PoU
double-sum well-definedness lemma — several hundred lines of genuinely new measure-theoretic
gluing, all to prove one implication that §5.1 gets from a 5-step local argument. The blueprint's
⚠ was written before it was known what would be on disk; given the actual built state, the
maximum principle is the cheapest correct path and stays fully inside the ⚠'s prohibition (it is
neither Hodge nor de Rham).

### 5.3 Documented FALLBACK: the PoU + planar-Stokes positivity (the blueprint's "Green flavor")

Recorded concretely in case a reviewer insists on Forster's integral argument. With `F` from
§5.1 step 1 and `u := F ∘ e.symm`, `h := coeffIn e η` in a chart: the pointwise Wirtinger identity
`wirtingerDbar (u·h) = wirtingerDbar u · h = ½ conj h · h = ½|h|²` (since `∂̄(Re G) = ½ conj G'`
for `G` a holomorphic primitive of `h`) turns `d(F η)` into a nonnegative density. Take a finite
smooth PoU `{ψⱼ}` subordinate to charts (`RS.exists_smoothPartitionOfUnity`, built):
`0 = ∑ⱼ ∫ wirtingerDbar((ψⱼ·F·η)-in-chart-j)` by the built compact-support planar Stokes
(`integral_wirtingerDbar_eq_zero`); expanding by the Leibniz rule,
`0 = ∑ⱼ ∫ wirtingerDbar(ψⱼ)·u·h + ½ ∑ⱼ ∫ ψⱼ|h|²`. The second sum is `> 0` unless `η = 0`; the
first sum vanishes because `∑ⱼ dψⱼ = 0` — but showing THAT requires comparing integrals of the
`(1,1)`-pieces across two charts (a double-PoU/common-refinement swap), i.e. exactly the
Area-Gluing change-of-variables atom (`|deriv τ|²` = the real Jacobian; residue-theorem §1.6/§4.2)
generalized to arbitrary continuous covariant coefficients. Cost estimate: the general atom
(~200 lines) + refinement bookkeeping (~120) + assembly (~150). **Do not build unless §5.1's
step 4 or 5 fails in an unforeseen way** (risk assessed LOW, both spiked/inventoried).

---

## 6. File plan and detailed proof plans

Unit root `Jacobian/PeriodLattice.lean` (docstring per CONVENTIONS) + 5 files.

### 6.1 `PeriodLattice/Membership.lean` (~90 lines) — §21.2

```lean
def periodRange (X) [...] : AddSubgroup (Fin (genus X) → ℂ) where
  carrier := Set.range fun γ : Path (Classical.arbitrary X) (Classical.arbitrary X) =>
    periodVector (basis X) γ
  zero_mem' := ⟨Path.refl _, periodVector_refl _⟩
  add_mem'  := by rintro _ _ ⟨γ₁, rfl⟩ ⟨γ₂, rfl⟩; exact ⟨γ₁.trans γ₂, periodVector_trans ..⟩
  neg_mem'  := by rintro _ ⟨γ, rfl⟩; exact ⟨γ.symm, periodVector_symm ..⟩

theorem periodSubgroup_eq_periodRange : periodSubgroup X = periodRange X :=
  -- `AddSubgroup.closure_eq_of_le` antisymmetry, or `AddSubgroup.closure_eq (periodRange X)`
  -- after `show closure ↑(periodRange X) = _` (the closure of a subgroup's carrier is itself)
theorem mem_periodSubgroup_iff : t ∈ periodSubgroup X ↔ ∃ γ, periodVector (basis X) γ = t
```

Nothing subtle; `AddSubgroup.closure_eq : closure ↑H = H` closes it.

### 6.2 `PeriodLattice/GenericPoints.lean` (~180 lines) — §21.3

Helper 1 — openness of nonvanishing (also used by 6.4):
```lean
theorem isOpen_coeffAt_ne_zero (η : Form1 X) : IsOpen {x : X | coeffAt x η ≠ 0}
```
*Proof.* At `x₀` with `coeffAt x₀ η ≠ 0`: in the fixed chart `e := chartAt ℂ x₀`, `coeffIn e η` is
continuous (`Form1.continuousOn_coeffIn`) and nonzero at `e x₀`, so nonzero on `e ⁻¹'`-of an open
set; for `x` in that set, `coeffAt x η = deriv (transition) · coeffIn e η (…) ≠ 0` by
`coeffIn_trans` (CC1 orientation, `Forms/Coeffs`) with nonvanishing transition derivative
(`analyticAt_transition`, `LocalMultiplicity/ChartBridge`). [If holomorphic-forms already exports
this or an equivalent, reuse; else local, with an upstream request filed.]

Helper 2 — a nonzero form is nonzero off any finite set:
```lean
theorem exists_coeffAt_ne_zero_notMem {η : Form1 X} (hη : η ≠ 0) (S : Finset X) :
    ∃ x, x ∉ S ∧ coeffAt x η ≠ 0
```
*Proof.* `{coeffAt · η ≠ 0}` is open and nonempty (`Form1.ext_coeffAt`: if empty, `η = 0`);
`RS.nonempty_open_diff_finite` (paths-and-integrals `Perturb.lean`, built) avoids `S`.

Main lemma (21.3) — induction over descending kernels:
```lean
theorem exists_genericPoints (hg : 1 ≤ genus X) : ∃ a : Fin (genus X) → X,
    Function.Injective a ∧ ∀ η : Form1 X, (∀ j, coeffAt (a j) η = 0) → η = 0
```
*Proof plan.* Work with `Hs (s : Finset X) : Submodule ℂ (Form1 X) := ⨅ x ∈ s, ker (evalAtₗ x)`
where `evalAtₗ x : Form1 X →ₗ[ℂ] ℂ` is `coeffAt x` bundled (linear by `coeffAt_add/_smul`).
Auxiliary claim, by induction on `k : ℕ`: `∃ s : Finset X, s.card = k ∧ finrank ℂ (Hs s) ≤ g − k`
for `k ≤ g` — step: if `Hs s ≠ ⊥`, pick `0 ≠ η ∈ Hs s`, pick `x ∉ s` with `coeffAt x η ≠ 0`
(Helper 2), then `Hs (insert x s) < Hs s` so the finrank drops by ≥ 1
(`Submodule.finrank_lt_finrank_of_lt`); if `Hs s = ⊥` already, insert ANY fresh point (Helper 2
applied to any basis form, or `nonempty_open_diff_finite` on `univ`) — the infimum only shrinks.
At `k = g`: `finrank (Hs s) = 0` hence `Hs s = ⊥` (`Submodule.finrank_eq_zero`), `s.card = g`;
enumerate `s` by an equiv `Fin g ≃ s` to get injective `a` with `⋂ ker = ⊥`, which is the stated
implication. (Alternative shape: direct strong induction producing the injective tuple; builder's
choice — the mathematics is fixed.)

Matrix corollary:
```lean
/-- The generic-point evaluation matrix `A i j := coeffAt (a j) (basis X i)` is invertible. -/
theorem det_genericMatrix_ne_zero (ha : ∀ η, (∀ j, coeffAt (a j) η = 0) → η = 0) :
    (Matrix.of fun i j => coeffAt (a j) (basis X i)).det ≠ 0
```
*Proof.* If `det = 0`, `Matrix.exists_vecMul_eq_zero_iff` (field) gives `c ≠ 0` with
`c ᵥ* A = 0`, i.e. `∀ j, ∑ i, c i * coeffAt (a j) (basis X i) = 0`, i.e. (linearity of `coeffAt`)
`coeffAt (a j) (∑ i, c i • basis X i) = 0 ∀ j`; by `ha` the form vanishes, and by basis linear
independence `c = 0` — contradiction. (Transpose orientation exactly as Forster; note this also
yields `A.det ≠ 0` for the `mulVec` direction used twice in 6.3.)

### 6.3 `PeriodLattice/Discreteness.lean` (~420 lines) — §21.4(a)(b) + discharge

**Stage A: chart-ball data.** From `exists_genericPoints`: points `a j`, charts
`e j := chartAt ℂ (a j)` (`chart_mem_maximalAtlas`), radii `r j > 0` with
`ball (e j (a j)) (r j) ⊆ (e j).target` and the open sets `V j := (e j).symm '' ball …`
**pairwise disjoint** (T2 separation of the `g` distinct points; shrink `r j` until
`V j ⊆ (chosen disjoint open) j` — routine continuity-at-a-point argument).

**Stage B: the local Jacobi map (21.4(a)), purely planar.** For each `i j`, a primitive
`gp i j : ℂ → ℂ` of `coeffIn (e j) (basis X i)` on the ball with `gp i j (e j (a j)) = 0`
(`exists_hasDerivAt_ball`). Define

```lean
𝔉 : (Fin (genus X) → ℂ) → (Fin (genus X) → ℂ) := fun w i => ∑ j, gp i j (w j)
c₀ : Fin (genus X) → ℂ := fun j => e j (a j)      -- the center; 𝔉 c₀ = 0
A  : Matrix (Fin g) (Fin g) ℂ := .of fun i j => coeffAt (a j) (basis X i)
```

`HasStrictFDerivAt 𝔉 (A-as-CLM) c₀`, where `A-as-CLM := (Matrix.mulVecLin A).toContinuousLinearMap`:
each component `w ↦ gp i j (w j)` is `AnalyticAt` at `c₀` (differentiable-on-ball ⟹
`DifferentiableOn.analyticAt`; compose with the continuous-linear coordinate projection), so `𝔉`
is `AnalyticAt` (`Finset.sum`, `AnalyticAt.pi`), hence `AnalyticAt.hasStrictFDerivAt`; identify
the derivative via a hand-built `HasFDerivAt 𝔉 (A-as-CLM) c₀` (sum/comp of `HasDerivAt (gp i j)`,
noting `coeffIn (e j) (basis X i) (c₀ j) = coeffAt (a j) (basis X i)` **by definition of
`coeffAt`**) and `HasFDerivAt.unique`. With `det A ≠ 0` (6.2), form the equiv by
`ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero` (`(A-as-CLM).det = A.det` via
`LinearMap.det_toLin'`-style glue — spiked, §11 item 4) and conclude by
`HasStrictFDerivAt.map_nhds_eq_of_equiv`:

```lean
theorem jacobi_image_mem_nhds :  𝔉 '' (Set.univ.pi fun j => ball (c₀ j) (r j)) ∈ 𝓝 0
```
(the polydisc is a nbhd of `c₀` by `set_pi_mem_nhds`; `𝔉 c₀ = 0` since every `gp i j` vanishes at
the center).

**Stage C: `Λ ∩ W ⊆ {0}` (21.4(b)).** `exists_isolating_nhds_periodSubgroup`: take
`W := 𝔉 '' polydisc`. Let `t ∈ periodSubgroup X`, `t = 𝔉 w`, `w ∈ polydisc`; suppose `t ≠ 0`.
1. `γ : Path P₀ P₀` with `periodVector (basis X) γ = t` (`mem_periodSubgroup_iff`).
2. Points `x j := (e j).symm (w j) ∈ V j`; paths `σ j : Path (a j) (x j)`,
   `σ j t := (e j).symm (lineMap (c₀ j) (w j) t)` (segment ⊆ ball by convexity; continuity through
   `(e j).symm`; endpoints by `left_inv`). By `isPrimitiveAlongMap_of_ball` +
   `IsPrimitiveAlong.pathIntegral_eq`: `pathIntegral (σ j) (basis X i) = gp i j (w j)`.
   Hence `∀ i, ∑ j, pathIntegral (σ j) (basis X i) = t i = period γ (basis X i)`, and by
   basis-expansion + `pathIntegralₗ` linearity: `∀ η : Form1 X, ∑ j, pathIntegral (σ j) η =
   period γ η`.
3. **[GATE abel-theorem]** `abel_sufficiency` (§7) gives `f : ℳ X`, `f ≠ 0`,
   `RS.divisor f = D := ∑ j, (single (x j) 1 − single (a j) 1)`.
4. `t ≠ 0 ⟹ ∃ j, x j ≠ a j` (else `w = c₀` — `(e j).symm` injective on target — and `t = 𝔉 c₀
   = 0`). Let `S := {j | x j ≠ a j}` (nonempty). Divisor values (disjointness of the `V j` + all
   `a j` distinct + `x j ∈ V j`): `D (a j) = −1` for `j ∈ S`, `D (a j) = 0` for `j ∉ S`,
   `D (x j) = 1` for `j ∈ S`, `D = 0` elsewhere.
5. Residues. For `j ∈ S`, the chart reading `fⱼ := f.holoRepr ∘ (e j).symm` has
   `meromorphicOrderAt fⱼ (c₀ j) = −1` (divisor value `−1`, `f ≠ 0` so ord ≠ ⊤; meromorphic-and-
   divisors' ord/chart compatibility). Set `c j := resAt fⱼ (c₀ j) ≠ 0`
   (`laurentCoeffAt_order_ne_zero`); for `j ∉ S`, `c j := 0`.
   For each `i`, the pair form `ωᵢ := MForm.smul f (MForm.ofForm1 (basis X i))` [canonical-forms
   D7] has `coeffAt (a j) = fⱼ · coeffIn (e j) (basis X i)` and
   `ωᵢ.resAt (a j) = coeffAt (a j) (basis X i) * c j = A i j * c j`
   (`resAt_analyticAt_mul` with `n := −1`, single-term `Icc (−1) (−1)` sum,
   `taylorCoeffAt_zero_apply`, `mul_comm`); `ωᵢ.PoleSet ⊆ a '' S ⊆ a '' univ`
   (ord additivity of `smul` + `ofForm1_ord_nonneg`; Compat lemma if canonical-forms does not
   export `ord_smul`, from mathlib `meromorphicOrderAt_mul` on chart readings — request filed).
6. **[GATE residue-theorem]** `residueTheorem ωᵢ (S := Finset.univ.image a)`:
   `0 = ∑ x ∈ image a, ωᵢ.resAt x = ∑ j, A i j * c j` (`Finset.sum_image`, `a` injective; non-pole
   terms vanish by `resAt_eq_zero_of_ord_nonneg`). I.e. `A.mulVec c = 0` with `c ≠ 0` —
   contradicting `det A ≠ 0` (`Matrix.exists_mulVec_eq_zero_iff`). ∎

**Stage D: discharge.**
```lean
theorem discreteTopology_periodSubgroup : DiscreteTopology (periodSubgroup X) := by
  by_cases h : genus X = 0
  · -- IsEmpty (Fin (genus X)) ⟹ Unique (Fin (genus X) → ℂ) ⟹ Subsingleton ↥Λ
    -- ⟹ `Subsingleton.discreteTopology`
  · -- `exists_isolating_nhds_periodSubgroup` + interior ⟹ open `U ∋ 0` isolating 0 in Λ;
    -- `discreteTopology_iff_isOpen_singleton_zero.mpr` with `({0} : Set Λ) = (↑) ⁻¹' U`  (spiked)
theorem periodSubgroup_topologicalClosure_eq : (periodSubgroup X).topologicalClosure
    = periodSubgroup X :=
  SetLike.coe_injective (AddSubgroup.isClosed_of_discrete).closure_eq   -- (spiked)
instance instDiscretePeriodClosure : DiscreteTopology (periodSubgroup X).topologicalClosure := by
  rw [periodSubgroup_topologicalClosure_eq]; exact discreteTopology_periodSubgroup  -- (spiked)
```

### 6.4 `PeriodLattice/FormIdentity.lean` (~110 lines) — identity theorem for coefficients

```lean
theorem form1_eq_zero_of_eventually_coeffIn_zero {η : Form1 X} {x₀ : X}
    (h : ∀ᶠ z in 𝓝 ((chartAt ℂ x₀) x₀), coeffIn (chartAt ℂ x₀) η z = 0) : η = 0
```
*Proof plan (clopen).* `S := {x | ∀ᶠ z in 𝓝 (chartAt ℂ x x), coeffIn (chartAt ℂ x) η z = 0}`.
`S` is open: vanishing of `coeffIn (chartAt x)` near `chartAt x x` transports to vanishing of
`coeffIn (chartAt y)` near `chartAt y y` for `y` near `x` via `coeffIn_trans` (the transition
factor `deriv (…) ≠ 0` is irrelevant for the zero-locus direction). `S` is closed: if
`x ∈ closure S`, pick a ball `B ∋ chartAt x x` inside the target; `coeffIn (chartAt x) η` is
`AnalyticOnNhd` on `B` (built), vanishes near `chartAt x x'` for some `x' ∈ S` close to `x`
(transport again via `coeffIn_trans`), hence vanishes on all of the preconnected `B`
(`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`, mathlib
`Analysis/Analytic/Uniqueness`), so `x ∈ S`. `ConnectedSpace X` + `S` nonempty ⟹ `S = univ` ⟹
`coeffAt x η = 0 ∀x` ⟹ `η = 0` (`Form1.ext_coeffAt`). [Alternative discharge: canonical-forms' D5
zero-dichotomy through `MForm.ofForm1` — NOT used, to keep nondegeneracy free of the
canonical-forms gate; noted as a simplification a builder may take if that unit lands first.]

### 6.5 `PeriodLattice/Nondegeneracy.lean` (~260 lines) — §5.1

`form1_eq_zero_of_re_period_eq_zero` exactly per the 5-step plan of §5.1 (steps 1–4 in this file,
step 5 = 6.4's lemma). Sub-lemmas as stated there; the only non-obvious formal points, spelled out:
* the loop bookkeeping of step 1 is three `pathIntegral_trans/_symm` rewrites and `Complex.add_re`;
* step 2's path `σ` needs continuity of `t ↦ e.symm (lineMap …)`: `lineMap` continuous, segment ⊆
  ball ⊆ target, `e.symm` continuous on target (`OpenPartialHomeomorph.continuousOn_symm`) — same
  pattern as Stage C.2 of §6.3 (factor into a shared private helper `segmentPath`);
* step 3's transfer of `IsLocalMax` through `e`: `IsLocalMax (Re ∘ g) (e p)` from
  `IsLocalMax F p` + the local identity + `e.symm`-continuity (`Filter.Tendsto.eventually`);
* step 4 is spiked verbatim (§11 item 5).

### 6.6 `PeriodLattice/FullRank.lean` (~200 lines) — §21.4(c) shell + discharge + rank

```lean
theorem span_real_periodSubgroup :
    Submodule.span ℝ ((periodSubgroup X : Set (Fin (genus X) → ℂ))) = ⊤ := by
  by_contra hne  -- `lt_top_iff_ne_top`
  -- [mathlib] Submodule.exists_dual_map_eq_bot_of_lt_top (over ℝ; quotient of a vector space is
  -- free hence Projective — instance search) : ∃ φ ≠ 0, (span …).map φ = ⊥
  -- hence φ = 0 on Λ (Λ ⊆ span, `Submodule.subset_span`).
  -- Complexify BY HAND (Forster's "every real linear form is Re of a complex linear form"):
  --   c i := (φ (Pi.single i 1) : ℂ) − Complex.I * (φ (Pi.single i Complex.I) : ℂ)
  -- Claim: ∀ v, (∑ i, c i * v i).re = φ v.  Proof: both sides are ℝ-linear in v; decompose
  --   v = ∑ i, Pi.single i (v i)   (`pi_eq_sum_univ`),
  --   Pi.single i (v i) = (v i).re • Pi.single i 1 + (v i).im • Pi.single i I,
  -- and check the two generators by direct computation (Re c i = φ(single i 1),
  -- Re (c i * I) = −Im c i = φ(single i I)).
  -- Set ω := ∑ i, c i • basis X i. For every loop γ:
  --   (period γ ω).re = (∑ i, c i * periodVector (basis X) γ i).re    -- `map_sum` of pathIntegralₗ
  --                  = φ (periodVector (basis X) γ) = 0               -- periodVector γ ∈ Λ
  -- `form1_eq_zero_of_re_period_eq_zero` ⟹ ω = 0 ⟹ c = 0 (basis lin. indep.)
  -- ⟹ φ kills every Pi.single i 1, Pi.single i I ⟹ φ = 0 (same decomposition) — contradiction.

instance instIsZLatticePeriodClosure :
    IsZLattice ℝ (periodSubgroup X).topologicalClosure.toIntSubmodule := by
  -- DiscreteTopology argument of the class: instDiscretePeriodClosure + jaccon's
  -- `discreteTopology_toIntSubmodule` (instance search).
  refine ⟨?_⟩
  rw [AddSubgroup.coe_toIntSubmodule, periodSubgroup_topologicalClosure_eq]  -- (spiked)
  by_cases h : genus X = 0
  · -- Unique (Fin (genus X) → ℂ): every submodule is ⊤ (subsingleton ⟹ ⊥ = ⊤)
  · exact span_real_periodSubgroup

theorem finrank_int_periodSubgroup :
    Module.finrank ℤ (periodSubgroup X).topologicalClosure.toIntSubmodule = 2 * genus X := by
  -- `ZLattice.rank ℝ` : finrank ℤ L = finrank ℝ (Fin g → ℂ);
  -- `Module.finrank_pi_fintype`-style + `Complex.finrank_real_complex` : = g * 2
```

Note the genus-0 branch makes both instances honest at every genus (no special-cased vacuous
instance: the same generic statements, discharged by the same generic lemmas).

### 6.7 Root file `Jacobian/PeriodLattice.lean`

Imports the five files; module docstring = API summary (the statement bank of §2, marked with
which items are gated); registers nothing else. Final assembly then only needs
`import Jacobian.PeriodLattice` for all four challenge instances to fire.

---

## 7. The Abel gate — request filed (`docs/requests/abel-theorem.md`)

Exact statement this unit consumes (Forster 20.7 sufficiency, path form, `k ≤ g` points — filed
verbatim in the request file, with rationale):

```lean
theorem abel_sufficiency {n : ℕ} {a x : Fin n → X} (σ : ∀ j, Path (a j) (x j))
    (γ : Path (Classical.arbitrary X) (Classical.arbitrary X))
    (h : ∀ η : Form1 X, ∑ j, pathIntegral (σ j) η = period γ η) :
    ∃ f : ℳ X, f ≠ 0 ∧ RS.divisor f
      = ∑ j, (Function.locallyFinsuppWithin.single (x j) 1
              − Function.locallyFinsuppWithin.single (a j) 1)
```

**Load-bearing coordination point (the #29/#31 ordering question):** the blueprint's abel-theorem
blurb emphasizes the two-point application (`ofCurve_inj`), but Forster 20.7 — and this unit —
need the **n-point** sufficiency direction. A two-point-only Abel does NOT suffice for 21.4(b)
(the divisor there has up to `g` point pairs). Forster's §20 proof is uniform in the divisor, so
this costs #29 nothing extra; the request makes the dependency explicit *now*, while #29 is being
designed. Ordering is otherwise clean: Forster proves §20 before and independently of §21, and
nothing in this unit is needed by abel-theorem (no cycle; this unit stays strictly downstream).
Any statement equivalent up to the (paths ↔ chains ↔ `Div₀`) dictionary is fine — the bridge from
this unit's Stage C.2 data to whatever carrier #29 chooses is local and cheap on this side, as
long as (i) arbitrary finite `n`, (ii) hypothesis = equality of integrals against every
`η : Form1 X` (or just the `basis X` forms), (iii) conclusion = existence of `f ≠ 0` with divisor
exactly the alternating sum of `single`s.

Fallback if #29 slips entirely: none cheap — discreteness is genuinely Abel-gated (risk R1, §9).
Everything else in this unit (nondegeneracy, all plumbing, generic points, the Jacobi map, both
instances *modulo* the one `sorry`-shaped gate inside Stage C.3) can be built and compiled first,
so the unit's critical path through #29 is a single lemma application.

---

## 8. Discharge plumbing summary (final-assembly-facing)

1. `discreteTopology_periodSubgroup` (6.3 Stage D; g=0 branch subsingleton).
2. Λ closed: `AddSubgroup.isClosed_of_discrete` (mathlib, `[T2Space]`, to_additive of
   `Subgroup.isClosed_of_discrete`, `Topology/Algebra/IsUniformGroup/Basic.lean:273/293`;
   spike-verified for normed `V`).
3. `closure Λ = Λ`: `SetLike.coe_injective ∘ IsClosed.closure_eq` (spiked).
4. `instance DiscreteTopology (closure Λ)`: rewrite along 3 (spiked).
5. `instance IsZLattice ℝ (closure Λ).toIntSubmodule`: constructor `⟨span_top⟩` after
   `AddSubgroup.coe_toIntSubmodule` + rewrite along 3 (spiked); its `[DiscreteTopology]` class
   argument is found via 4 + jaccon's `discreteTopology_toIntSubmodule`.
6. jaccon's four gated challenge instances fire by instance search (their ledger; no code here).
7. Bonus rank-`2g` corollary via `ZLattice.rank` (mathlib, pin line 525).

---

## 9. Risks, ranked

* **R1 (HIGH, external): the abel-theorem gate.** Discreteness consumes #29's n-point sufficiency;
  #29 is being designed concurrently. Mitigated: request filed with the exact statement (§7);
  everything else here is gate-free; the consuming site is a single lemma application inside
  Stage C. If #29 lands two-point-only, escalate to the orchestrator — that is a blueprint-level
  gap, not something this unit can route around.
* **R2 (MEDIUM, external): canonical-forms/residue-theorem interface drift.** Stage C.5–6 consume
  `MForm.smul`/`ofForm1`/`resAt` and `residueTheorem` at their design-frozen signatures; both
  units are mid-build/mid-revision. Mitigated: consumption is confined to ~40 lines of Stage C;
  the needed `ord_smul`/`resAt_eq_zero_of_ord_nonneg` glue is flagged as Compat-able; drift is a
  rename risk, not a mathematical one.
* **R3 (MEDIUM, internal): Stage B derivative bookkeeping** (`HasStrictFDerivAt` of `𝔉` with the
  matrix CLM; `(mulVecLin A).toContinuousLinearMap.det = A.det` glue). Spiked at the pin (§11
  items 3–4): the IFT call, the det-nonzero equiv, and the analytic-⟹-strict path all compile;
  what remains is `Finset.sum`/`Pi` calculus, mechanical but fiddly (~80 lines).
* **R4 (LOW-MEDIUM, internal): the clopen identity lemma (6.4)** — chart-transport of "vanishing
  near" via `coeffIn_trans` needs care with sources/targets; the mathlib planar continuation lemma
  is pin-present. Fallback: canonical-forms D5 dichotomy (adds a gate but deletes the lemma).
* **R5 (LOW): max-principle step** — spiked end-to-end at the pin (§11 item 5), including the
  dichotomy name and the ε-shift contradiction; remaining work is the chart transport of the
  local max, standard filter algebra.
* **R6 (LOW): disjoint-neighborhood/radius bookkeeping** (Stage A, divisor values in Stage C.4) —
  elementary T2/topology, but a known time sink; isolate in small private lemmas.

## 10. Downstream

Final assembly (`Jacobian/Challenge.lean`): `import Jacobian.PeriodLattice` ⟹ challenge instances
at `docs/Jacobian_challenge.lean:78-89` all discharge via jaccon's ledger, and jaccon's gated
`ofCurve_contMDiff`/`inducedHom`/`contMDiff_inducedHom` become available at their bare challenge
signatures. No other unit consumes this one (it is a leaf of the DAG apart from final assembly).
`periodSubgroup_topologicalClosure_eq` is also exported for anyone (e.g. abel-theorem's
`ofCurve_inj` bridge, jaccon's `ofCurve_eq_of_path` consumers) who wants to strip the
`.topologicalClosure` from `Jac₀`'s defining quotient.

## 11. Spike results (`scratch_plr.lean`, gated per protocol, compiled clean at the pin)

1. `AddSubgroup.isClosed_of_discrete` exists additively, applies to a discrete
   `S : AddSubgroup (Fin 2 → ℂ)` in a normed space, and
   `SetLike.coe_injective isClosed.closure_eq : S.topologicalClosure = S` typechecks. ✓
2. `DiscreteTopology S.topologicalClosure` by rewriting along 1. ✓ ;
   `IsZLattice ℝ S.toIntSubmodule` from `⟨by rw [AddSubgroup.coe_toIntSubmodule]; exact hspan⟩`
   with the `[DiscreteTopology]` argument found by instance search (through jaccon-shaped bridge
   restated locally). ✓
3. `discreteTopology_iff_isOpen_singleton_zero` applies to the subgroup subtype; `{0} = ↑⁻¹' U`
   route compiles. ✓
4. IFT chain: `f' := (Matrix.mulVecLin A).toContinuousLinearMap`, `A.det ≠ 0` ⟹
   `f'.toContinuousLinearEquivOfDetNeZero`, coe-equality by `ContinuousLinearMap.ext` +
   `toContinuousLinearEquivOfDetNeZero_apply`, then `HasStrictFDerivAt.map_nhds_eq_of_equiv`. ✓
   (det glue: `ContinuousLinearMap.det` unfolds to `LinearMap.det (mulVecLin A)` =
   `A.det` via `Matrix.det_toLin'`/`mulVecLin`-toLin' defeq — exact rewrite recorded in spike.)
5. Max-principle kernel: `AnalyticAt.eventually_constant_or_nhds_le_map_nhds` + the
   `g z + ε/2`-shift contradiction ⟹ `IsLocalMax (Re ∘ g) z → ∀ᶠ w, g w = g z`. ✓

(Exact line-by-line contents kept in `scratch_plr.lean` at the project root for the builder.)
