# Design: abel-theorem (`Jacobian/Abel/`)

Blueprint unit **abel-theorem** (#29). Blueprint text: "Abel's theorem (Forster 20.7,
dissection-free): the two-point Abel–Jacobi value is nonzero for distinct points on `g ≥ 1`, hence
`ofCurve` is **injective**. Strategy: if `AJ(P)=AJ(Q)` then there is a meromorphic function with
divisor `P−Q`, i.e. a degree-1 map ⇒ `g=0`, contradiction. Use Forster's dissection-free
formulation (no fundamental-polygon machinery). ⚠ Avoid the cut-surface/dissection route."
Declared **Builds on:** abel-weak-solutions, cech-h1-genus. Consumer: **period-lattice-rank**
(#31) + the challenge's `Jacobian.ofCurve_inj`. Read in full: Forster §20.7 proof (PDF 169–170,
book 163–164), §20.6 statement (for context only — not used), §21.1–21.4 (PDF 172–176, book
166–170, in full, to settle the ordering question), `docs/design/abel-weak-solutions.md`
(AUTHORITATIVE for its own frozen exports), `Jacobian/JacobianConstruction/{Basic,OfCurve,
Periods}.lean` (BUILT, read at source).

---

## 0. Verdict up front

**The blueprint's DAG order (`abel-theorem` before `period-lattice-rank`) is mathematically
forced, not a formalization accident**: Forster's own proof of period-lattice discreteness
(Thm 21.4(b), PDF 169) literally invokes "By Abel's Theorem there exists a meromorphic function
`f`..." — so period-lattice-rank cannot be built first. The `closure(Λ)` vs `Λ` gap the task
brief worries about is real but is a **consequence of a design choice already made and already
correct** in the built `jacobian-construction` unit (it quotients by `Λ.topologicalClosure`,
not `Λ`, because the challenge demands `T2Space (Jacobian X)` **unconditionally**, even at
`genus X = 0` where `Λ = {0}` trivially and no discreteness fact is available yet). Forster
himself never needs the closure operation at all: `Per(ω)` stays a bare algebraic subgroup
throughout §20–21, and `Jac(X) := ℂ^g/Per(ω)` is only ever formed in §21.6, *after* discreteness
(hence closedness) is already in hand. Our formalization needs the quotient **before** that,
so it pays for it with the closure trick; this unit's job is to prove everything **about the raw
algebraic `RS.periodSubgroup X`** (matching Forster's own development, and exactly what
period-lattice-rank's Forster-21.4-shaped proof consumes), and to export the challenge-shaped
`ofCurve_inj` **gated** on the one bridge fact (`closure Λ = Λ`) that only period-lattice-rank can
supply — discharged by a three-line mathlib fact (`AddSubgroup.isClosed_of_discrete`, spiked
§9) the moment period-lattice-rank lands. No fundamental-polygon/cut-surface machinery is used
anywhere (the blueprint's ⚠ is honored).

**A second, sharper finding, not anticipated by the task brief**: Forster 21.4(b)'s own
"By Abel's Theorem" step is **not** the two-point case — it needs a meromorphic function with
*up to `g` simultaneous* simple poles/zeros (a general degree-0 point-divisor), because the
point `t ∈ Γ ∩ W` it rules out can have anywhere from `1` to `g` coordinates `x_j ≠ a_j`. The
blueprint's one-line blurb ("two-point Abel–Jacobi value") undersells what `abel-theorem` must
actually export for `period-lattice-rank` to work at all. The fix is cheap: Forster's own
Lemma 20.1 ("weak solutions of `D₁`, `D₂` multiply to a weak solution of `D₁+D₂`") means the
finite-point case is a **verbatim product/sum iteration of the two-point machinery**, no new
mathematical idea — §1.4 and §5 below build it as a thin `Finset`-indexed generalization sitting
on top of the two-point proof. This is recorded as a **scope correction** to the blueprint's
one-line description and to `abel-weak-solutions.md` §1.4/§8's claim that the general-chain
case "is real content, but... no current consumer needs [it]" — `period-lattice-rank` **is**
such a consumer, and it needs it now, not as a hypothetical future extension.

**DAG audit**: `abel-weak-solutions` is genuinely essential (its weak-solution engine, exactly as
frozen). `cech-h1-genus` is **dropped** — the one analytic fact this unit needs from "the
Serre-duality side" (a Dolbeault-solvability/vanishing-pairing criterion, Forster's own citation
`(19.10)`, which is Hodge-theoretic and routing-decision-#3-forbidden) is available **directly**
by composing three *other* units' frozen exports — `canonical-forms` (BUILT: `holomorphicMFormsEquiv`,
`genus_eq_finrank_omegaSpace_zero`), `serre-duality-tails` (designed, not built: `resEquiv`,
`i_neg_eq_h1`), and `dolbeault-comparison` (partially built — `Leray.lean` only; `Comparison.lean`
designed, not built: `H01`, `dolbeaultEquiv`, `exists_dbar_eq_iff`) — with **no** further content
from a dedicated `cech-h1-genus` unit (whose blueprinted deliverable, `dim H¹(X,𝒪)=g`, is *already*
`serre-duality-tails`'s own `h1_zero_eq_genus` export; a redundant edge, matching this project's
established pattern of DAG-audit corrections). `form-trace-tower` is **not needed at all** (not
even for Forster's "necessity" direction) — the necessity half this unit actually needs (`∃f` with
one prescribed simple pole `⟹ genus X = 0`) is already fully discharged by two **built, zero-sorry**
units (`Jacobian.ProperDegree`'s `RS.homeoSphere_of_exists_simple_pole` +
`Jacobian.SphereTopology`'s `RS.SphereTopology.genus_eq_zero_of_homeo_sphere`), sidestepping
Forster's general `Trace(ω)`-on-`ℙ¹` necessity construction entirely.

**Biggest schedule risk, stated honestly**: the "Dolbeault-upgrade bridge" (§4.3) is the one place
this unit's own new content depends on two units that are designed but **not yet built**
(`serre-duality-tails`, `dolbeault-comparison/Comparison.lean`). Everything else in this design
(the loop-cancellation algebra, the weak-solution product, the CR-converse promotion, the
genus-0 shortcut, the gated `ofCurve_inj` assembly) depends only on **already-built, zero-sorry**
units and is immediately buildable.

---

## 1. THE ORDERING RESOLUTION (FROZEN)

### 1.1 What the built substrate actually says (read at source)

`Jacobian/JacobianConstruction/Basic.lean:54`: `abbrev Jac₀ : Type := (Fin (genus X) → ℂ) ⧸
(periodSubgroup X).topologicalClosure` — the quotient is by the **closure**, unconditionally, for
every `X` including `genus X = 0`. The file's own docstring explains why: `T2Space (Jacobian X)`
is a challenge-mandated **unconditional** instance (`docs/Jacobian_challenge.lean:75`, no
hypotheses), and quotienting a Hausdorff topological group by a subgroup is Hausdorff **iff the
subgroup is closed** — so `jacobian-construction` (built long before period-lattice-rank exists)
had no choice but to close `Λ := RS.periodSubgroup X` first. `Jacobian.ofCurve_inj`'s honest
unfolding (`OfCurve.lean:64-89`, `ofCurve` defined via `ULift.up (QuotientAddGroup.mk ...)`,
well-definedness proved via `QuotientAddGroup.eq_iff_sub_mem` + `(periodSubgroup X)
.topologicalClosure.neg_mem`/`AddSubgroup.le_topologicalClosure`) is therefore genuinely a
statement about **`closure Λ`**, not `Λ`.

### 1.2 What Forster actually needs, and where it needs it (read in full)

Forster's own text (book 159–170, PDF 165–176) **never once takes a topological closure of
`Per(ω)`**. The logical order is:

1. **§20.7 (Abel's Theorem, book 163–164)** is proved for the bare algebraic condition "there is a
   chain `c` with `∂c=D` and `∫_c ω=0` for every `ω∈Ω(X)`" — no topology on `Per(ω)` is mentioned
   or needed; `Per(ω)` is not even *defined* until §21.2, one section later.
2. **§21.3–21.4 (book 168–170)**: `Per(ω) =: Γ` is defined (§21.2) and its two lattice properties
   — (i) **discreteness** and (ii) **full rank** — are proved. The discreteness proof (21.4(b))
   reads verbatim (PDF 169, transcribed exactly): *"Renumbering, if necessary, we may assume
   `x_j ≠ a_j` for `1 ≤ j ≤ k` and `x_j = a_j` for `j > k`... **By Abel's Theorem** there exists a
   meromorphic function `f` on `X` which has a pole of first order at `a_j`, `1 ≤ j ≤ k`, and a
   zero of first order at `x_j`, `1 ≤ j ≤ k`, and is holomorphic otherwise... `0 = Res(fω_i) =
   Σ_{j=1}^k c_j φ_ij(a_j)`... But this is not possible since the matrix `(φ_ij(a_j))` has rank
   `g`."* This is an **unconditional, direct citation** of 20.7's sufficiency direction, applied to
   the point `t = F(x) ∈ Γ ∩ W` that discreteness must rule out.
3. **Only after** discreteness (hence, in a Hausdorff topological group, closedness — a subgroup
   that is discrete *as a subspace* is automatically a *closed* subset, mathlib:
   `AddSubgroup.isClosed_of_discrete`, spiked §9) is `Jac(X) := ℂ^g/Per(ω)` formed (§21.6) — by
   which point `Per(ω) = Per(ω).topologicalClosure` for free, so the distinction this task worries
   about never surfaces in Forster's own book at all.

**Conclusion on option (b) of the task brief: REFUTED.** Discreteness (21.3–21.4) is emphatically
**not** independent of Abel's theorem — it is proved *using* Abel's theorem's sufficiency
direction, in the same section, one theorem later. No reordering of the blueprint's declared edges
(`abel-theorem` before `period-lattice-rank`) is possible or desirable; the blueprint's order
already matches Forster's own logical dependency exactly.

### 1.3 The frozen resolution: options (a)+(c) merged, informed by 1.2's finding

Since discreteness cannot come first, and our `Jacobian X` is *already* built on `closure Λ`
(a decision this unit does not revisit — it is forced by the challenge's unconditional `T2Space`
requirement, §1.1), the only sound path is:

* **abel-theorem proves everything in terms of the literal, uncompleted `RS.periodSubgroup X`**
  (no closure anywhere in its own statements) — this is *exactly* what Forster's text does, and
  exactly what `period-lattice-rank`'s Forster-21.4-shaped proof needs to consume (§1.2 point 2).
  This is the unit's **primary export**: `RS.Abel.exists_mero_of_periodVector_mem` (§4.1/§5, the
  general finite-point sufficiency direction) plus its genus-0 corollary.
* **abel-theorem also derives the challenge-shaped `Jacobian.ofCurve_inj`, but GATED** on the one
  hypothesis that bridges `closure Λ` to `Λ`: `[DiscreteTopology (RS.periodSubgroup X)]` (Forster
  21.4(i), the literal, un-closed subgroup). This is **exactly** the gating idiom already
  established by `jacobian-construction` itself (`Jacobian.ofCurve_contMDiff`,
  `Jacobian.instChartedSpace`, etc. are all gated the same way, on
  `[DiscreteTopology (RS.periodSubgroup X).topologicalClosure]` — a closely related but not
  identical hypothesis, reconciled in §4.4). The **statement** of `ofCurve_inj` needs no such
  instance to typecheck (unlike `ofCurve_contMDiff`, which needs a `ChartedSpace` instance on the
  codomain) — only its **proof** does, so the gate costs nothing extra at the call site once
  discharged.
* **Final assembly (or `period-lattice-rank` itself, the moment it registers
  `instance : DiscreteTopology (RS.periodSubgroup X)` for a real `X`)** discharges the gate by
  instance search, producing the literal ungated `Jacobian.ofCurve_inj` matching
  `docs/Jacobian_challenge.lean:99` exactly. This is a **one-line wrapper**, not new mathematics
  (§4.4, §8).

This is the FROZEN design. It costs nothing extra in proof effort (the gated and ungated
statements have the *same* proof, modulo one `rw` through the bridge fact) and it means
`abel-theorem` can be built to completion **right now**, without waiting for
`period-lattice-rank`, exactly matching the blueprint's stated build order.

### 1.4 The general-point-count correction (not anticipated by the task brief)

Forster 21.4(b)'s divisor has support size `k` for *any* `1 ≤ k ≤ g` (renumbering lets `k` be as
small as `1`, matching our two-point case, or as large as `g`). `abel-weak-solutions.md` §1.4
explicitly declines to build the general chain/cycle bookkeeping of Forster §20.4, on the grounds
that "no current consumer needs [it]" beyond the two-point case. **This is now known to be false**:
`period-lattice-rank` is a real, blueprint-declared consumer (`Builds on: abel-theorem`) that
needs the `k`-point case for every `1 ≤ k ≤ g`. The fix does **not** require building Forster's
general `C₁(X)/Z₁(X)/H₁(X)` machinery (formal `ℤ`-linear combinations of curves, homology) — it
only requires the *degenerate, already-disjoint* case Forster 21.4(a) itself sets up: `k` **pairwise
disjoint** two-point pieces, each already a `Path (a i) (x i)` living inside its own chart
neighborhood, with no shared endpoints. Forster's own Lemma 20.1 ("weak solutions of `D₁, D₂`
multiply to a weak solution of `D₁+D₂`") is the only "general chain" content genuinely used, and it
is a **verbatim finite product** of `abel-weak-solutions`'s already-built two-point weak solution —
no new idea, see §4.1/§5.2.

---

## 2. Forster 20.7, transcribed into our vocabulary (both directions)

Two-point case first (`k = 1`; the general `k`-point case, §4.1, is the identical argument run
`k` times and combined additively/multiplicatively — nothing below changes).

### 2.1 Sufficiency (`(*) ⟹ ∃` solution) — the hard direction, THIS unit's main content

Forster's chain-level condition `(*)` (§20.7's Remark, PDF 169: "If `γ` is an arbitrary 1-chain
with `∂γ=D`... there exists a cycle `α`... such that `∫_γ ω_j = ∫_α ω_j`") becomes, for a *fixed*
path `δ : Path Q P` (`Q` the prospective pole, `P` the prospective zero — matching
`abel-weak-solutions`'s own `(P,Q)` convention): **the vector
`(fun i => RS.pathIntegral δ (RS.basis X i))` lies in `RS.periodSubgroup X`** (the literal,
uncompleted algebraic subgroup — no closure). Proof pipeline (all steps below are either already
built or are this unit's own new content, marked):

1. **[NEW, §4.2, cheap]** Unfold membership in `RS.periodSubgroup X` (`AddSubgroup.closure` of the
   range of `RS.periodVector (RS.basis X)` over based loops at a fixed point `x₀`) down to a
   *single* based loop `α : Path x₀ x₀` with `periodVector (basis X) α` exactly equal to the
   target vector — because the generating set (based-loop period vectors) is *already* closed
   under `+`/`neg`/`0` (`RS.periodVector_trans/_symm/_refl`, **built**,
   `Jacobian/Path/Periods.lean:55-68`), so `AddSubgroup.closure` of it adds nothing: every element
   of the closure is already `periodVector (basis X)` of *some* single loop (proved by
   `AddSubgroup.closure_induction`, combining sub-loops via `.trans`/`.symm`, mirroring exactly how
   `periodVector_mem_periodSubgroup` (**built**, `OfCurve.lean:46-55`) already proves the reverse
   inclusion).
2. **[NEW, §4.2, cheap]** Conjugate `α` (based at `x₀`) to a loop `β` based at `Q` with the *same*
   period, via `RS.period_conj` (**built**, `Jacobian/Path/Periods.lean:45-48`) and
   `PathConnectedSpace.somePath Q x₀` (available: `LocPathConnectedSpace X`/`PathConnectedSpace X`
   instances are **built**, `OfCurve.lean:36-39`).
3. **[NEW, §4.2, cheap]** Set `δ' := β.symm.trans δ : Path Q P`. By `RS.pathIntegral_trans/_symm`
   (**built**, `Path/Continuation.lean:187-236`) and linearity of `RS.pathIntegralₗ`
   (**built**, `:334`) checked on the basis then extended by `Module.Basis.ext`/linearity:
   `RS.pathIntegral δ' ω = 0` for **every** `ω ∈ Form1 X`, matching Forster's own Remark
   ("only needs to be checked for a basis") exactly.
4. **[abel-weak-solutions, cited verbatim]** `RS.AbelWeak.exists_weakSolutionOfPair (hQP :
   Q ≠ P) δ'` gives `f : X → ℂ`, `U`, `RS.AbelWeak.IsWeakSolutionOfPair f P Q`, `IsOpen U`,
   `IsCompact (closure U)`, `Set.range δ' ⊆ U`, `∀ x ∉ U, f x = 1`.
5. **[abel-weak-solutions, cited verbatim, §7.3]** Package `f`'s chart-local log-derivative data
   (`logDerivCoeff`, built per-chart) into ONE global `η : RS.Form01 X` (**this unit's own
   packaging step**, §4.3 D1 — `abel-weak-solutions` explicitly does *not* build a global object,
   D5) and use the residue identity (§7.3 of `abel-weak-solutions.md`) plus step 3's *exact*
   vanishing (not just of the basis integral, but chart-piece by chart-piece) to show: **`η`
   pairs to zero against every `ω ∈ Ω(X)`** (in the residue/Serre-pairing sense, §4.3).
6. **[NEW, §4.3, the unit's hardest content, HIGH RISK]** By the Dolbeault-upgrade bridge (the
   `canonical-forms` + `serre-duality-tails` + `dolbeault-comparison` composite, §4.3): `η` pairs
   to zero against every `ω ∈ Ω(X)` `⟹` `η` is `d''`-exact, i.e. `∃ g : RS.SmoothC X,
   RS.dbar g = η` — the project's PDE-free substitute for Forster's own citation `(19.10)`
   (Hodge-theoretic, routing-decision-#3-forbidden).
7. **[NEW, §4.2, mechanical]** `F := fun z => Complex.exp (-(g' z)) * f z` (`g'` the underlying
   function of `g : SmoothC X`) satisfies `d''F = 0` pointwise off `Q`
   (`wirtingerDbar`-product-rule computation, `d''g = d''f/f` cancels exactly as in Forster's own
   text) — hence, by the **built** CR-converse `RS.differentiableAt_of_wirtingerDbar_eq_zero`
   (`Jacobian/Dbar/Wirtinger.lean:125-126`, chart-transported via
   `wirtingerDbar_comp_differentiableAt`), `F` is genuinely `MeromorphicOnX` on all of `X`, with
   local order matching `f`'s known weak-solution model exactly (multiplying by the smooth,
   nowhere-zero unit `Complex.exp (-(g' ·))` changes no order anywhere). Package
   `F' := MeroGermOn.mk F hF : RS.ℳ X`. **This is the honest, non-cheating meromorphic solution**
   — no junk values, no vacuous instance, real analytic content at every step.

### 2.2 Necessity (`∃` solution `⟹` genus 0), only as much as is actually needed

Forster's own necessity direction (20.7(b), the `Trace(ω)` construction on `ℙ¹`) is **not built
here** — not needed by any current consumer. What `ofCurve_inj` needs is *strictly weaker*: not
"`∃F ⟹ (*)`" but "`∃F` with exactly one simple pole `⟹ genus X = 0`" — already **fully built**,
zero sorries, by two other units:

```
RS.homeoSphere_of_exists_simple_pole (φ : ℳ X) (Q : X) (hpole : φ.ord Q = -1)
    (hreg : ∀ x, x ≠ Q → 0 ≤ φ.ord x) :
    Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    -- Jacobian/ProperDegree/GenusZeroFinisher.lean:32
RS.SphereTopology.genus_eq_zero_of_homeo_sphere
    (h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) : genus X = 0
    -- Jacobian/SphereTopology/Headline.lean:27
```
Composed directly: `F'` from §2.1 step 7 has `F'.ord Q = -1`, `∀x≠Q, 0 ≤ F'.ord x` (order `+1` at
`P`, order `0` everywhere else) `⟹ Nonempty (X ≃ₜ S²) ⟹ genus X = 0`. **`form-trace-tower` is not
imported anywhere in this unit.**

---

## 3. DAG audit (dependencies actually consumed)

| Declared / candidate dependency | Verdict | Why |
|---|---|---|
| **abel-weak-solutions** | **Essential**, used exactly as frozen: `exists_weakSolutionOfPair`, `IsWeakSolutionOfPair`, `pathIntegral_eq_sum_chartChain`, the §7.3 residue identity. | The weak-solution engine; nothing here duplicates it. |
| **cech-h1-genus** | **Dropped.** | Its blueprinted deliverable (`dim H¹(X,𝒪)=g`) is already `serre-duality-tails`'s own `h1_zero_eq_genus` (composing `i_neg_eq_h1` at `D=0` with `canonical-forms`' `genus_eq_finrank_omegaSpace_zero`, **both already covering this**). The fact *this* unit actually needs (Dolbeault-solvability from a vanishing pairing) is not what `cech-h1-genus`'s one-line blurb describes at all (that blurb is a dimension count, Forster §17.4–17.5/Miranda Ch. X §2 — Serre duality bookkeeping, not a `d''`-exactness criterion) — composing `canonical-forms` + `serre-duality-tails` + `dolbeault-comparison` directly supplies exactly what is needed (§4.3), with no separate unit required. |
| **form-trace-tower** | **Not needed at all** (not even transitively). | Necessity is only ever used in the specific "one simple pole" shape, already discharged by `proper-map-degree`/`sphere-topology` (§2.2). `abel-weak-solutions.md`'s own DAG audit already found this unit does not need `form-trace-tower` either; this unit independently confirms the same for its own necessity-direction use. |
| **canonical-forms** | **Essential** (new edge; not in blueprint's declared list, but load-bearing). | `MForm.OmegaSpace`, `i`, `holomorphicMFormsEquiv`, `genus_eq_finrank_omegaSpace_zero` — all **built** — are half of the Dolbeault-upgrade bridge (§4.3). |
| **serre-duality-tails** | **Essential** (new edge). | `resEquiv`/`i_neg_eq_h1` at `D=0` are the other half of the bridge (§4.3). **Designed, not yet built** — the unit's #1 schedule risk (§7 R1). |
| **dolbeault-comparison** | **Essential** (new edge, partially available). | `Leray.lean` (**built**) is not used directly; `Comparison.lean`'s `H01`/`dolbeaultEquiv`/`exists_dbar_eq_iff` (**designed, not built**) are the bridge's entry point from the concrete `Form01 X η` this unit constructs. Second-biggest schedule risk (§7 R1). |
| **dbar-solvability** | **Essential** (new edge; already built). | `RS.SmoothC X`, `RS.dbar`, `RS.differentiableAt_of_wirtingerDbar_eq_zero`/`wirtingerDbar_comp_differentiableAt` (the CR-converse promotion, §2.1 step 7). |
| **meromorphic-and-divisors** | **Essential** (new edge; already built). | `RS.ℳ X`, `MeroGermOn.mk`, `.ord`, `MeromorphicOnX` — packaging `F` as an honest `ℳ X` element. |
| **proper-map-degree, sphere-topology** | **Essential** (new edges; already built). | §2.2's genus-0 shortcut. |
| **monodromy** | **Not needed.** | Nothing here operates on a genuine `ℳ X` before it exists; the loop-cancellation algebra (§2.1 steps 1–3) is pure `Path`/`AddSubgroup` bookkeeping, no monodromy/continuation machinery. |

**Recommended blueprint correction**: `abel-theorem`'s `Builds on:` line should read
`abel-weak-solutions, canonical-forms, serre-duality-tails, dolbeault-comparison,
dbar-solvability, meromorphic-and-divisors, proper-map-degree, sphere-topology` (dropping
`cech-h1-genus`). Filed as a coordination note (§8), matching the project's established practice
of flagging rather than editing `clean_room_blueprint.md` directly.

---

## 4. Core definitional decisions

Namespace `RS.Abel` for internal lemmas; `Jacobian` namespace (matching `OfCurve.lean`) for the
challenge-shaped final exports. Standing variables as in `CONVENTIONS.md`.

### 4.1 D1 — the general finite-point sufficiency theorem (§1.4's correction, built first)

```lean
namespace RS.Abel

/-- **Forster 20.7, sufficiency direction, `k`-point form** (the shape `period-lattice-rank`'s
own Thm 21.4(b) argument needs — `k` ranges over every `1 ≤ k ≤ g` there). `a`/`x` are the
prospective poles/zeros (order `-1`/`+1`), assumed pairwise distinct as a set of `2·|ι|` points
(discharged automatically in 21.4's own application by its disjoint-chart construction, §1.4);
`γ i : Path (a i) (x i)` is a chosen connecting path for each pair; the hypothesis is that the
*total* period vector (summed over the chain `∑ᵢ γ i`) lies in the literal, uncompleted
`RS.periodSubgroup X`. -/
theorem exists_mero_of_periodVector_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a x : ι → X) (ha : Function.Injective a) (hx : Function.Injective x)
    (hax : ∀ i j, a i ≠ x j) (γ : (i : ι) → Path (a i) (x i))
    (hmem : (fun k => ∑ i, RS.pathIntegral (γ i) (RS.basis X k)) ∈ RS.periodSubgroup X) :
    ∃ F : RS.ℳ X, F ≠ 0 ∧ (∀ i, F.ord (x i) = 1) ∧ (∀ i, F.ord (a i) = -1) ∧
      ∀ z, (∀ i, z ≠ a i) → (∀ i, z ≠ x i) → F.ord z = 0

/-- The `k = 1` (`ι := Unit`) specialization — the blueprint's literal "two-point" statement,
matching `abel-weak-solutions`'s `(P, Q)` convention (`x () = P`, `a () = Q`). -/
theorem exists_mero_of_pathIntegral_mem {P Q : X} (hPQ : Q ≠ P) (δ : Path Q P)
    (hmem : (fun k => RS.pathIntegral δ (RS.basis X k)) ∈ RS.periodSubgroup X) :
    ∃ F : RS.ℳ X, F ≠ 0 ∧ F.ord P = 1 ∧ F.ord Q = -1 ∧ ∀ z, z ≠ Q → z ≠ P → F.ord z = 0

end RS.Abel
```

**Proof plan for `exists_mero_of_pathIntegral_mem` (~120 lines, the two-point case, built out in
full — the numbered steps of §2.1):**

1. `mem_periodSubgroup_iff_exists_loop` (Compat, request filed to `jacobian-construction`'s
   `Periods.lean` — see §4.2): `hmem` unfolds to `∃ α : Path x₀ x₀, periodVector (basis X) α =
   fun k => pathIntegral δ (basis X k)` where `x₀ := Classical.arbitrary X` (`periodSubgroup`'s own
   fixed basepoint).
2. Conjugate: `β := (σ.trans α).trans σ.symm : Path Q Q` where `σ := PathConnectedSpace.somePath
   Q x₀`; `RS.period_conj σ α (basis X k) : period β (basis X k) = period α (basis X k)` for
   every `k`.
3. `δ' := β.symm.trans δ : Path Q P`; `RS.pathIntegral_trans`/`_symm` give `pathIntegral δ' (basis
   X k) = -period β (basis X k) + pathIntegral δ (basis X k) = 0` for every `k`; extend to every
   `ω : Form1 X` via `RS.pathIntegralₗ` linear + `Module.Basis.ext` (a linear map vanishing on a
   basis is the zero map).
4. `⟨f, U, hf, hUo, hUc, hUr, hU1⟩ := RS.AbelWeak.exists_weakSolutionOfPair hPQ δ'`.
5. Package `η : Form01 X` from `f`'s local log-derivative data (§4.3 D1) and show (via `δ'`'s
   *exact* vanishing from step 3, chart-piece by chart-piece via `abel-weak`'s
   `pathIntegral_eq_sum_chartChain` + §7.3 residue identity, run against **each** basis form
   `basis X i`) that `η` pairs to zero against every `basis X i`, hence (linearity of the pairing,
   `RS.SerrePairing`-style) against every `ω ∈ Ω(X)`.
6. `⟨g, hg⟩ := RS.Abel.exists_dbar_eq_zero_of_forall_omega_pairing_eq_zero hη` (§4.3 D3, the
   bridge).
7. `F := fun z => Complex.exp (-(g z)) * f z`; `wirtingerDbar_eq_zero` computation (§4.2 D2);
   promote via `differentiableAt_of_wirtingerDbar_eq_zero` chart-transported; package
   `MeroGermOn.mk F hF`; order computations at `P`, `Q`, and elsewhere from `f`'s known local
   models (`IsWeakSolutionAt`) multiplied by the nowhere-zero smooth unit `Complex.exp (-(g ·))`.

`exists_mero_of_periodVector_mem` (the `k`-point case) reruns steps 4–7 **once per `i : ι`**
(`f := ∏ i, f i`, a `Finset.prod`, well-defined pointwise since the `2|ι|` points are pairwise
distinct so no two factors interact locally) and step 5–6 **once**, with `η := ∑ i, η i` (the
`Form01 X` module's own addition) — Forster's Lemma 20.1 multiplicativity, no new proof idea,
~80 lines of `Finset`-bookkeeping on top of the two-point machinery.

### 4.2 D2 — Compat lemmas needed (small, low-risk, filed as requests where upstream-owned)

```lean
/-- Compat (request filed to `jacobian-construction`'s `Periods.lean`, §8): `periodSubgroup`'s
generating set is already closed under `+`/`neg`/`0` (via `periodVector_trans/_symm/_refl`), so
`AddSubgroup.closure` adds nothing — every element is `periodVector` of a single based loop. -/
theorem RS.mem_periodSubgroup_iff_exists_loop {v : Fin (genus X) → ℂ} :
    v ∈ RS.periodSubgroup X ↔
      ∃ α : Path (Classical.arbitrary X) (Classical.arbitrary X), RS.periodVector (RS.basis X) α = v

/-- The `d''F = 0` computation underlying the meromorphic promotion (`Compat`, this unit,
`WeakToMero.lean`): a direct `wirtingerDbar`-product-rule identity, chart-local. -/
theorem RS.Abel.wirtingerDbar_exp_neg_mul_eq_zero {u f : ℂ → ℂ} {z : ℂ}
    (hu : DifferentiableAt ℝ u z) (hf : DifferentiableAt ℝ f z)
    (h : wirtingerDbar u z = wirtingerDbar f z / f z) (hfz : f z ≠ 0) :
    wirtingerDbar (fun w => Complex.exp (-(u w)) * f w) z = 0
```
Both are short (`mem_periodSubgroup_iff_exists_loop`: `AddSubgroup.closure_induction` with three
cases mirroring `.trans`/`.symm`/`.refl`, ~20 lines; the `wirtingerDbar` identity: product/chain
rule via `wirtingerDbar_add`/`_const_mul` plus `Complex.exp`'s own derivative, `field_simp`, ~15
lines) — flagged LOW risk (§7 R4).

### 4.3 D3 — the Dolbeault-upgrade bridge (the unit's hardest, highest-risk content)

**Statement needed** (packaging `canonical-forms` + `serre-duality-tails` + `dolbeault-comparison`
into one usable fact; this is a NEW lemma, owned and proved here, `DolbeaultBridge.lean`):

```lean
namespace RS.Abel

/-- **The Forster-19.10 substitute** (routing decision #3 honored: no harmonic theory, no
Hodge `*`-operator — a pure finite-dimensional-linear-algebra consequence of `resEquiv` being a
linear EQUIVALENCE, composed with `dolbeaultEquiv`). If a smooth global `(0,1)`-form `η` pairs to
zero (via the residue/Serre pairing, concretely: its image class in `RS.H1 (0 : Divisor X)` pairs
to zero against `resMap`'s image of every `ω ∈ Ω(X)`) against a BASIS of `Form1 X`, then `η` is
`d''`-exact. -/
theorem exists_dbar_eq_zero_of_forall_basis_pairing_eq_zero {η : RS.Form01 X}
    (h : ∀ i : Fin (genus X),
      RS.pairT (RS.MForm.ofForm1 (RS.basis X i)) (mem_omegaSpace…)
        (RS.H1Tail.equiv.symm (RS.dolbeaultEquiv.symm (RS.H01.mk η))) = 0) :
    ∃ u : RS.SmoothC X, RS.dbar u = η

end RS.Abel
```

**Proof plan (~90 lines once `serre-duality-tails`/`dolbeault-comparison/Comparison.lean` land;
0 lines buildable today — HIGH RISK, §7 R1):**

1. `holomorphicMFormsEquiv : Form1 X ≃ₗ[ℂ] MForm.OmegaSpace (0 : Divisor X)` (**canonical-forms,
   built**) identifies a basis of `Form1 X` with a basis of `OmegaSpace 0`.
2. `resEquiv 0 : ↥(MForm.OmegaSpace (-0)) ≃ₗ[ℂ] Module.Dual ℂ (H1Tail 0)` (**serre-duality-tails,
   designed**, `-0 = 0` so this is exactly `OmegaSpace 0 ≃ Dual (H1Tail 0)`) composed with
   `H1Tail.equiv : H1Tail 0 ≃ₗ Cech.H1 0` (**laurent-tails, designed**) gives `Θ : Form1 X ≃ₗ[ℂ]
   Dual (RS.H1 (0 : Divisor X))` — a PERFECT PAIRING between global holomorphic forms and the
   Čech-dual, both finite-dimensional (`genus X`).
3. `dolbeaultEquiv : RS.H1 (0 : Divisor X) ≃ₗ[ℂ] RS.H01 X` (**dolbeault-comparison, designed**)
   transports `Θ` to `Θ' : Form1 X ≃ₗ[ℂ] Dual (RS.H01 X)`.
4. `h`'s hypothesis (pairing to zero against a basis) plus `Θ'`'s **surjectivity** (it is a linear
   equivalence, hence bijective) implies `H01.mk η` pairs to zero against **every** functional in
   `Dual (RS.H01 X)` — a standard finite-dimensional fact (the canonical evaluation map into the
   double dual is injective for any vector space over a field; mathlib name TBD at build time,
   e.g. via `Basis.ext`/`Subspace.dual_eq_bot_iff`-style lemma on `RS.H01 X`'s own `Module.finBasis`,
   using `finiteDimensional_H01` from `dolbeault-comparison`) — hence `H01.mk η = 0`.
5. `RS.H01.mk_eq_zero_iff` (**dolbeault-comparison, designed**: `H01.mk ω = 0 ↔ ∃ u : SmoothC X,
   dbar u = ω`) closes it directly. (`exists_dbar_eq_iff` is an equally usable, slightly more
   general packaging of the same fact — either works; `mk_eq_zero_iff` needs no auxiliary `ξ`.)

**The residue-pairing side of `h`'s hypothesis** (connecting `η` — built from `abel-weak`'s
`logDerivCoeff` chart data, §5.1 — to `pairT`'s abstract residue formula) is exactly
`abel-weak-solutions.md` §7.3's residue identity, run once per basis element; no new integration
atom is needed beyond what `abel-weak-solutions`/`planar-stokes-atoms` already ship (including the
`hconst`-refinement flagged there as risk R1 — inherited here, not re-derived).

### 4.4 D4 — the gated `ofCurve_inj` and the final-assembly discharge

```lean
namespace Jacobian

/-- **The challenge lemma, gated** on the literal (uncompleted) period subgroup's discreteness
— Forster 21.4(i) exactly, NOT the `.topologicalClosure` variant `jacobian-construction`'s other
gated instances use (reconciled below). -/
theorem ofCurve_inj' (P : X) (h : 0 < genus X) [DiscreteTopology (RS.periodSubgroup X)] :
    Function.Injective (ofCurve P) := by
  intro x y hxy
  by_contra hne
  -- `hxy : ofCurve P x = ofCurve P y` unfolds (ULift.up.injEq, QuotientAddGroup.eq_iff_sub_mem)
  -- to `(fun i => pathIntegral (somePath P x) (basis X i))
  --       - (fun i => pathIntegral (somePath P y) (basis X i)) ∈ (periodSubgroup X).topologicalClosure`
  -- which, via `(periodSubgroup X).topologicalClosure = periodSubgroup X`
  -- (`AddSubgroup.isClosed_of_discrete` + `IsClosed.closure_eq`, spiked §9), becomes membership
  -- in the literal `periodSubgroup X`.
  -- Set `τ := (somePath P x).symm.trans (somePath P y) : Path x y`; the difference above equals
  -- `-(fun i => pathIntegral τ (basis X i))` (the same `pathIntegral_trans`/`_symm` algebra
  -- `ofCurve_eq_of_path`'s own proof already uses).
  -- `RS.Abel.exists_mero_of_pathIntegral_mem hne.symm τ (this) : genus X = 0` (§2.2's shortcut,
  -- inlined) contradicts `h`.
  sorry -- (design-stage placeholder; full ~40-line proof at build time)

/-- **The literal challenge statement** (`docs/Jacobian_challenge.lean:99`), discharged the
moment `period-lattice-rank` registers `instance : DiscreteTopology (RS.periodSubgroup X)`
for the real period subgroup (Forster 21.4(i)). A one-line wrapper, not new mathematics — lives
in final assembly (or in `period-lattice-rank`'s own root file, alongside the instance it
registers). -/
theorem ofCurve_inj (P : X) (h : 0 < genus X) : Function.Injective (ofCurve P) :=
  ofCurve_inj' P h

end Jacobian
```

**Reconciling the two gate shapes**: `jacobian-construction`'s existing gates use
`[DiscreteTopology (RS.periodSubgroup X).topologicalClosure]` (discreteness of the *closure*,
needed for the quotient's own manifold charts); this design's gate uses
`[DiscreteTopology (RS.periodSubgroup X)]` (discreteness of the *raw* subgroup, matching Forster
21.4(i) verbatim, and what makes `AddSubgroup.isClosed_of_discrete` fire, §9). These are not the
same hypothesis, but `period-lattice-rank`'s own proof of Forster 21.4 naturally produces the raw
one *first* (Forster proves discreteness of `Γ` itself, not of some closure of `Γ`), and
`jacobian-construction`'s `discreteTopology_toIntSubmodule`-style bridge instances (`Basic.lean:60`)
already show the project's idiom for deriving one shape from the other cheaply — `period-lattice-
rank` is expected to register **both** instances (raw discreteness directly from Forster 21.4, and
`.topologicalClosure` discreteness via `(periodSubgroup X).topologicalClosure = periodSubgroup X`
rewriting, a corollary of the same `isClosed_of_discrete` fact this unit uses). Filed as a
coordination note for `period-lattice-rank`'s designer (§8).

---

## 5. File plan

| # | File | Content | Est. lines |
|---|------|---------|-----------|
| 1 | `Abel/Loops.lean` | `mem_periodSubgroup_iff_exists_loop` (D2), the loop-cancellation construction (§2.1 steps 1–3, `RS.Abel.exists_zeroPeriod_path`), the `k`-point period-vector bookkeeping for §4.1's `ι`-indexed sum | ~140 |
| 2 | `Abel/DolbeaultBridge.lean` | `exists_dbar_eq_zero_of_forall_basis_pairing_eq_zero` (D3) — the highest-risk file, gated on `serre-duality-tails`/`dolbeault-comparison` landing | ~150 (0 buildable today) |
| 3 | `Abel/WeakToMero.lean` | The `wirtingerDbar`-product-rule identity (D2), the CR-converse promotion of a weak solution + `d''`-exact witness into an honest `RS.ℳ X`, order computations at `P`/`Q`/elsewhere | ~180 |
| 4 | `Abel/Sufficiency.lean` | `exists_mero_of_pathIntegral_mem` (two-point, D1, full proof), `exists_mero_of_periodVector_mem` (`k`-point, D1, `Finset`-iteration), the genus-0 shortcut corollaries (§2.2) | ~220 |
| 5 | `Abel/OfCurveInj.lean` | `Jacobian.ofCurve_inj'` (gated, D4), `Jacobian.ofCurve_inj` (final-assembly one-line wrapper — may instead live in `period-lattice-rank`'s or the final assembly's own file; kept here as the default location) | ~70 |
| 6 | `Jacobian/Abel.lean` | unit root; API docstring; DAG-audit note (§3); ordering-resolution note (§1) | ~50 |

Total ≈ 810 lines (near the per-file budget aggregate; files 1, 3, 4 are independently buildable
today — no blocked imports; file 2 is the sole schedule-blocked file; file 5 needs files 1–4).
Build order: file 1 (independent) → file 3 (independent of 1) → file 2 (blocked on external
units) → file 4 (needs 1–3) → file 5 (needs 4).

---

## 6. Exports — exact signatures (consolidated)

```lean
namespace RS.Abel

-- Loops.lean
theorem mem_periodSubgroup_iff_exists_loop {X} [...] {v : Fin (genus X) → ℂ} :
    v ∈ RS.periodSubgroup X ↔
      ∃ α : Path (Classical.arbitrary X) (Classical.arbitrary X), RS.periodVector (RS.basis X) α = v

theorem exists_zeroPeriod_path {Q P : X} (hQP : Q ≠ P)
    (hmem : (fun i => RS.pathIntegral (some fixed δ : Path Q P) (RS.basis X i)) ∈ RS.periodSubgroup X) :
    ∃ δ' : Path Q P, ∀ ω : RS.Form1 X, RS.pathIntegral δ' ω = 0

-- DolbeaultBridge.lean
theorem exists_dbar_eq_zero_of_forall_basis_pairing_eq_zero {η : RS.Form01 X}
    (h : ∀ i : Fin (genus X), <pairing of η against basis X i> = 0) :
    ∃ u : RS.SmoothC X, RS.dbar u = η

-- WeakToMero.lean
theorem exists_mero_of_weakSolution_and_dbarExact {P Q : X}
    {f : X → ℂ} (hf : RS.AbelWeak.IsWeakSolutionOfPair f P Q)
    {u : RS.SmoothC X} (hu : RS.dbar u = <η built from f>) :
    ∃ F : RS.ℳ X, F ≠ 0 ∧ F.ord P = 1 ∧ F.ord Q = -1 ∧ ∀ z, z ≠ Q → z ≠ P → F.ord z = 0

-- Sufficiency.lean
theorem exists_mero_of_pathIntegral_mem {P Q : X} (hPQ : Q ≠ P) (δ : Path Q P)
    (hmem : (fun k => RS.pathIntegral δ (RS.basis X k)) ∈ RS.periodSubgroup X) :
    ∃ F : RS.ℳ X, F ≠ 0 ∧ F.ord P = 1 ∧ F.ord Q = -1 ∧ ∀ z, z ≠ Q → z ≠ P → F.ord z = 0

theorem exists_mero_of_periodVector_mem {ι} [Fintype ι] [DecidableEq ι]
    (a x : ι → X) (ha : Function.Injective a) (hx : Function.Injective x) (hax : ∀ i j, a i ≠ x j)
    (γ : (i : ι) → Path (a i) (x i))
    (hmem : (fun k => ∑ i, RS.pathIntegral (γ i) (RS.basis X k)) ∈ RS.periodSubgroup X) :
    ∃ F : RS.ℳ X, F ≠ 0 ∧ (∀ i, F.ord (x i) = 1) ∧ (∀ i, F.ord (a i) = -1) ∧
      ∀ z, (∀ i, z ≠ a i) → (∀ i, z ≠ x i) → F.ord z = 0

theorem genus_eq_zero_of_pathIntegral_mem {P Q : X} (hPQ : Q ≠ P) (δ : Path Q P)
    (hmem : (fun k => RS.pathIntegral δ (RS.basis X k)) ∈ RS.periodSubgroup X) :
    genus X = 0

end RS.Abel

namespace Jacobian
theorem ofCurve_inj' (P : X) (h : 0 < genus X) [DiscreteTopology (RS.periodSubgroup X)] :
    Function.Injective (ofCurve P)
theorem ofCurve_inj (P : X) (h : 0 < genus X) : Function.Injective (ofCurve P)  -- final assembly
end Jacobian
```

---

## 7. Risks (ranked)

1. **HIGH — R1, the Dolbeault-upgrade bridge (§4.3) depends on two not-yet-built units**
   (`serre-duality-tails`, `dolbeault-comparison/Comparison.lean`). Both are fully designed with
   frozen signatures (quoted verbatim above), so the *interface* is stable, but zero lines of
   `Abel/DolbeaultBridge.lean` can compile until they land. Mitigation: build every other file
   first (they are independent); the design's proof plan (§4.3) is short (~5 composed
   equivalences) once the pieces exist, so this file is not expected to be a large risk once
   unblocked — the risk is scheduling, not mathematics.
2. **MEDIUM — R2, inherited from `abel-weak-solutions`'s own R1**: the `hconst`-refinement of
   Atom 2 (§7.3 of `abel-weak-solutions.md`) needed to match `g`'s value against the puncture in
   the residue identity. Not this unit's own gap, but this unit's proof (§4.1 step 5) directly
   consumes it.
3. **MEDIUM — R3, the `k`-point generalization's bookkeeping** (§4.1, `Finset`-indexed product of
   weak solutions and sum of `Form01 X` pieces). No new mathematical idea, but genuinely more
   `Finset`/pairwise-distinctness plumbing than the two-point case; budget accordingly (the
   two-point case, §4.1's `exists_mero_of_pathIntegral_mem`, should be built and verified FIRST,
   with the `k`-point case as a mechanical follow-up, not attempted from scratch).
4. **LOW — R4, the two Compat lemmas of §4.2** (`mem_periodSubgroup_iff_exists_loop`, the
   `wirtingerDbar`-product-rule identity). Both short, self-contained, no upstream blocker;
   filed as a request to `jacobian-construction`'s `Periods.lean` for the first (natural home for
   a fact about `periodSubgroup`'s own definition) with a local Compat fallback per
   `CONVENTIONS.md` rule 4.
5. **LOW — R5, gate-shape reconciliation** (§4.4): `ofCurve_inj'`'s gate
   (`[DiscreteTopology (RS.periodSubgroup X)]`) differs from `jacobian-construction`'s existing
   gates (`.topologicalClosure` variant). Flagged as a coordination note for `period-lattice-rank`
   (§8); no risk to *this* unit's own correctness, only to how cleanly the final assembly composes
   instances — mitigated by `AddSubgroup.isClosed_of_discrete` making the two shapes
   interderivable in one line either way.
6. **LOW — naming/signature churn**, standard per every sibling design doc: re-verify
   `abel-weak-solutions`'s exact exports (not yet built at time of this design — a design doc, not
   built code, per its own §9 spike) and `canonical-forms`'/`dbar-solvability`'s exact names
   (built, verified at source during this design, §2/§3) immediately before coding.

---

## 8. Coordination notes filed (no blueprint edit made)

* **DAG correction** (§3): recommend `abel-theorem`'s `Builds on:` read `abel-weak-solutions,
  canonical-forms, serre-duality-tails, dolbeault-comparison, dbar-solvability,
  meromorphic-and-divisors, proper-map-degree, sphere-topology` — dropping `cech-h1-genus`
  (redundant with `serre-duality-tails`'s own `h1_zero_eq_genus`) and never having needed
  `form-trace-tower`/`monodromy` in the first place.
* **`abel-weak-solutions.md` §1.4/§8 correction**: its claim that the general chain/cycle case
  "no current consumer needs" is now known to be false — `period-lattice-rank` needs the `k`-point
  case (§1.4). No change needed to `abel-weak-solutions`'s own built content (its two-point weak
  solution is exactly right and is reused `k` times, unchanged); the correction is to its
  *downstream-need* claim only.
* **`period-lattice-rank` (#31) designer, please note**: (a) this unit's primary export for you is
  `RS.Abel.exists_mero_of_periodVector_mem` (§4.1/§6, the `k`-point sufficiency direction) — this
  is what Forster 21.4(b)'s own proof needs, not the two-point specialization the blueprint's
  one-line blurb might suggest; (b) once you prove discreteness (`Γ ∩ W = 0`, Forster 21.4(b)),
  please register **both** `instance : DiscreteTopology (RS.periodSubgroup X)` (the raw fact) and
  (via `AddSubgroup.isClosed_of_discrete` + `IsClosed.closure_eq`, one line) `instance :
  DiscreteTopology (RS.periodSubgroup X).topologicalClosure` (needed by `jacobian-construction`'s
  existing gates) — both are cheap corollaries of the same discreteness proof, see §4.4/§9.
* **`cech-h1-genus`'s future designer** (if the orchestrator keeps the unit despite §3's redundancy
  finding): nothing in this design blocks on it; if built anyway, its content is expected to be a
  strict subset of what `serre-duality-tails`+`canonical-forms` already deliver.

---

## 9. Spike report (`scratch_abel.lean`, project root)

Gate respected (`pgrep -cx lean` = 1 at run time, under the limit of 3). `lake env lean
scratch_abel.lean`: **compiles clean, exit 0, zero sorries, zero errors** (18 lines of content).

Content: the ordering-resolution's load-bearing mathlib fact — for `H : AddSubgroup G` in any
`[AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]` (in particular
`G := Fin (genus X) → ℂ`, our actual use), `[DiscreteTopology H] → H.topologicalClosure = H`.
Proved via `AddSubgroup.isClosed_of_discrete` (the `to_additive` of mathlib's
`Subgroup.isClosed_of_discrete`, `Mathlib/Topology/Algebra/IsUniformGroup/Basic.lean:273`) +
`AddSubgroup.topologicalClosure_minimal`/`le_topologicalClosure` (antisymmetry). This is exactly
§1.3/§4.4's bridge step, confirmed to exist in mathlib at the pinned commit with no extra side
conditions beyond `[T2Space G]` (already available for `Fin n → ℂ`) — de-risking the entire
ordering-resolution design: the "discreteness ⟹ closedness" step this unit's whole gating strategy
depends on is a **three-line, zero-risk** mathlib citation, not new content.

Name traps surfaced (recorded for the real builder): the multiplicative `Subgroup.isClosed_of_discrete`
lives in `Topology.Algebra.IsUniformGroup.Basic` (not the more obviously-named
`Topology.Algebra.Group.Basic`, which only has `topologicalClosure`'s definition and
`isClosed_topologicalClosure`/`le_topologicalClosure`/`topologicalClosure_minimal` — the discreteness
half needs the uniform-group file specifically); a first attempt instantiating the spike at the
literal type `Fin n → ℂ` failed (`AddGroup (Fin n → ℂ)` did not synthesize from the targeted
imports used) — fixed by stating the lemma for an abstract topological group `G` instead (strictly
more general, and what the design doc's citation above states), sidestepping the missing
`Pi`-instance import rather than chasing it.

---

## 10. Downstream map

| Consumer | What it needs | Our export |
|---|---|---|
| **period-lattice-rank** (#31, primary) | The `k`-point sufficiency direction (Forster 21.4(b)'s own citation of Abel), for every `1 ≤ k ≤ g` | `RS.Abel.exists_mero_of_periodVector_mem` |
| **Final assembly / `Jacobian/Challenge.lean`** | The literal challenge lemma | `Jacobian.ofCurve_inj` (one-line wrapper over `ofCurve_inj'`, discharged once `period-lattice-rank`'s `DiscreteTopology (RS.periodSubgroup X)` instance is registered) |
| **genus-zero-headline** | Nothing directly (its forward direction is `proper-map-degree`'s `homeoSphere_of_exists_simple_pole` applied to Riemann–Roch's own single-simple-pole existence, not to anything Abel-specific) | — |
| **jacobian-construction** | Nothing further (its gates are already exactly shaped to receive `period-lattice-rank`'s instances directly, §4.4) | — |

No other unit needs anything from `abel-theorem` per the current blueprint edges (after the §3/§8
corrections).
