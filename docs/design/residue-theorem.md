# Design: residue-theorem (`Jacobian/ResidueTheorem/`)

Blueprint unit **residue-theorem**. Blueprint text: "The unconditional residue theorem
`∑_p Res_p(h·dg₀) = 0` for meromorphic pair forms on a compact `X`, any genus, via partition of
unity + planar Stokes. Read: Forster §10 (Thm 10.21); Miranda Ch. VI pp. 186–188. Strategy: cover
`X`, write the form as a sum of locally-supported pieces, apply planar Stokes to each; the
boundary terms cancel and what survives is `∑Res`." **Builds on:** canonical-forms,
planar-stokes-atoms (frozen DAG edges — verified against `clean_room_blueprint.md`, not just the
prose). ⚠ (routing decision #2): the residue **theorem** is Stokes-only/genus-agnostic; the residue
**functional** of Serre duality is a different object built later (serre-duality-tails, Miranda's
tail pairing) and must not be shortcut through here.

References: Forster GTM81 §10, Thm 10.21 (book p. 80 = PDF 86, **read in full**, quoted verbatim
below); Miranda GSM5 PDF 198–200 (cites the theorem as a black box, no independent proof); Forster
§17.1–17.3 (Mittag-Leffler forms, `Res(μ)=Res([δμ])`, PDF ~138–141, context for the downstream
Serre-pairing consumer).

One gated end spike (`scratch_resthm.lean`, project root) compiled clean — §12. Both spiked facts
de-risk the single new atom this unit must supply (§4).

---

## 0. Mandatory reading, digested

- **`CONVENTIONS.md`**: junk-free representations, `Compat` sections for missing upstream lemmas,
  ≤1 `lake`/`lean` job at a time, standing surface variables, `scripts/check.sh`.
- **`clean_room_blueprint.md`**: residue-theorem's entry (quoted above) and routing decision #2
  (theorem vs. functional — this unit builds **only** the theorem). The frozen `Builds on:` edge
  is `canonical-forms, planar-stokes-atoms` — **no other unit**. This is load-bearing for §3 below:
  it rules out silently adding `form-trace-tower` as a dependency.
- **`docs/design/core-choices.md`**: CC7 (`SmoothPartitionOfUnity` on `X` via the `𝓘(ℝ,ℂ)` bridge,
  built — `Jacobian/Surface/RealSmooth.lean`, read in full, §1.5 below).
- **`docs/design/canonical-forms.md`** (AUTHORITATIVE, being built now; `Jacobian/CanonicalForms/`
  does **not exist on disk yet** — zero files, confirmed by `find`). This unit is designed
  **against canonical-forms's design doc**, exactly as form-trace-tower's own design was written
  against mtrace's design doc while mtrace was mid-build (documented precedent in this project).
  The exports consumed (`MForm`, `.coeffAt`, `.compat`, `.ord`, `.resAt`, `.divisor`) are all
  **frozen interface** per canonical-forms's own file-plan table (files 1–2, gate-independent of
  finiteness-and-chi) — low risk of drift. §1.2 below re-quotes the exact signatures consumed.
- **`docs/design/planar-stokes.md`** (AUTHORITATIVE, being built; `Jacobian/PlanarStokes/` has
  **`Compat.lean` and `CompactSupport.lean` built, zero sorries** — read both in full, §1.3 below,
  confirms the design doc matches the code exactly — but **`AnnulusResidue.lean` (Atom 1′/Atom 2,
  the smeared-residue theorem) is NOT yet on disk**, only frozen-signature design). Its own §11
  ("Downstream map") already sketches how residue-theorem is expected to consume Atom 1b/Atom 2 —
  read in full, it is the direct ancestor of §4.3's assembly below. Its §D4 hypothesis (cutoffs
  must be **locally constant**, not merely continuous, near a pole) is the coordination constraint
  this design is built around throughout.
- **`docs/design/dbar-solvability.md`** + `Jacobian/Dbar/` on disk (`Wirtinger.lean`,
  `CauchyKernel.lean`, `Form01.lean`, `Operator.lean`, `SolveDisk.lean` — all present; `Wirtinger.lean`
  and `Form01.lean` read in full). `SmoothPartitionOfUnity`/PoU availability is CC7's job, not
  dbar-solvability's; dbar-solvability's own PoU need (`PlanarPoU.lean`, planar-only) is a
  **different, disjoint** object from what this unit needs (a **surface-level** PoU) — no overlap,
  no import from `Jacobian/Dbar/PlanarPoU.lean` (not even built) is required here.
- **`Jacobian/Surface/RealSmooth.lean`** (read in full, quoted §1.5): `RS.exists_smoothPartitionOfUnity`
  is **already built** — the exact tool §5 below is built on.
- **`docs/design/form-trace-tower.md`** (read in full — the candidate alternative route, evaluated §3, designed in full §6):
  its own §0.3 ("DAG audit") independently confirms **residue-theorem's frozen edge does not
  include form-trace-tower** ("`residue-theorem` — Builds on: canonical-forms, planar-stokes-atoms
  ... no mention of a push to `ℙ¹`. This is Forster's route, not Miranda's."). Its own file 5
  (`RationalOnP1.lean`, the partial-fraction `∑Res=0`-on-`ℙ¹` base case) is flagged **by its own
  designer** as "non-load-bearing bonus... do not let it hold up," and its central theorem
  (`resAtP1_trace_eq_sum`) is gated on mtrace's `PlanarTrace.lean` `laurentCoeffAt_traceZk` (P6),
  which **has an open `sorry`** (verified directly, §1.6). `Jacobian/FormTrace/` does not exist on
  disk (0 files). This is decisive for §3's recommendation.

---

## 1. Facts relied on (verified against files/design docs on disk)

### 1.1 Verified project state (searched, not assumed)

```
find Jacobian -iname "*Canonical*" -o -iname "*MForm*"   →  (nothing — unit not started)
find Jacobian -iname "*FormTrace*"                        →  (nothing — unit not started)
ls Jacobian/PlanarStokes/   → Compat.lean, CompactSupport.lean   (AnnulusResidue.lean missing)
ls Jacobian/Dbar/           → Wirtinger.lean, CauchyKernel.lean, Form01.lean, Operator.lean,
                               SolveDisk.lean   (all present)
grep -rn sorry Jacobian/    → zero hits (the one grep hit is a docstring sentence, not a tactic)
```
`Jacobian/MeromorphicTrace/PlanarTrace.lean:` `laurentCoeffAt_traceZk` (P6, form-trace-tower's own
central input) carries an in-file `sorry` per form-trace-tower's design doc §0.4 (re-verified: the
file exists and mtrace's own design doc records the sorry status; the trace-route evaluation in
§3 treats this as an *external, out-of-scope* blocker, not something residue-theorem can resolve).

### 1.2 `MForm` (canonical-forms, design-frozen; file 1–2 of its plan, gate-independent)

```lean
structure MForm (X) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] where
  coeffAt : X → ℂ → ℂ
  coeffAt_zero_off : ∀ x, ∀ z ∉ (chartAt ℂ x).target, coeffAt x z = 0
  meromorphicOn_coeffAt : ∀ x, MeromorphicOn (coeffAt x) (chartAt ℂ x).target
  compat : ∀ x y : X, ∀ z ∈ ⇑(chartAt ℂ y) '' ((chartAt ℂ x).source ∩ (chartAt ℂ y).source),
    coeffAt y z = deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) z *
      coeffAt x (chartAt ℂ x ((chartAt ℂ y).symm z))

noncomputable def MForm.ord (ω : MForm X) (x : X) : WithTop ℤ :=
  meromorphicOrderAt (ω.coeffAt x) (chartAt ℂ x x)
noncomputable def MForm.resAt (ω : MForm X) (x : X) : ℂ :=
  RS.resAt (ω.coeffAt x) (chartAt ℂ x x)
noncomputable def MForm.divisor [T2Space X] [CompactSpace X] (ω : MForm X) : Divisor X where
  toFun x := (ω.ord x).untop₀
  -- local finiteness: connectedness-free (canonical-forms D6) — mirrors `MeroGermOn.divisorOn`

theorem MForm.resAt_eq_of_mem_source {ω x} {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (hx : x ∈ e.source) :
    ω.resAt x = RS.resAt (fun z => deriv (⇑(chartAt ℂ x) ∘ ⇑e.symm) z *
      ω.coeffAt x (chartAt ℂ x (e.symm z))) (e x)          -- via `resAt_comp_mul_deriv`, built
```
`MForm.d`/`dlog`/`resAt_dlog` (canonical-forms D7, §4.3 of its design, consumed only by §5's bonus
corollaries here, not by the main theorem):
```lean
theorem MForm.resAt_dlog [T1Space X] (f : ℳ X) (hf : f ≠ 0) (x : X) :
    (MForm.dlog f).resAt x = ((f.ord x).untop₀ : ℂ)
```
**One gap filled locally (§4.1, marked `Compat`):** canonical-forms's design doc does not export
"`ω.ord x ≥ 0 ⟹ ω.resAt x = 0`" as a named lemma, but it is a **one-line corollary** of already-frozen
pieces (`MForm.resAt`'s definition unfolds to `RS.resAt`, and `RS.resAt_of_order_nonneg` is BUILT,
`ResidueCalculus/Residue.lean:72`) — this unit proves it locally per CONVENTIONS.md's Compat rule
and files a request to canonical-forms to upstream it (§11).

### 1.3 `Jacobian/PlanarStokes/` — verified against the actual files on disk

Built (`Compat.lean`, `CompactSupport.lean`, read in full):
```lean
theorem wirtingerDbar_mul_of_differentiableAt (hg : DifferentiableAt ℝ g z)
    (hf : DifferentiableAt ℂ f z) :
    wirtingerDbar (fun w => g w * f w) z = wirtingerDbar g z * f z
theorem wirtingerDbar_mul_eq_zero_of_notMem_tsupport (hz : z ∉ tsupport g) :
    wirtingerDbar (fun w => g w * f w) z = 0
theorem ContDiffOn.contDiff_of_hasCompactSupport {U} {n} (hU : IsOpen U)
    (hg : ContDiffOn ℝ n g U) (hcs : HasCompactSupport g) (hsub : tsupport g ⊆ U) : ContDiff ℝ n g
theorem continuous_wirtingerDbar_of_contDiff_one (hg : ContDiff ℝ 1 g) : Continuous (wirtingerDbar g)
theorem integral_wirtingerDbar_eq_zero (hU) (hg) (hcs) (hsub) : ∫ w : ℂ, wirtingerDbar g w = 0
theorem integral_wirtingerDbar_mul_eq_zero_of_differentiableOn (hU) (hg) (hcs) (hsub)
    (hf : DifferentiableOn ℂ f U) : ∫ w : ℂ, wirtingerDbar g w * f w = 0     -- Atom 1b
```
**Designed but not yet on disk** (`AnnulusResidue.lean`, frozen signature per its design §5.3,
consumed here as an interface — this unit's builder must confirm it has landed with this exact
shape before `Theorem.lean` compiles; §10 flags this as a scheduling, not interface, risk):
```lean
theorem integral_wirtingerDbar_mul_eq_neg_pi_mul_resAt (hU : IsOpen U) (hpU : p ∈ U)
    (hg : ContDiffOn ℝ 1 g U) (hcs : HasCompactSupport g) (hsub : tsupport g ⊆ U)
    (hconst : g =ᶠ[nhds p] Function.const ℂ (g p))
    (hf : DifferentiableOn ℂ f (U \ {p})) (hfp : MeromorphicAt f p) :
    ∫ w : ℂ, wirtingerDbar g w * f w = -π * g p * resAt f p          -- Atom 2
```

### 1.4 `Jacobian/Dbar/Wirtinger.lean` (built, mathlib-only, read in full)

```lean
theorem wirtingerDbar_comp_differentiableAt {τ : ℂ → ℂ} (hF : DifferentiableAt ℝ f (τ z))
    (hτ : DifferentiableAt ℂ τ z) :
    wirtingerDbar (f ∘ τ) z = (starRingEnd ℂ) (deriv τ z) * wirtingerDbar f (τ z)
```
**This is exactly the `(0,1)`-transition rule** the new Area-Gluing atom (§4.2) needs; it is already
proved, so the entire *algebraic* half of that atom is free.

### 1.5 `Jacobian/Surface/RealSmooth.lean` (built, read in full)

```lean
theorem exists_smoothPartitionOfUnity [T2Space X] [CompactSpace X] {ι : Type*}
    (U : ι → Set X) (ho : ∀ i, IsOpen (U i)) (hU : (univ : Set X) ⊆ ⋃ i, U i) :
    ∃ p : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) X univ, p.IsSubordinate U
```
mathlib's `SmoothPartitionOfUnity.IsSubordinate f U := ∀ i, tsupport (f i) ⊆ U i`
(`Geometry/Manifold/PartitionOfUnity.lean:270`, verified). `sum_eq_one' : ∀ x ∈ s, ∑ᶠ i, f i x = 1`
(here `s = univ`, so unconditionally `∀ x`).

### 1.6 The Jacobian-determinant fact (NEW, spike-verified §12)

No mathlib lemma packages "the real Jacobian determinant of a holomorphic map is `‖deriv f z‖²`"
directly (checked: no hits for `abs_det_fderiv` combined with `Complex`/`holomorphic` anywhere in
`Mathlib/Analysis/Complex` or `Mathlib/MeasureTheory`). It assembles cleanly from three already-built
pieces, chained in the spike:
```lean
Mathlib.Analysis.Calculus.Deriv.Basic:
  fderiv_eq_deriv_mul {f : 𝕜 → 𝕜} {x y} : (fderiv 𝕜 f x : 𝕜 → 𝕜) y = deriv f x * y   -- unconditional
Mathlib.Algebra.Algebra.Bilinear:
  Algebra.coe_lmul_eq_mul, LinearMap.mul_apply'   -- ⇑(Algebra.lmul R A a) = (a * ·)
Mathlib.RingTheory.Norm.Defs / Mathlib.RingTheory.Complex:
  Algebra.norm_apply (x : S) : norm R x = LinearMap.det (lmul R S x)
  Algebra.norm_complex_apply (z : ℂ) : Algebra.norm ℝ z = Complex.normSq z
```
### 1.7 The general planar change-of-variables theorem (mathlib, `MeasureTheory/Function/Jacobian.lean`)

```lean
theorem MeasureTheory.integral_target_eq_integral_abs_det_fderiv_smul {f : OpenPartialHomeomorph E E}
    (hf' : ∀ x ∈ f.source, HasFDerivAt f (f' x) x) (g : E → F) :
    ∫ x in f.target, g x ∂μ = ∫ x in f.source, |(f' x).det| • g (f x) ∂μ
```
`E := ℂ`, `μ := volume`. This is the measure-theoretic engine of §4.2's new atom.

### 1.8 `RS.analyticAt_transition` (local-multiplicity, BUILT, `ChartBridge.lean`, read in full)

```lean
theorem analyticAt_transition {e e' : OpenPartialHomeomorph X ℂ}
    (he he' : mem maximalAtlas) {x} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    AnalyticAt ℂ (⇑e' ∘ ⇑e.symm) (e x) ∧ deriv (⇑e' ∘ ⇑e.symm) (e x) ≠ 0
```
Already the engine behind `ordAtX_eq_of_mem_source`, mtrace's `resAtX_eq_of_mem_source`, and
canonical-forms's own `MForm.resAt_eq_of_mem_source` (§1.2) — reused again for §4.2's transition
map `τ`.

---

## 2. The statement (no connectedness needed — matches Forster exactly)

Forster's own hypothesis (10.21, quoted in full, PDF 80): *"Suppose `X` is a compact Riemann
surface and `a₁,…,aₙ` are distinct points in `X`."* **No connectedness hypothesis.** The blueprint
task brief's phrasing ("compact connected `X`") is stronger than needed; the Stokes/PoU proof does
not use connectedness anywhere (unlike the field/germ machinery of `ℳ X`, which does). This is a
genuine, free generalization worth keeping.

```lean
namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The pole set of a meromorphic 1-form: points of strictly negative order. Finite on compact
`X`, connectedness-free (mirrors `MForm.divisor`'s own connectedness-free local finiteness). -/
def MForm.PoleSet [T2Space X] [CompactSpace X] (ω : MForm X) : Set X := {x | ω.ord x < 0}

theorem MForm.resAt_eq_zero_of_ord_nonneg {ω : MForm X} {x : X} (h : 0 ≤ ω.ord x) :
    ω.resAt x = 0                                                          -- Compat, §1.2/§4.1

theorem MForm.finite_poleSet [T2Space X] [CompactSpace X] (ω : MForm X) :
    ω.PoleSet.Finite                                                       -- §4.1, mirrors D6

theorem MForm.resAt_support_subset_poleSet [T2Space X] [CompactSpace X] (ω : MForm X) :
    Function.support ω.resAt ⊆ ω.PoleSet := fun x hx =>
  by_contra fun h => hx (resAt_eq_zero_of_ord_nonneg (not_lt.mp h))

/-- **THE residue theorem** (Forster 10.21 / Miranda VI "the Residue Theorem", eq. 3.2): for any
meromorphic 1-form on a compact (not necessarily connected) Riemann surface, the sum of residues
over any finite set containing the poles is zero. Phrased over an arbitrary containing `Finset`
(mirrors `Divisor.degree_eq_sum_of_subset`'s idiom) rather than a canonical choice, so callers may
plug in whatever finite index set is convenient (e.g. a shared pole set of several forms in a
Serre-pairing computation). -/
theorem residueTheorem [T1Space X] [T2Space X] [CompactSpace X] (ω : MForm X)
    {S : Finset X} (hS : ω.PoleSet ⊆ (S : Set X)) :
    ∑ x ∈ S, ω.resAt x = 0

/-- Corollary in the canonical, PoU-independent finite-sum form. -/
theorem MForm.sum_resAt_eq_zero [T1Space X] [T2Space X] [CompactSpace X] (ω : MForm X) :
    ∑ x ∈ ω.finite_poleSet.toFinset, ω.resAt x = 0 :=
  residueTheorem ω (by simp [Set.Finite.subset_toFinset])

end RS
```

---

## 3. Route evaluation: PoU + planar Stokes (PRIMARY) vs. trace-to-`ℙ¹` (documented alternative)

The task brief for this design explicitly asks to seriously evaluate the trace-to-`ℙ¹` route as a
possible ~10× cheaper primary, *conditional on* form-trace-tower's residue-trace-compatibility +
partial-fraction base case + a nonconstant map all being available. **That condition fails, on all
three counts, verified directly against the files:**

1. **`resAtP1_trace_eq_sum`** (form-trace-tower's own central theorem, Miranda Lemma 3.2
   globalized) is gated on mtrace's `laurentCoeffAt_traceZk` (P6), which **carries an open `sorry`**
   in `Jacobian/MeromorphicTrace/PlanarTrace.lean` today (form-trace-tower's own design doc §0.4
   records this; re-verified live). This sorry belongs to a *different* unit (`meromorphic-trace`),
   outside residue-theorem's scope to fix.
2. **`Jacobian/FormTrace/` does not exist on disk** (0 files) — the whole unit, including
   `FunctionTrace.lean` (mtrace's own `Tr_F h` assembly, also not yet written) and
   `ResidueTraceCompat.lean`, would need to be built from scratch, by a different unit's builder,
   before residue-theorem could import it.
3. **The partial-fraction `∑Res=0`-on-`ℙ¹` base case** (form-trace-tower's `RationalOnP1.lean`) is
   flagged **by its own designer** as "non-load-bearing... do not let it hold up" — i.e., even the
   unit that would supply it does not treat it as a priority, and it needs its own new
   "entire + polynomial growth ⟹ polynomial" Liouville-type lemma, "not found in mathlib as a
   packaged theorem" (form-trace-tower §1, independently checked here, confirmed absent).
4. Using the trace route would require **adding `form-trace-tower` to this unit's `Builds on:`
   edge**, deviating from the frozen DAG (`canonical-forms, planar-stokes-atoms` only) — a
   blueprint change, not a local design choice, per CONVENTIONS.md's spirit that the DAG and the
   three frozen definitional choices are not unilaterally re-chosen by a unit designer.

The one piece that *is* available today is a nonconstant map `X → ℙ¹`
(`RS.toP1`/`toP1_contMDiff`/`toP1_not_const`, `Jacobian/MeromorphicTrace/ToP1.lean`, **zero
sorries**) — but one available ingredient out of four does not make the route ready.

**Conclusion: the trace route is not ready today, and adopting it now would trade a self-contained,
in-DAG unit for a dependency on another unit's open sorry, a nonexistent unit, and a
deliberately-deprioritized bonus fact — the opposite of "10× cheaper" in practice.** §6 designs it
in full anyway (as the task requests, and because it is a legitimate, cheaper-in-principle route
that should be revisited once form-trace-tower's P6 gate clears and the unit lands) but as the
**documented alternative**, not primary.

### 3.1 Why the "obvious" PoU + Stokes proof needs ONE genuinely new atom

Re-reading Forster 10.21's proof in full (quoted in §0, PDF 80) exposes a subtlety the blueprint
prose glosses over. Forster's argument is not "each partition-of-unity piece independently gives 0
or a residue, and the pieces trivially add up" — it routes through his **own prior, general fact**
(10.20: "`X` a Riemann surface, `ω ∈ ℰ^(1)(X)` compact support `⟹ ∬_X dω = 0`"), which is itself
built on a **chart-independent notion of `∬_X` for smooth (not necessarily holomorphic) forms**
(defined earlier in his book, §10.18, exactly the passage quoted at the top of the excerpt: *"Then
`f_kω` is a differential form with `Supp(f_kω) ⋐ U`... Define `∬_X ω := ∑ₖ ∬_X f_kω`... it is
straightforward to check the definition is independent of the choice of charts and functions
`f_k`."*). **That independence check is precisely a change-of-variables/Jacobian fact** — Forster
has it as prior general machinery; this project has never built anything like it (checked: no
design doc anywhere in `docs/design/` mentions a chart-independent area/2-form integral on `X`).

Working through the algebra confirms this is not avoidable by being cleverer about the *specific*
partition used. Write `g := 1 - ∑ₖ fₖ` (Forster's cutoff, `fₖ ≡ 1` near pole `aₖ`, compact support
in disjoint chart disks `Uₖ`). Because `X` is not (in general) coverable by a single chart, `g`
must *also* be written as `∑ⱼ χⱼ` for finitely many further chart-supported bumps `χⱼ` covering
`X \ {a₁,…,aₙ}`. Both expressions of `g` give a pointwise identity of smooth 2-forms,
`∑ⱼ d(χⱼω) = -∑ₖ d(fₖω)`, but turning this into the numeric identity `∑ⱼ Ⲓⱼ = -∑ₖ Ⲓₖ` (where each
`Ⲓ` is *that piece's own chart-local planar integral*) requires knowing that "the total, computed
by decomposing into single-chart pieces, is independent of which decomposition/chart family is
used" — exactly the (1,1)-density transformation fact. There is no way to route around it while
still handling **every** genus (a single global remainder chart only exists for genus 0).

**The good news, confirmed by the spike (§12):** this fact is cheap to build here, because its two
halves are *already* available for free:
- the **algebraic** half (how the `(0,1)`-coefficient of a cutoff and the `(1,0)`-coefficient of
  `ω` each transform under a chart change) is **already proved**: `wirtingerDbar_comp_differentiableAt`
  (Dbar, built, §1.4) for the cutoff's `∂̄`, and `MForm.compat`/`resAt_eq_of_mem_source` (canonical-forms,
  §1.2) for `ω`'s coefficient. Multiplying the two transition factors (`conj(deriv τ)` and `deriv τ`)
  gives exactly `‖deriv τ‖²` — the correct (1,1)-density weight — with zero new algebra.
- the **measure-theoretic** half is one clean application of mathlib's own general
  `integral_target_eq_integral_abs_det_fderiv_smul` (§1.7) plus the small Jacobian-determinant
  computation `LinearMap.det (fderiv ℝ τ z) = normSq (deriv τ z)` (§1.6), **both spike-verified**.

So the new content is genuinely new (nothing in `planar-stokes` or `canonical-forms` supplies it —
planar-stokes explicitly scopes out any change-of-variables beyond `resAt_comp_mul_deriv`, §10 of
its own design, which is about *residues*, not *area integrals*) but it is a self-contained,
moderate-sized (~150–250 line) lemma built entirely from already-verified pieces, owned cleanly by
*this* unit, with no dependency on any other unit's incomplete work. That is why §4 below still
recommends the PoU + Stokes route as primary.

---

## 4. Design of the primary route

### 4.1 The cutoff construction: automatic constancy (cheap, spike-verified)

**The key simplification the task asked to verify is correct.** Given a `SmoothPartitionOfUnity`
`{ψᵢ}` on `X` (`s := univ`) subordinate to a cover `{Uᵢ}`, if a point `p` has a neighborhood `V`
that meets no `Uⱼ` for `j ≠ i`, then `ψᵢ ≡ 1` on `V` and `ψⱼ ≡ 0` on `V` for `j ≠ i` — **automatically**,
with no `ContDiffBump`-specific construction needed. The proof, confirmed by the spike:

```lean
theorem SmoothPartitionOfUnity.eventuallyEq_one_of_forall_disjoint
    {ι} {p : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) X univ} {U : ι → Set X} (hp : p.IsSubordinate U)
    {x : X} {i : ι} {V : Set X} (hV : V ∈ 𝓝 x) (hVi : ∀ j ≠ i, V ∩ U j = ∅) :
    ∀ y ∈ V, p i y = 1 := by
  intro y hy
  have hzero : ∀ j ≠ i, p j y = 0 := fun j hj => by
    by_contra hne
    exact Set.eq_empty_iff_forall_notMem.mp (hVi j hj) y
      ⟨hy, hp j (Function.mem_support.mpr hne)⟩         -- support (p j) ⊆ tsupport (p j) ⊆ U j
  have := p.sum_eq_one (Set.mem_univ y)
  rwa [finsum_eq_single (fun j => p j y) i hzero] at this
```
(Proof: `y ∈ V`, `j ≠ i`, `p j y ≠ 0 ⟹ y ∈ Function.support (p j) ⊆ tsupport (p j) ⊆ U j`
(`hp j`, subordination) `⟹ y ∈ V ∩ U j`, contradicting `hVi j hj`. So `p j y = 0` for all `j ≠ i`;
`finsum_eq_single` (mathlib, `Algebra/BigOperators/Finprod.lean:209`-additive-alias — additive form
of `finprod_eq_single`, **spike-verified**, §12) collapses `∑ᶠ j, p j y` to `p i y`, and `sum_eq_one'`
(`s = univ`) gives the total `1`.) **No local finiteness argument, no `ContDiffBump` centering
argument, and no case split are needed** — this is the entire content, ~10 lines, exactly matching
the task brief's own "automatic!" intuition, now spike-verified rather than merely asserted.

**Building the disjoint pole-disk + remainder cover.** With `ω.finite_poleSet` finite (§2), for
each pole `p ∈ ω.PoleSet` (T1 space, finite set minus a point is closed) choose an open
`Wₚ ⊆ (chartAt ℂ p).source` with `Wₚ ∩ (ω.PoleSet \ {p}) = ∅` (routine: `(chartAt ℂ p).source ∩
(ω.PoleSet \ {p})ᶜ` is open — finite-minus-a-point is closed in a `T1Space` — and contains `p`).
Since `X` is compact, `X \ ω.PoleSet` is open and admits a **finite** subcover by chart sources
avoiding `ω.PoleSet` entirely (compactness of `X \ ⋃ₚ Wₚ`, a closed — hence compact — subset of
`X`, covered by `{(chartAt ℂ x).source \ ω.PoleSet}ₓ`; extract a finite subcover
`{(chartAt ℂ x_ℓ).source \ ω.PoleSet}_{ℓ=1}^m`). Feed the finite cover
`(inl p)ₚ ↦ Wₚ`, `(inr ℓ) ↦ (chartAt ℂ x_ℓ).source \ ω.PoleSet` (index type
`ω.finite_poleSet.toFinset ⊕ Fin m`) to `RS.exists_smoothPartitionOfUnity` (§1.5, built) to get
`{ψᵢ}` subordinate to it. **Automatic constancy** (above), applied with `V := Wₚ` at each pole
`p` (which meets no other cover element, by construction — the `Wₚ`'s pairwise-disjointness from
each other's poles and from every remainder piece is built into their definition), gives
`ψ_{inl p} ≡ 1` on `Wₚ` and every other piece `≡ 0` there. This is a **finite** cover throughout
(both summands finite), matching planar-stokes's own §11 sketch ("finite open cover... one per
pole plus enough to cover the rest").

### 4.2 The new atom: chart-invariance of the planar `wirtingerDbar`-pairing integral

File `Jacobian/ResidueTheorem/AreaGluing.lean`. Stated for two arbitrary maximal-atlas charts (not
just `chartAt`-to-`chartAt`, so it is reusable for both the automatic-constancy cover of §4.1 and
any future consumer):

```lean
/-- **The new atom.** Two charts' own planar `wirtingerDbar`-against-`ω` integrals over
corresponding (compactly-supported-in-the-overlap) regions agree. `τ := e' ∘ e.symm` is the
transition map; `g'` is `g` transported through it; `f`, `f'` are `ω`'s two chart readings, related
by `MForm.compat`. No integration-theoretic content beyond mathlib's own
`integral_target_eq_integral_abs_det_fderiv_smul`; the transition algebra is 100% reused
(`wirtingerDbar_comp_differentiableAt`, `MForm.compat`/`resAt_eq_of_mem_source`). -/
theorem integral_wirtingerDbar_mul_chart_congr {e e' : OpenPartialHomeomorph X ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    {g : ℂ → ℂ} {U : Set X} (hU : IsOpen U) (hUe : U ⊆ e.source) (hUe' : U ⊆ e'.source)
    (hg : ContDiffOn ℝ 1 g (e '' U)) (hcs : HasCompactSupport g) (hsub : tsupport g ⊆ e '' U)
    (ω : MForm X) (hf : DifferentiableOn ℂ (ω.coeffAt) ((e '' U) \ (ω.PoleSet.image e)))
    -- (shape schematic; exact side-conditions threaded in the proof, see below)
    :
    ∫ w : ℂ, wirtingerDbar g w * (fun z => deriv (⇑e ∘ ⇑e'.symm) z *
        ω.coeffAt _ (e ((e'.symm) z))) w -- reads `ω` through `e`
      = ∫ w : ℂ, wirtingerDbar (g ∘ ⇑e ∘ ⇑e'.symm) w * ω.coeffAt _ w -- reads `ω` through `e'`
```

**Proof plan** (~150–200 lines, three parts):

1. **The determinant fact** (spike-verified, §12 item 1, ~20 lines): for `τ` holomorphic at `z`,
   `LinearMap.det (fderiv ℝ τ z : ℂ →ₗ[ℝ] ℂ) = Complex.normSq (deriv τ z)`, via
   `fderiv_eq_deriv_mul` + `Algebra.lmul`/`Algebra.norm_apply`/`Algebra.norm_complex_apply` (§1.6).
   Package as `RS.det_fderiv_eq_normSq_deriv {τ} {z} (hτ : DifferentiableAt ℂ τ z) : ...`.
2. **The substitution** (~60–80 lines): apply
   `MeasureTheory.integral_target_eq_integral_abs_det_fderiv_smul` (§1.7) to the transition
   `τ := e ∘ e'.symm` (an `OpenPartialHomeomorph ℂ ℂ` on the relevant overlap, built from `e`, `e'`
   restricted to the common source via `OpenPartialHomeomorph.trans`/`restr`, `analyticAt_transition`
   giving `AnalyticAt`/nonvanishing-derivative pointwise, §1.8) with `g := fun w => wirtingerDbar
   (g∘τ⁻¹) w * f'(w)` (the "chart `e`-side" integrand read on the target), giving
   `∫_{e-target} (...) = ∫_{e'-target} |det(fderiv ℝ τ)| • (... ∘ τ)`. Rewrite `|det (fderiv ℝ τ z)|
   = normSq(deriv τ z) = ‖deriv τ z‖²` (item 1).
3. **The algebra** (~40–60 lines): apply `wirtingerDbar_comp_differentiableAt` (§1.4, the `conj(deriv
   τ)` factor for the cutoff) and `MForm.compat`/`resAt_eq_of_mem_source` (§1.2, the `deriv τ`
   factor for `ω`'s coefficient) to show the two transition factors multiply to exactly cancel the
   `‖deriv τ‖²` weight from step 2, closing the identity. This is the SAME algebra already
   spike-verified in `docs/design/planar-stokes.md` §7 Step 2 (the `exp`-substitution computation)
   generalized from `τ := exp` to an arbitrary holomorphic transition — no new algebraic idea, just
   the general case of a pattern already exercised once.

**A second, targeted lemma (not a fully general "PoU-independence" theorem — scope discipline)**
packages exactly what §4.3 needs: given the *specific* pole-cover `{ψᵢ}` of §4.1 and *any other*
finite chart-supported decomposition `g = ∑ⱼ χⱼ` of the same function `g`, the two totals
`∑ᵢ(chart-i integral of ψᵢ-piece)` and `∑ⱼ(chart-j integral of χⱼ-piece)` agree — proved via the
**common refinement** `{ψᵢ·χⱼ}ᵢⱼ` (a finite grid of compactly-supported-in-a-single-overlap
pieces; each product lies in *both* chart i's and chart j's domain, so `integral_wirtingerDbar_mul_chart_congr`
applies once per grid cell) and summing twice (once grouping by `i`, once by `j`), matching Čech
refinement bookkeeping in *flavor* only (no import from `Jacobian/Cech/` — that would be a DAG
deviation; the analogy is for the builder's intuition, the lemma itself is self-contained).

### 4.3 Assembly: Forster's `g := 1 - ∑fₖ` argument

File `Jacobian/ResidueTheorem/Theorem.lean`. With the finite pole-indexed pieces `{ψ_{inl p}}_{p ∈
ω.finite_poleSet.toFinset}` (each `≡ 1` on `Wₚ`, §4.1) and remainder pieces `{ψ_{inr ℓ}}_{ℓ<m}`
(each compactly supported in a chart avoiding every pole):

1. **Each pole piece.** In chart `chartAt ℂ p`, apply Atom 2 (§1.3,
   `integral_wirtingerDbar_mul_eq_neg_pi_mul_resAt`) with `g := ψ_{inl p} ∘ (chartAt ℂ p).symm`
   (`hconst` from §4.1's automatic constancy, `ψ_{inl p} ≡ 1` on `Wₚ`, an open neighborhood of `p`)
   and `f := ω.coeffAt p`, `p_local := chartAt ℂ p p`: gives
   `∫∫ wirtingerDbar(ψ_{inl p}-in-chart) · ω.coeffAt p = -π · ω.resAt p` (using `ψ_{inl p}(p) = 1`).
2. **Each remainder piece.** In chart `chartAt ℂ x_ℓ`, apply Atom 1b (§1.3,
   `integral_wirtingerDbar_mul_eq_zero_of_differentiableOn`) — `ω.coeffAt x_ℓ` is
   `DifferentiableOn ℂ` on all of `tsupport(ψ_{inr ℓ})` since that support avoids `ω.PoleSet`
   entirely (by construction, §4.1): gives `∫∫ wirtingerDbar(ψ_{inr ℓ}) · ω.coeffAt x_ℓ = 0`.
3. **The cross-chart identity.** `∑ᵢ (all pieces) Ⲓᵢ = ∑_p (-π·ω.resAt p) + ∑_ℓ 0` on one hand
   (direct evaluation, steps 1–2); on the other, `1 = ∑ᵢ ψᵢ` (PoU) gives, by the §4.2 common-refinement
   lemma applied between *this* decomposition and a **second, single-point** decomposition (`g := 1`
   read in any one fixed chart `e₀`, trivially `wirtingerDbar(1) ≡ 0`, giving total `0` — the
   "everything is secretly comparing against the constant function 1, whose `∂̄` is 0" step), the
   grand total is `0`. Concluding: `-π · ∑_p ω.resAt p = 0`, i.e. `∑_p ω.resAt p = 0` (dividing by
   `-π ≠ 0`). This is `residueTheorem` (§2).

*(Estimated 150–200 lines for this file: steps 1–2 are direct atom applications (~40 lines total,
one loop over a `Finset`), step 3 is the bulk, reusing §4.2's refinement lemma once (~80–120
lines of `Finset.sum` bookkeeping — pairing up the pole/remainder decomposition against the
single-chart-constant-1 decomposition via the common refinement, then discharging both `Finset.sum`
manipulations).*

---

## 5. Corollaries consumed downstream (bridges, not new proof content)

### 5.1 `Res(df) = 0`, pointwise — needs NOTHING from this unit

Not a consequence of the residue *theorem* at all: residue-calculus's own
`MeromorphicAt.resAt_deriv (hf : MeromorphicAt f z₀) : resAt (deriv f) z₀ = 0` (built,
`ResidueCalculus/Residue.lean:99`) gives, via canonical-forms's `MForm.d` unfolding (D7), that
`(MForm.d h).resAt x = 0` **at every single point** `x`, for any `h : ℳ X` — a strictly stronger,
pointwise fact requiring zero PoU/Stokes machinery. Worth stating here as a one-line bridge
(`MForm.resAt_d_eq_zero`) purely for discoverability, but it is not load-bearing for this unit's
own proof and does not need `residueTheorem`.

### 5.2 The argument principle / `deg(div f) = 0` (Forster 10.22) — a genuine, non-blocking bonus

`∑_x ordAt(f, x) = ∑_x (MForm.dlog f).resAt x = 0` combines `MForm.resAt_dlog` (canonical-forms
D7, §1.2) with `residueTheorem` applied to `ω := MForm.dlog f`. This is Forster's own Corollary
10.22 ("a non-constant meromorphic function has, counting multiplicities, as many zeros as poles"),
literally the next paragraph after 10.21 in the source. **Ownership note**: `proper-map-degree`'s
own blueprint entry explicitly routes `deg(div f) = 0` through **degree-counting** instead ("NOT
from a general manifold Stokes theorem... the general-Stokes route to `deg∘div=0` is a dead end")
— so this corollary is offered as a documented, independent cross-check / convenience, **not** a
dependency any other unit's frozen edge requires. State it (`deg_div_eq_zero_of_residueTheorem` or
similar) but do not let it block anything.

### 5.3 The load-bearing export: `residueTheorem`/`MForm.sum_resAt_eq_zero` themselves

This is what `serre-duality-tails` actually needs (its Serre-pairing residue map, Miranda VI.3, is
stated for an arbitrary `ω ∈ L⁽¹⁾(-D)`, not merely `dlog`-shaped forms) — see §7 for the DAG audit
confirming this is the *only* unit whose frozen edge points here.

---

## 6. Documented alternative in full: the trace-to-`ℙ¹` route

Designed in full as requested, notwithstanding §3's recommendation against adopting it *today*.
This is the Forster-avoiding, Miranda-VIII.3-style route: push `ω` down to `ℙ¹` along any
nonconstant meromorphic map, and get `∑Res=0` from elementary partial-fraction algebra on `ℙ¹`
instead of any 2-D integration. All signatures below are quoted from `form-trace-tower.md`'s own
design (its unit does not exist on disk, §0/§1.1) plus the already-built pieces it would sit on.

### 6.1 The three ingredients, and their current state

1. **A nonconstant holomorphic map `F : X → ℙ¹`.** Available *today*, fully built, zero sorries:
   `canonical-forms.exists_nonconstant_mero` (design-only, D9, gate-independent modulo file 5's
   finiteness-and-chi dependency) feeds `f.holoRepr` into mtrace's `RS.toP1`
   (`Jacobian/MeromorphicTrace/ToP1.lean`, **built**): `toP1 (f : X → ℂ) (x : X) : OnePoint ℂ`,
   `toP1_contMDiff (hf : MeromorphicOnX f univ) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (toP1 f)`,
   `toP1_not_const (hf) (hnc : NotEventuallyConstX f) : ¬∃c, ∀x, toP1 f x = c`. This part of the
   route has no gap.
2. **`resAtP1_trace_eq_sum`** (form-trace-tower D4, Miranda Lemma 3.2 globalized — the
   residue-trace compatibility `∑Res=0` would actually ride on):
   ```lean
   theorem resAtP1_trace_eq_sum {F : X → OnePoint ℂ} (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
       (hne : ¬ ∃ c, ∀ x, F x = c) {h : X → ℂ} (hh : MeromorphicOnX h Set.univ)
       {y₀ : OnePoint ℂ} (S : RS.FiberStack F y₀) :
       resAtP1 (RS.MTrace.trace F h) y₀ = ∑ i, resAtX F h (S.pt i)
   ```
   **Gated** on mtrace's `laurentCoeffAt_traceZk` (P6, open `sorry`, §0/§1.1) via
   `resAt_traceZkForm`, and on `RS.MTrace.trace`/`FunctionTrace.lean` (mtrace file 5, **not yet
   written at all**). Neither gap is closeable from within residue-theorem's own scope.
3. **`∑Res=0` on `ℙ¹` for a rational (elementary partial-fraction) form** (form-trace-tower's
   `RationalOnP1.lean`, D5, "task item 4"'s cheap base case): needs `exists_partialFraction`
   (finite-pole decomposition, built from `finite_support_divisor` + `principalPartAt`, both
   already available) plus a **new** "entire + polynomial growth ⟹ polynomial" Liouville-style
   lemma via `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` (mathlib, built, but no
   packaged corollary at the pin — form-trace-tower's own §1 confirms this, independently
   re-checked here). Then, for an elementary piece `c·(z-a)ⁿdz`, `∑Res=0` is a **three-case direct
   check** (`n ≤ -2`: `resAt = 0` since it is `RS.resAt_zpow_monomial`-shaped away from `n=-1`;
   `n = -1`: the residue is `c` at `a` and `0`/finite elsewhere, canceling against the *other*
   `ℙ¹`-chart reading of the same rational function at `∞` — the "sum of residues of a rational
   function over `ℂℙ¹` is 0" fact, itself classical and short once partial fractions are in hand;
   `n ≥ 0`: analytic, `resAt = 0` everywhere by `resAt_of_analyticAt`). form-trace-tower's own
   designer flags this whole item as "non-load-bearing... do not let it hold up" (§0.3) — even
   the unit that would own it does not treat it as a priority.

### 6.2 Assembling the route (schematic — not gated on residue-theorem's own scope, hence not
built here)

```lean
-- (1) pick F : X → ℙ¹ nonconstant, via canonical-forms + toP1.
-- (2) resAtP1_trace_eq_sum, summed over ALL fibres q : ℙ¹ (finitely many with nonempty fibre-sum
--     contribution, by properness/finiteness of the pole set): ∑_p Res_p(ω) = ∑_q Res_q(Tr_F ω).
-- (3) Tr_F ω is a rational (meromorphic-with-finite-poles) 1-form on ℙ¹ (mtrace's own
--     `traceZkForm`/`meromorphicAt_traceZkForm` give the local meromorphy; global rationality on
--     all of ℙ¹ needs the same Liouville-style closure fact as (6.1) item 3.
-- (4) ∑_q Res_q(Tr_F ω) = 0 by the elementary partial-fraction computation on ℙ¹ (6.1 item 3).
-- (5) Conclude ∑_p Res_p(ω) = 0. QED — NO Stokes, NO PoU, NO area integration anywhere.
```
Step (2)'s "sum over all fibres" bookkeeping (turning a sum over `X`'s poles into a sum over
`ℙ¹`'s points, each grouped by fibre via `RS.FiberStack`) is itself a genuine ~40–60 line argument
(finite fibre-sum reindexing, `Finset.sum_biUnion`-style), but strictly smaller than the Area-Gluing
atom of §4.2 — this is the concrete sense in which the route would be cheaper *once its
prerequisites exist*.

### 6.3 Why this is not adopted as primary today (recap of §3, made concrete)

Every one of steps (2)–(4) above is blocked on work outside this unit's control: (2) needs mtrace's
P6 sorry resolved and `FunctionTrace.lean` written (mtrace's job); (3)–(4) need form-trace-tower's
`RationalOnP1.lean` (flagged non-priority by its own designer) plus a new Liouville-style lemma. To
adopt this as primary, residue-theorem would need to either (a) block on two other units' unfinished,
non-priority work, or (b) absorb and build all of it itself, which is exactly the "form-trace-tower"
unit's job under the frozen DAG (blueprint edge: `form-trace-tower` — Builds on: meromorphic-trace
only; **not** residue-theorem) — i.e., doing so here would duplicate another unit's blueprint scope,
not merely deviate from an edge. Recommendation stands: **build primary route (§4) now; revisit
this route as a possible replacement (or a second, cross-checking proof) once form-trace-tower lands
with P6 resolved** — flagged to the orchestrator in §11.

---

## 7. Downstream map and a DAG audit (mirrors the pattern form-trace-tower/mtrace already used)

Re-reading `clean_room_blueprint.md`'s `Builds on:` edges (not just prose) for every unit that
*mentions* residues:

- **`serre-duality-tails`** — **Builds on: laurent-tails, proper-map-degree, residue-theorem,
  serre-duality-cech.** This is the *only* frozen edge into this unit. Its strategy text ("pair
  tails against holomorphic forms... Miranda VI.3") needs the *general* `∑Res=0` (their pairing is
  stated for arbitrary meromorphic 1-forms in `L⁽¹⁾(-D)`, via `MForm.OmegaSpace`, not just
  `dlog`-shaped ones) — `residueTheorem`/`MForm.sum_resAt_eq_zero` (§2) is exactly what they need,
  no bridge lemma required beyond stating it for their specific `ω`.
- **`serre-duality-cech`** — **Builds on: canonical-forms** (only). Despite the task brief's
  phrasing ("the statement bank serre-duality-cech... expect"), the frozen edge does **not**
  include residue-theorem. No direct export required here; any indirect need routes through
  `serre-duality-tails`.
- **`abel-weak-solutions`** — **Builds on: form-trace-tower, monodromy, planar-stokes-atoms.** Also
  does **not** include residue-theorem in its frozen edge, despite superficially residue-flavored
  prose elsewhere in the blueprint. No export required here either.

**Conclusion**: this unit's real downstream consumer is `serre-duality-tails` alone. No blueprint
edit filed (the DAG is accurate; only the task brief's own summary prose overstated the fan-out —
recorded here so no downstream builder mistakenly waits on a bridge lemma that was never planned).

---

## 8. File plan

| # | File | Content | Est. | Imports beyond mathlib |
|---|------|---------|------|-------------------------|
| 1 | `ResidueTheorem/Cutoff.lean` | Automatic-constancy lemma (§4.1, spike-verified), `MForm.PoleSet`/`finite_poleSet`/`resAt_eq_zero_of_ord_nonneg` Compat (§1.2 gap), the disjoint pole-disk + finite remainder cover construction | ~220 | `Jacobian.CanonicalForms`, `Jacobian.Surface.RealSmooth` |
| 2 | `ResidueTheorem/AreaGluing.lean` | The new Jacobian-determinant fact (§1.6), the chart-congruence atom (§4.2), the common-refinement corollary | ~230 | file 1, `Jacobian.Dbar.Wirtinger`, `Jacobian.LocalMultiplicity.ChartBridge`, `Mathlib.MeasureTheory.Function.Jacobian`, `Mathlib.RingTheory.Complex` |
| 3 | `ResidueTheorem/Theorem.lean` | Assembly (§4.3): `residueTheorem`, `MForm.sum_resAt_eq_zero`, the two bonus corollaries (§5.1–5.2) | ~200 | files 1–2, `Jacobian.PlanarStokes.{CompactSupport, AnnulusResidue}`, `Jacobian.ResidueCalculus.Residue` |
| 4 | `Jacobian/ResidueTheorem.lean` | Unit root, 5–15 line API docstring | ~25 | all |

Four files (within the 2–4 budget). Build waves: file 1 needs only canonical-forms's frozen files
1–2 (`MForm.lean`/`OrdRes.lean`, gate-independent of finiteness-and-chi, per canonical-forms's own
table) — buildable as soon as those land. File 2 is independent of file 3's needs beyond file 1;
it can be developed and checked in isolation (pure mathlib + Dbar + LocalMultiplicity, no
`AnnulusResidue` dependency). File 3 is the only file blocked on `AnnulusResidue.lean` landing in
`planar-stokes-atoms` (§1.3's ⚠) — build and check files 1–2 first regardless of that unit's
progress.

---

## 9. Exact signatures (consolidated export list)

```lean
namespace RS

-- Cutoff.lean
def MForm.PoleSet [T2Space X] [CompactSpace X] (ω : MForm X) : Set X
theorem MForm.resAt_eq_zero_of_ord_nonneg {ω : MForm X} {x} (h : 0 ≤ ω.ord x) : ω.resAt x = 0
theorem MForm.finite_poleSet [T2Space X] [CompactSpace X] (ω : MForm X) : ω.PoleSet.Finite
theorem SmoothPartitionOfUnity.eventuallyEq_one_of_forall_disjoint {ι}
    {p : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) X univ} {U : ι → Set X} (hp : p.IsSubordinate U)
    {x : X} {i : ι} {V : Set X} (hV : V ∈ 𝓝 x) (hVi : ∀ j ≠ i, V ∩ U j = ∅) : ∀ y ∈ V, p i y = 1
theorem exists_finite_poleCover [T1Space X] [T2Space X] [CompactSpace X] (ω : MForm X) :
    ∃ (n m : ℕ) (p : SmoothPartitionOfUnity (Fin n ⊕ Fin m) 𝓘(ℝ, ℂ) X univ)
      (poles : Fin n → X) (charts : Fin m → X),
      Function.Bijective poles ∧ ...  -- exact bundling left to the builder; see §4.1 narrative

-- AreaGluing.lean
theorem det_fderiv_eq_normSq_deriv {τ : ℂ → ℂ} {z : ℂ} (hτ : DifferentiableAt ℂ τ z) :
    LinearMap.det (fderiv ℝ τ z : ℂ →ₗ[ℝ] ℂ) = Complex.normSq (deriv τ z)
theorem integral_wirtingerDbar_mul_chart_congr {e e' : OpenPartialHomeomorph X ℂ} (he he')
    {g : ℂ → ℂ} {U : Set X} (hU) (hUe hUe') (hg) (hcs) (hsub) (ω : MForm X) (hf) :
    (* two chart readings of the same planar pairing integral agree — see §4.2 *)
theorem sum_integral_wirtingerDbar_mul_eq_of_common_refinement
    {ι κ : Type*} [Fintype ι] [Fintype κ] (* two finite chart-decompositions of the same
    smooth cutoff sum, each summand's own chart; conclude the two totals agree *) : True  -- schematic

-- Theorem.lean
def MForm.PoleSet ...   -- (re-exported)
theorem residueTheorem [T1Space X] [T2Space X] [CompactSpace X] (ω : MForm X)
    {S : Finset X} (hS : ω.PoleSet ⊆ (S : Set X)) : ∑ x ∈ S, ω.resAt x = 0
theorem MForm.sum_resAt_eq_zero [T1Space X] [T2Space X] [CompactSpace X] (ω : MForm X) :
    ∑ x ∈ ω.finite_poleSet.toFinset, ω.resAt x = 0
theorem MForm.resAt_d_eq_zero [T1Space X] (h : ℳ X) (x : X) : (MForm.d h).resAt x = 0     -- §5.1
theorem sum_ordAtX_eq_zero_of_residueTheorem [T1Space X] [T2Space X] [CompactSpace X]
    (f : ℳ X) (hf : f ≠ 0) {S : Finset X} (hS : (divisor f).support ⊆ (S : Set X)) :
    ∑ x ∈ S, ((f.ord x).untop₀ : ℤ) = 0                                                    -- §5.2

end RS
```

---

## 10. Risks & fallbacks

1. **R1 (MEDIUM, the unit's central risk): the Area-Gluing atom (§4.2) and its common-refinement
   corollary.** Both halves (determinant fact, transition algebra) are individually spike-verified
   or already-built; the *assembly* (threading `OpenPartialHomeomorph.trans`/`restr` correctly, and
   the `Finset.sum` bookkeeping of the common-refinement grid) is genuinely new "grind," comparable
   in flavor to other units' own top risks (canonical-forms' P1, form-trace-tower's P1). Budget
   200–300 lines, not the 150 estimated in §4.2, if the refinement bookkeeping proves fiddlier than
   expected. **Fallback**: state the common-refinement lemma only for the *specific* two
   decompositions §4.3 needs (pole+remainder vs. single-chart-constant-1), rather than a reusable
   "any two finite decompositions" lemma — strictly less general, but the only instance actually
   consumed, and removes one layer of abstraction if it resists.
2. **R2 (LOW-MEDIUM, scheduling): `AnnulusResidue.lean` (Atom 2) is not yet built.** File 3
   (`Theorem.lean`) cannot compile until `planar-stokes-atoms` lands it with the exact signature
   frozen in its own design doc (§1.3). This is a normal DAG dependency (not a deviation), but
   worth flagging since it is the one place this design's *interface*, not just its own proof, is
   contingent on another unit's remaining work landing unchanged.
3. **R3 (LOW): the `MForm.compat`/`resAt_eq_of_mem_source` shape drifts** once `canonical-forms`
   actually lands on disk (it is currently design-only). Per canonical-forms's own file-plan table,
   files 1–2 (which contain everything this unit consumes: `MForm`, `.compat`, `.ord`, `.resAt`,
   `.divisor`) are gate-independent of finiteness-and-chi and are architecturally the most stable
   part of that design (no dependence on the not-yet-resolved existence-chain machinery in its
   file 5) — low risk, but re-verify signatures against the actual file once it lands, not just
   this doc.
4. **R4 (LOW): the "T1 space, finite-minus-a-point is closed" step in §4.1's disjoint-disk
   construction.** Routine but not yet reduced to a one-line mathlib citation in this design;
   likely `Set.Finite.isClosed`/`isClosed_biUnion_finite` composed with `isOpen_compl_singleton`
   intersected finitely — a small `Compat` lemma if no direct hit exists.
5. **R5 (LOW, honest scope note): the common-refinement lemma's exact "two decompositions of the
   same object" hypothesis shape (§4.2, §9's schematic signature) is not fully pinned down in this
   design** — the *mathematical content* (proved via `integral_wirtingerDbar_mul_chart_congr`
   applied per grid cell, then double-counting the `Finset.sum`) is solid and spike-adjacent, but
   the precise Lean packaging (what exactly "two decompositions of the same function" means as a
   hypothesis) is left for the builder to finalize against the *specific* instance §4.3 needs,
   per the R1 fallback. This is a genuine "40+ line proof, sketch not full script" item, flagged
   honestly rather than papered over with a falsely-precise signature.

---

## 11. Coordination notes filed

- `docs/requests/canonical-forms.md`: request `MForm.resAt_eq_of_ord_nonneg` (§1.2's gap) as a
  first-class export — trivial (`RS.resAt_of_order_nonneg` composed with `MForm.resAt`'s
  definition), used here via local Compat meanwhile, but generically useful (laurent-tails and
  serre-duality-tails will likely also want "residue vanishes off the pole set" as a named fact).
- `docs/requests/planar-stokes.md`: none — Atom 1/1b/2's frozen signatures (§1.3) are exactly what
  is consumed; flagging only the scheduling dependency on `AnnulusResidue.lean` landing (§10 R2), not
  an interface request.
- `docs/requests/dbar-solvability.md`: none needed beyond what planar-stokes already filed
  (`wirtingerDbar_mul` upstreaming) — this unit's own new atom (§4.2) is deliberately scoped as
  residue-theorem-local (a chart-*comparison* fact tied to `MForm`, not a general `Form01` API
  addition), so it is not proposed for upstreaming to `Jacobian/Dbar/`.
- No blueprint edit filed for the DAG (§7): the frozen edges are accurate; only the blueprint's own
  summary prose overstated the fan-out to `serre-duality-cech`/`abel-weak-solutions`.

---

## 12. Spike report (`scratch_resthm.lean`, project root)

Gated per compile discipline (`pgrep -cx lean` was `0` at both attempts, under the limit of 3), run
`lake env lean scratch_resthm.lean`: **compiles clean, exit 0** (one round of import/naming fixes,
recorded for the next builder):

1. **The Jacobian-determinant fact** (§1.6/§4.2 item 1): `LinearMap.det (fderiv ℝ τ z : ℂ →ₗ[ℝ] ℂ)
   = Complex.normSq (deriv τ z)`, for `τ : ℂ → ℂ` with `hτ : DifferentiableAt ℂ τ z`, proved via
   `hτ.fderiv_restrictScalars ℝ`-style pointwise identification with `Algebra.lmul ℝ ℂ (deriv τ z)`
   (using the *unconditional* `fderiv_eq_deriv_mul`, no differentiability side-condition needed for
   the pointwise formula itself) followed by `Algebra.norm_apply`/`Algebra.norm_complex_apply`. This
   is the load-bearing measure-theoretic ingredient of the new Area-Gluing atom (§4.2) —
   **de-risked**: no exotic instance-search or restrict-scalars issues, ~10 lines once the right
   lemma names are found (`Algebra.coe_lmul_eq_mul`, `LinearMap.mul_apply'`, not
   `Algebra.lmul_apply`, which does not exist — recorded so the next builder doesn't re-search for
   it).
2. **The automatic-constancy finsum argument** (§4.1): for an abstract index type `ι`, function
   `ψ : ι → ℝ`, `i : ι`, `∑ᶠ j, ψ j = 1` and `∀ j ≠ i, ψ j = 0 ⟹ ψ i = 1`, proved by
   `finsum_eq_single ψ i hzero` rewritten against the sum-to-one hypothesis. **De-risked**: exactly
   the one-line mechanism the §4.1 cutoff construction needs; no surprises.

Import fix needed during the spike: the bare `Mathlib.RingTheory.Complex` +
`Mathlib.Analysis.Calculus.FDeriv.RestrictScalars` pair is insufficient on its own (`NontriviallyNormedField
ℂ`/`deriv` not in scope without a further complex-analysis import); adding
`Mathlib.Analysis.SpecialFunctions.Complex.Circle` (pulled in transitively by Dbar's own
`Wirtinger.lean` imports too) resolved it. `scratch_resthm.lean` left in the repo root per the
workflow; a builder may delete it once `AreaGluing.lean`/`Cutoff.lean` land.

---

## 13. Summary of what is NOT built here (scope discipline, restated)

No Serre pairing, no `H¹(Ω) → ℂ` functional (routing decision #2 — that is serre-duality-tails' job
via Miranda's tail route). No general manifold-Stokes theorem, no reusable "`∬_X ω` for arbitrary
smooth 2-forms on `X`" API (the Area-Gluing atom, §4.2, is deliberately scoped to the one
`wirtingerDbar`-against-`MForm` pairing this proof needs, not a general integration theory — mirrors
planar-stokes's own "prove exactly the one annulus identity needed" scope discipline, §4 D6 of that
design). No trace-to-`ℙ¹` machinery built (documented as the alternative route, §3, not
implemented — form-trace-tower's own gaps make it premature). No change to any other unit's frozen
interface.
## Orchestrator addendum (2026-07-07)

The route recommendation in this doc was made while mtrace P6 (laurentCoeffAt_traceZk) still
had a sorry. That sorry is CLOSED (MeromorphicTrace complete) and Jacobian/FormTrace/ is in
build. Therefore the BUILD order is inverted: **§6 trace route is PRIMARY**; the PoU+Stokes
route (§3-5) is the fallback if FormTrace's residue-trace compatibility or the P1 base case
slips. The Area-Gluing atom should NOT be built unless the fallback is triggered.
