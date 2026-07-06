# Design: proper-map-degree (`Jacobian/ProperDegree/`)

Blueprint unit **proper-map-degree**. Blueprint text: "Degree of a global meromorphic map:
`ContMDiff.degree`, sheet counting, multiplicity patching, `deg(div f) = 0`, and degree-1 maps to
`S²` are homeomorphisms." Read: Forster §4, §17.9. ⚠ "get `deg(div f)=0` from the
argument-principle/degree route... not from a general manifold Stokes theorem." Declared **Builds
on:** monodromy.

Everything below verified by reading the actual files on disk (not just their design docs) for
every upstream unit, against pinned mathlib `548398201a64f3a5127d90d83945278cfe38cac4`. One gated
spike (`scratch_pmd.lean`, §7) compiled clean.

---

## 0. Verdict up front

**This is a small consolidation unit, not a new mathematical development.** Every headline
result the blueprint names — the mapping degree itself, sheet counting, multiplicity patching,
degree-1 ⇒ homeomorphism — is **already built** in `Jacobian/MappingDegree/` (a complete,
sorry-free, registered-eligible unit). The order↔multiplicity bridge to a meromorphic function's
zeros/poles is **already built** in `Jacobian/MeromorphicTrace/{ToP1,OrderMultiplicity}.lean`
(complete, sorry-free at time of writing). What remains for `proper-map-degree` is genuinely three
small pieces of **glue**, estimated **~370–460 lines across 3–4 files**:

1. The root-level `ContMDiff.degree` wrapper over `RS.degree` (a `rfl`-def + a couple of restated
   corollaries).
2. `divisor_degree_eq_zero` for `ℳ X`/`Divisor X` (repackaging the zeros=poles fact into CC2/CC3
   vocabulary) and its immediate corollary, the **unconditional** discharge of
   `Meromorphic.linSys_eq_bot_of_degree_neg`'s hypothesis.
3. `homeoSphere_of_exists_simple_pole`: the meromorphic-function-level finisher genus-zero-headline
   needs (single simple pole ⇒ degree-1 map to `ℙ¹` ⇒ `X ≃ₜ S²`), assembled from pieces in (1)
   plus `MappingDegree`/`MeromorphicTrace`/`ProjectiveLine`.

**The blueprint's `Builds on: monodromy` is wrong and should be dropped** — see §2. **Sheet
counting/multiplicity patching (item 5 of the task) needs no new content**: `MappingDegree`'s
`fiberMultSum_eq_finset_sum`/`ncard_fiber_*` family already covers everything downstream units cite
us for; they reach `MappingDegree` directly, not through us. See §6.

---

## 1. Gap analysis table (what exists where vs. what's genuinely new)

| Blueprint ask | Status | Where |
|---|---|---|
| The mapping degree itself | **Built, complete unit** | `Jacobian/MappingDegree/Degree.lean`: `RS.degree`, `fiberMultSum_eq_degree`, `degree_of_forall_eq`, `one_le_degree`, `degree_pos_iff`, `multiplicity_le_degree` |
| Sheet counting / regular-fiber cardinality | **Built** | `RS.ncard_fiber_of_isRegularValue`, `RS.ncard_fiber_le_degree` (`Degree.lean`); `RS.FiberStack`, `exists_fiberStack` (`LocalStructure.lean`) |
| Multiplicity patching (well-definedness of the fiber sum) | **Built** | `RS.fiberMultSum_const`, `RS.isLocallyConstant_fiberMultSum` (`LocalConstancy.lean`) |
| Degree-1 ⇒ homeomorphism | **Built** | `RS.bijective_of_degree_eq_one`, `RS.homeomorphOfDegreeEqOne`, `RS.isHomeomorph_of_degree_eq_one` (`Degree.lean`) |
| Degree multiplicativity | **Built** (statement bank) | `RS.degree_comp` (`Degree.lean`) |
| `f`-to-`ℙ¹` bridge (`toP1`), its holomorphy | **Built** | `RS.MTrace.toP1`, `toP1_contMDiff` (`MeromorphicTrace/ToP1.lean`) |
| Order↔multiplicity bridge at zeros/poles | **Built** | `RS.MTrace.multiplicity_toP1_of_ordAtX_pos/neg` (`MeromorphicTrace/OrderMultiplicity.lean`) |
| The finsum argument-principle identity `∑ᶠ ordAtX = 0` | **Designed, NOT yet built** | `docs/design/meromorphic-trace.md` §2 D5, §4.3 — file `MeromorphicTrace/ArgumentPrinciple.lean` does not exist on disk yet (only `ToP1.lean`/`OrderMultiplicity.lean`/`PlanarTrace.lean` of the 5-file plan exist; `ArgumentPrinciple.lean`/`FunctionTrace.lean` are missing) |
| `ℳ X`, `divisor`, `Divisor.degree`, `LinSys`, `l` | **Built, complete unit** | `Jacobian/Meromorphic/{GermSpace,OrderEval,Field,Divisor,LinearSystem}.lean` |
| `L(D) = 0` for `deg D < 0` | **Built, but CONDITIONAL** | `RS.linSys_eq_bot_of_degree_neg (hdeg : ∀φ≠0, (divisor φ).degree=0) (h : D.degree<0) : LinSys D = ⊥` (`LinearSystem.lean:206`) — the `hdeg` hypothesis is *exactly* what this unit must discharge |
| `ℙ¹ ≃ₜ S²` | **Built, complete unit** | `RS.P1.homeoSphere` (`ProjectiveLine/Sphere.lean`) |
| `ContMDiff.degree` (challenge signature) | **Not built** (genuinely ours) | new, §3.1 |
| `deg(div f) = 0` in `ℳ X`/`Divisor` terms | **Not built** (genuinely ours — the "few lines of bookkeeping" mtrace's design doc explicitly defers to us) | new, §3.2 |
| Meromorphic single-simple-pole ⇒ `X ≃ₜ S²` | **Not built anywhere** (genuinely ours) | new, §3.3 |

**Bottom line**: of the blueprint's four headline items, three (degree, sheet counting, degree-1⇒
homeo) are *fully discharged by MappingDegree already*; the fourth (`deg(div f)=0`) has its hard
mathematical content *already proved* by `MeromorphicTrace`'s built `ToP1`/`OrderMultiplicity`
files (the missing `ArgumentPrinciple.lean` is a "statement + one lemma" repackaging away, per
mtrace's own P3 proof plan, §4 below) — and the genus-zero finisher is a straightforward assembly
of already-built parts. There is no undischarged deep mathematics left for this unit.

---

## 2. The `Builds on: monodromy` DAG correction

**Verdict: spurious. Drop it.** Evidence:

1. `Jacobian/Monodromy/` does not exist — the monodromy unit is not built, has no design doc, and
   nothing in this project currently exports anything under that name.
2. `MappingDegree` (which does essentially all of the "degree"/"sheet counting"/"degree-1⇒homeo"
   content the blueprint assigns to us) was built **without any monodromy dependency** — its whole
   machinery is `FiberStack`/chart-adapted local structure (Forster 4.24's proof mechanism), a
   purely local-to-global patching argument, not a continuation-of-primitives argument.
3. `MeromorphicTrace`'s `ToP1`/`OrderMultiplicity` (the order↔multiplicity bridge we consume) is
   likewise built from chart-local analytic-repair arguments (`holoRepr`, `meromorphicOrderAt`),
   again with zero monodromy content; its design doc's own D6 route decision for the *unrelated*
   `traceZk` atom explicitly says "**no monodromy**... Monodromy is avoided because `traceZk` is
   defined via the abstract root *set*... local branches are only ever used to witness analyticity
   at a fixed point, never to assemble a global formula that would need patching across branch
   cuts."
4. `sphere-topology` (a different, already-complete unit near this part of the DAG) states in its
   own root docstring: "no van Kampen, no universal cover, **no covering-space monodromy
   anywhere**." If even the topology of `ℙ¹`/simple-connectedness manages without monodromy, there
   is no reason a meromorphic function's degree-counting would need it.
5. The actual `monodromy` blueprint entry (`Monodromy/`) is about a completely different problem:
   *global primitives of holomorphic 1-forms on a simply-connected surface* (chain-of-charts
   continuation replacing ∫ as a primitive), consumed by `abel-weak-solutions`/period theory —
   nothing to do with counting sheets of a map to `ℙ¹`.

**Recommended DAG correction** (for the orchestrator, mirroring the correction meromorphic-trace
already filed for its own entry): `proper-map-degree`'s `Builds on:` line should read
`mapping-degree, meromorphic-and-divisors, meromorphic-trace, projective-line` — **not**
`monodromy`. (This matches `mapping-degree.md`'s own downstream table, §7 there, which already
lists `proper-map-degree` as a consumer of `fiberMultSum_eq_degree`/`fiberMultSum_eq_finset_sum` —
the edge was simply mislabeled in the blueprint, the same class of slip meromorphic-trace's
designer already caught and filed for their own entry.)

**Secondary observation (flag, don't overreach):** the blueprint's `genus-zero-headline` entry
lists `Builds on: riemann-roch` only, yet per the task's own brief (and confirmed by our §3.3
design) genus-zero-headline's forward direction will call `RS.homeoSphere_of_exists_simple_pole`
**directly** from this unit, not merely transitively through riemann-roch. Recommend the
orchestrator also add `proper-map-degree` to `genus-zero-headline`'s `Builds on:` list. Filed
non-blocking (this unit's own build does not depend on that correction being made).

---

## 3. File plan and exact signatures

| # | File | Content | Est. lines |
|---|------|---------|-----------|
| 1 | `ProperDegree/ChallengeDegree.lean` | `_root_.ContMDiff.degree`, `degree_eq`, `degree_comp` (wrapper) | ~80–110 |
| 2 | `ProperDegree/DivisorDegreeZero.lean` | `divisor_degree_eq_zero`, Finset corollary, unconditional `LinSys`-vanishing discharge | ~150–220 (self-contained fallback) or ~40–60 (if mtrace's `ArgumentPrinciple.lean` has landed — see §5 R1) |
| 3 | `ProperDegree/GenusZeroFinisher.lean` | `homeoSphere_of_exists_simple_pole` | ~80–120 |
| 4 | `Jacobian/ProperDegree.lean` | unit root, API docstring | ~25–35 |

Total: **~335–485 lines**, matching the "small consolidation unit" expectation.

### 3.1 `ChallengeDegree.lean`

Standing variables per `CONVENTIONS.md` (both `X` and `Y` are **full** compact connected Riemann
surfaces — the challenge file's own `variable {Y :...}` block at `docs/Jacobian_challenge.lean:101`
carries the same five instances as `X`, so `[CompactSpace Y]`/`[ConnectedSpace Y]` are available
for free, in particular discharging `RS.degree_comp`'s `[CompactSpace Y]` need and `RS.degree`'s
`[Nonempty Y]` need via mathlib's `ConnectedSpace.toNonempty` instance,
`Mathlib/Topology/Connected/Basic.lean:634` — confirmed present at the pin, no risk).

```lean
variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {f : X → Y}

/-- The degree of a holomorphic map between compact Riemann surfaces (challenge signature).
Equal to `0` for constant maps (`RS.degree_of_forall_eq`), otherwise the usual mapping degree
(`RS.degree`). One-line wrapper — `RS.degree` already has the right junk-`0` convention
definitionally, no case split needed. -/
noncomputable def _root_.ContMDiff.degree (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ := RS.degree f

@[simp] theorem _root_.ContMDiff.degree_eq (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    hf.degree = RS.degree f := rfl

/-- Restated junk convention in wrapper form (`RS.degree_of_forall_eq`, unfolded). -/
theorem _root_.ContMDiff.degree_of_forall_eq {c : Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun _ : X => c)) :
    hf.degree = 0 := by rw [ContMDiff.degree_eq]; exact RS.degree_of_forall_eq c

/-- Functoriality, restated in wrapper form (statement bank; no critical consumer identified,
kept for API parity with `RS.degree_comp`). -/
theorem _root_.ContMDiff.degree_comp {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    [ConnectedSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    {g : Y → Z} (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hneG : ¬ ∃ c, ∀ y, g y = c) (hneF : ¬ ∃ c, ∀ x, f x = c) :
    (hg.comp hf).degree = hg.degree * hf.degree := by
  simp only [ContMDiff.degree_eq]; exact RS.degree_comp hg hf hneG hneF
```

No proof risk here — every RHS citation is a already-built, sorry-free `MappingDegree` lemma; this
file is pure `rfl`/`simp` bookkeeping.

### 3.2 `DivisorDegreeZero.lean`

```lean
namespace RS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **`deg(div φ) = 0`** for nonzero `φ : ℳ X` — the argument principle, repackaged from
`MeromorphicTrace`'s order/multiplicity bridge into `Divisor`/CC2 terms. Consumed by
`serre-duality-tails`/`riemann-roch` (mainly via the corollary below). -/
theorem divisor_degree_eq_zero (φ : ℳ X) (hφ : φ ≠ 0) : (divisor φ).degree = 0

/-- Finset padding corollary (matches `Divisor.degree`'s definitional Finset shape; free from
`Function.locallyFinsuppWithin.degree_eq_sum_of_subset`). -/
theorem sum_ord_eq_zero_of_finite {φ : ℳ X} (hφ : φ ≠ 0) {s : Finset X}
    (hs : (divisor φ).support ⊆ (s : Set X)) :
    ∑ x ∈ s, divisor φ x = 0 := by
  rw [← Function.locallyFinsuppWithin.degree_eq_sum_of_subset hs]; exact divisor_degree_eq_zero φ hφ

/-- The **unconditional** discharge of `Meromorphic.linSys_eq_bot_of_degree_neg`'s `hdeg`
hypothesis — the whole point of routing `deg(div f)=0` through this unit. -/
theorem linSys_eq_bot_of_degree_neg' [T2Space X] (D : Divisor X) (h : D.degree < 0) :
    LinSys D = ⊥ :=
  RS.linSys_eq_bot_of_degree_neg (fun φ hφ => divisor_degree_eq_zero φ hφ) h

end RS
```

(`linSys_eq_bot_of_degree_neg'` — primed, since the unprimed name is already taken by
`Meromorphic/LinearSystem.lean`'s conditional lemma in the same `RS` namespace; cannot rename
their declaration, per `CONVENTIONS.md` rule 4 — edit only this unit's directory.)

**Proof plan for `divisor_degree_eq_zero`** (the one real proof obligation in this unit):

1. `obtain ⟨f, hf, rfl⟩ := MeroGermOn.exists_rep φ` (φ = `mk f hf`).
2. Case split on constancy: `by_cases hc : ∃ c : ℂ, MeroGermOn.mk f hf = algebraMap ℂ (ℳ X) c`.
   - **Constant case**: `obtain ⟨c, rfl⟩ := hc`; `rw [divisor_algebraMap]`; degree of the zero
     divisor is `0` (`Function.locallyFinsuppWithin.degree_zero`). ~3 lines.
   - **Nonconstant case**: `push_neg at hc`. Translate to mtrace's raw-function nonconstancy
     predicate: `hnc : MTrace.NotEventuallyConstX f := fun c hcontra => hc c (by
     rw [MeroGermOn.algebraMap_mk]; exact MeroGermOn.mk_eq_mk.2 (by filter_upwards [hcontra] with
     x hx; linarith [hx] <;> ring_nf ... )` — a short filter/`sub_eq_zero`-massage translating
     `(f - c) =ᶠ[codiscrete X] 0` to `f =ᶠ[codiscreteWithin univ] (fun _ => c)`
     (`codiscreteWithin univ = codiscrete X` definitionally). ~10–15 lines.
   - Apply `MTrace.toP1_not_const hf hnc` to get `hne : ¬∃c,∀x, MTrace.toP1 f x = c`.
   - Set `F := MTrace.toP1 f`, `hF := MTrace.toP1_contMDiff hf`.
3. **The zeros=poles accounting** — this is exactly mtrace's own planned P3 proof
   (`docs/design/meromorphic-trace.md` §5 P3), reproduced here in `ℳ X`/`Divisor` vocabulary
   instead of the bare `∑ᶠ x, (ordAtX f x).untop₀ = 0` shape:
   - `RS.fiberMultSum_eq_degree hF hne (0 : OnePoint ℂ)` and `... (∞ : OnePoint ℂ)` give
     `fiberMultSum F 0 = degree F = fiberMultSum F ∞`.
   - `RS.fiberMultSum_eq_finset_sum` (using `RS.fiber_finite hF hne` at both `0` and `∞`) unfolds
     both sides to `Finset.sum`s over the (finite) zero-fiber and pole-fiber.
   - Termwise, `multiplicity F x` on the zero-fiber is `(ordAtX f x).untop₀` (positive orders, via
     `MTrace.multiplicity_toP1_of_ordAtX_pos`, cast `ℤ→ℕ`) and on the pole-fiber is
     `-(ordAtX f x).untop₀` = `(-ordAtX f x).untop₀` (via `_neg`, cast similarly). Equating the two
     `Finset.sum`s and moving everything to one side gives
     `∑_{x: ord>0} (ord f x).untop₀ + ∑_{x: ord<0} (ord f x).untop₀ = 0` (as integers).
   - The zero-fiber Finset ∪ pole-fiber Finset is exactly `(divisor φ).support` (as a Finset):
     `divisor φ x ≠ 0 ↔ (ordAtX f x).untop₀ ≠ 0 ↔ ordAtX f x ≠ 0 ∧ ordAtX f x ≠ ⊤ ↔ 0 < ordAtX f x
     ∨ ordAtX f x < 0` (`⊤`-points have `divisor φ x = 0` by `untop₀`'s junk convention, matching
     `divisor_apply`), so summing `divisor φ x = (ordAtX f x).untop₀` over this Finset (via
     `Function.locallyFinsuppWithin.degree_eq_sum_of_subset`) IS the equation just established.
   - Assemble: `(divisor φ).degree = 0`.

Est. **110–150 lines** for the nonconstant case (mechanical `WithTop ℤ`/`ℤ`/`ℕ` cast bookkeeping,
`omega`-closeable once the order identities are `have`d, per mtrace's own estimate for the
mathematically-identical P3). See §5 R1 for the "cite instead of reprove" fallback if
`ArgumentPrinciple.lean` lands first.

### 3.3 `GenusZeroFinisher.lean`

```lean
namespace RS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The meromorphic-function version of degree-1 ⇒ homeomorphism**: a single simple pole (no
other poles) forces the induced `ℙ¹`-valued map to have degree exactly `1`, hence `X` is
homeomorphic to `ℙ¹`, hence to `S²`. This is genus-zero-headline's forward-headline finisher; the
caller (riemann-roch's genus-0 single-simple-pole existence result) supplies `φ` and the pole
location `Q` — no other data. `φ ≠ 0`/nonconstancy of `φ` are *derived*, not required: `φ.ord Q =
-1` alone already rules out both (a nonzero constant has `ord ≡ 0`; `0` has `ord ≡ ⊤`). -/
theorem homeoSphere_of_exists_simple_pole (φ : ℳ X) (Q : X) (hpole : φ.ord Q = -1)
    (hreg : ∀ x, x ≠ Q → 0 ≤ φ.ord x) :
    Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)

end RS
```

**Proof plan** (~80–120 lines):

1. `obtain ⟨f, hf, rfl⟩ := MeroGermOn.exists_rep φ`; transport `hpole`/`hreg` to `ordAtX f Q = -1`
   / `∀ x ≠ Q, 0 ≤ ordAtX f x` via `MeroGermOn.ord_mk isOpen_univ (mem_univ _)`.
2. `F := MTrace.toP1 f`, `hF := MTrace.toP1_contMDiff hf`.
3. `hFQ : F Q = ∞ := MTrace.toP1_eq_infty_iff.2 (by rw [hpole]; decide)` (`(-1 : WithTop ℤ) < 0`).
4. **Nonconstancy, derived directly (no need for `toP1_not_const`/`NotEventuallyConstX`'s codiscrete
   machinery — a strictly easier argument suffices here)**: surface perfectness
   (`RS.nhdsNE_neBot Q`, already an instance from `Jacobian/Surface/Identity.lean`, re-exported by
   `MappingDegree`) gives `({Q}ᶜ : Set X) ∈ 𝓝[≠] Q` (`self_mem_nhdsWithin`), hence (`Filter.
   nonempty_of_mem`) `∃ x₀, x₀ ≠ Q`. By `hreg x₀`, `ordAtX f x₀ ≥ 0`, so (`MTrace.toP1_eq_infty_iff`,
   contrapositive) `F x₀ ≠ ∞`. Since `F Q = ∞ ≠ F x₀`, `F` is not constant:
   `hne : ¬∃c,∀x,F x=c := fun ⟨c,hc⟩ => (hc x₀ ▸ hc Q ▸ hFQ ▸ rfl : F x₀ = F Q) ▸ ...` (short
   `by_contra`/direct contradiction, ~10 lines). *No dependency on mtrace's `NotEventuallyConstX`
   or `toP1_not_const` at all* — cheaper than §3.2's route because we already have an explicit
   witness point (`Q`) with a *known* value (`∞`), unlike the general nonconstancy argument.
5. **`degree F = 1`**: the fiber `F ⁻¹' {∞}` equals `{Q}`.
   - `⊇`: `hFQ`.
   - `⊆`: if `F x = ∞` then (`toP1_eq_infty_iff`) `ordAtX f x < 0`; if `x ≠ Q` this contradicts
     `hreg x`; so `x = Q`.
   - `fiberMultSum F ∞ = multiplicity F Q` (singleton fiber sum, `finsum_mem_singleton`-style) `= 1`
     (`MTrace.multiplicity_toP1_of_ordAtX_neg hf (hpole ▸ ...)`, giving `(multiplicity F Q : ℤ) =
     -(ordAtX f Q).untop₀ = -(-1) = 1`, cast to `ℕ`).
   - `RS.fiberMultSum_eq_degree hF hne ∞` converts this to `degree F = 1`.
6. `X ≃ₜ OnePoint ℂ` via `RS.homeomorphOfDegreeEqOne hF hne (step 5)`.
7. Compose with `RS.P1.homeoSphere : OnePoint ℂ ≃ₜ Metric.sphere ...`.
8. `exact ⟨(RS.homeomorphOfDegreeEqOne hF hne h1).trans RS.P1.homeoSphere⟩`.

Every named citation in this plan (`toP1`, `toP1_contMDiff`, `toP1_eq_infty_iff`,
`multiplicity_toP1_of_ordAtX_neg`, `nhdsNE_neBot`, `fiberMultSum_eq_degree`,
`homeomorphOfDegreeEqOne`, `P1.homeoSphere`) is **already built and sorry-free** — this file has
zero dependency on `MeromorphicTrace`'s not-yet-built `ArgumentPrinciple.lean`/`FunctionTrace.lean`,
unlike §3.2's fallback route. This is the *safest* file to build first if §3.2's mtrace-adjacent
bookkeeping proves fiddlier than estimated.

### 3.4 `Jacobian/ProperDegree.lean` (unit root)

Standard root docstring per `CONVENTIONS.md` §Workflow step 5: 5–15 lines summarizing the three
exports above plus the DAG correction note (§2) for downstream readers, mirroring how
`meromorphic-trace`'s and `mapping-degree`'s own root docstrings record their DAG corrections.

---

## 4. Why `deg(div f)=0`'s hard content is already discharged (recap of the routing decision)

The blueprint's ⚠ insists on the **argument-principle/degree-counting route** ("count zeros = count
poles = degree"), explicitly forbidding a general Stokes-theorem route. This is *exactly* the route
`mapping-degree.md`'s own downstream table already prescribes (§7 there: "`fiberMultSum_eq_degree`
at `y:=0`, `y:=∞`") and *exactly* the route `meromorphic-trace.md`'s P3 proof plan uses (§5 there).
Both upstream designers independently converged on the same strategy the blueprint mandates; this
unit's job is purely to execute the *last* step of that already-planned route (repackaging into
`Divisor`/`ℳ X` vocabulary) — see §3.2. No alternative route (residues, Stokes, monodromy) is
needed or considered.

---

## 5. Risks

1. **HIGH-then-LOW, timing-dependent — `MeromorphicTrace/ArgumentPrinciple.lean` is designed but
   not yet built.** At the time of this design, `Jacobian/MeromorphicTrace/` contains `ToP1.lean`
   (0 sorries), `OrderMultiplicity.lean` (0 sorries), `PlanarTrace.lean` (1 documented sorry, in
   unrelated cluster-2 content); `ArgumentPrinciple.lean` and `FunctionTrace.lean` (files 3 and 5
   of mtrace's own 5-file plan) do not exist on disk yet, and `docs/build-log.md` has no `[mtrace]`
   entries at all — this upstream unit is genuinely mid-flight. **Mitigation**: §3.2's proof plan
   is *self-contained* — it re-derives the same finsum/fiber identity mtrace's own P3 would supply,
   using only the **already-landed** `ToP1.lean`/`OrderMultiplicity.lean` plus `MappingDegree`
   (complete). **Adapter note for the builder**: check whether
   `Jacobian/MeromorphicTrace/ArgumentPrinciple.lean` exists on disk *at build time*; if it does
   and exports `finsum_ordAtX_eq_zero`/`sum_ordAtX_eq_zero_of_finite` as designed, cite it directly
   (§3.2 collapses to ~40–60 lines of pure repackaging, no re-derivation); if not, use the
   self-contained ~110–150 line route in §3.2 verbatim — **do not block waiting for mtrace**. Note
   for §3.3: it needs *none* of this — it is independent of the whole risk.
2. **MEDIUM — multi-builder churn.** This is a live, concurrently-built repository (per
   `docs/build-log.md`, ~15 units built or in progress). During this design session,
   `Jacobian/MeromorphicTrace/OrderMultiplicity.lean`'s line count was observed to shift (178→181
   lines between two reads, no sorry either time) — some other agent is actively touching files
   this unit depends on. **Action**: re-verify every cited lemma's exact name/signature immediately
   before writing code that depends on it (`grep`/`lake env lean` a one-line check), do not trust
   this document's line numbers/exact wording as gospel by build time.
3. **LOW — `WithTop ℤ`/`ℤ`/`ℕ` cast bookkeeping** in §3.2's zeros=poles accounting and §3.3's
   `multiplicity F Q = 1` computation. Mechanical but fiddly (mirrors mtrace's own flagged risk #4
   for the mathematically identical computation); budget extra time, keep every cast in an
   explicit `have`, lean on `omega`/`push_cast`.
4. **Resolved, not a risk** — `[Nonempty Y]` for `RS.degree`/`ContMDiff.degree`: discharged for
   free by mathlib's `ConnectedSpace.toNonempty` instance (`Topology/Connected/Basic.lean:634`,
   confirmed present at the pin), matching the challenge file's own v0.3 changelog note ("drop
   `[Nonempty X]` in the presence of `[ConnectedSpace X]`").
5. **Naming collision, handled in the plan**: `Meromorphic/LinearSystem.lean` already declares
   `RS.linSys_eq_bot_of_degree_neg` (conditional); our unconditional discharge is named
   `RS.linSys_eq_bot_of_degree_neg'` (§3.2) to avoid redeclaring in the same namespace — we cannot
   rename their lemma (edit scope is this unit's directory only, `CONVENTIONS.md` rule 4).

---

## 6. Sheet counting / multiplicity patching — sufficiency check (task item 5)

Checked `serre-duality-tails`'s and `riemann-roch`'s blueprint entries (`clean_room_blueprint.md`)
for what they actually cite `proper-map-degree` for: `serre-duality-tails` lists us as a direct
`Builds on` dependency but its own text ("the multiplication action on `H¹`-tails, surjectivity, the
order downgrade, `h¹(D)=l(K−D)`") never mentions sheet-counting directly — per mtrace's own
downstream table (`meromorphic-trace.md` §8, row `proper-map-degree`), the *only* concrete thing
serre-duality-tails/riemann-roch need from this chain is `deg(div f)=0` (feeding
`linSys_eq_bot_of_degree_neg'`, §3.2, likely used as a base case in whatever induction
riemann-roch's own proof uses for small/negative-degree divisors). Meanwhile `form-trace-tower`
and `laurent-tails` — the units that actually *consume* `FiberStack`/multiplicity-patching directly
— reach `MappingDegree` **directly** per the blueprint's own edges (`meromorphic-trace: Builds on
mapping-degree`, corrected; `laurent-tails: Builds on canonical-forms, meromorphic-trace`), not
through `proper-map-degree`. **Conclusion: no additional sheet-counting/multiplicity-patching
content belongs in this unit.** `MappingDegree`'s existing `fiberMultSum_eq_finset_sum`,
`ncard_fiber_of_isRegularValue`, `ncard_fiber_le_degree` already suffice for every downstream need;
this unit only forwards the `deg(div f)=0` fact and the genus-zero finisher.

---

## 7. Spike report (`scratch_pmd.lean`, project root)

Gate respected (`pgrep -cx lean` < 3 at run time). `lake env lean scratch_pmd.lean`: **compiles
clean, exit 0** (imports: `Jacobian.MappingDegree`, `Jacobian.MeromorphicTrace.OrderMultiplicity`,
`Jacobian.Meromorphic.LinearSystem`). Verified three load-bearing facts:

1. `Meromorphic.linSys_eq_bot_of_degree_neg` applied to an assumed `∀φ≠0,(divisor φ).degree=0`
   hypothesis produces the unconditional `LinSys D = ⊥` — confirms §3.2's `linSys_eq_bot_of_degree_neg'`
   composition typechecks exactly as planned.
2. `∃ x, x ≠ Q` derived from `self_mem_nhdsWithin` + `Filter.nonempty_of_mem` against `𝓝[≠] Q` —
   confirms §3.3 step 4's nonconstancy witness is available with zero extra imports beyond what
   `MappingDegree` already re-exports (`RS.nhdsNE_neBot`).
3. `RS.fiberMultSum_eq_degree` (from `MappingDegree`) applied directly to `F := RS.MTrace.toP1 f`
   with `hF := RS.MTrace.toP1_contMDiff hf` (from `MeromorphicTrace`) — confirms the two
   already-built units compose exactly as §3.2/§3.3's proof plans assume, with no import conflict
   and no missing bridge lemma.

All three compiled with **zero sorries** (no proof obligations were stubbed — these are genuine
`exact`/term-mode proofs against the cited lemmas' real signatures, not placeholders).

---

## 8. Downstream map

| Consumer | What it needs | Our export |
|---|---|---|
| **serre-duality-tails** | `deg(div f)=0` (cited "mainly" per blueprint text) | `RS.divisor_degree_eq_zero`, `RS.linSys_eq_bot_of_degree_neg'` |
| **riemann-roch** | (transitively via serre-duality-tails, and plausibly directly for a negative-degree base case in its own induction) | `RS.linSys_eq_bot_of_degree_neg'` |
| **genus-zero-headline** | single-simple-pole ⇒ `X ≃ₜ S²` (the forward-headline finisher; supplies `(φ, Q)` from riemann-roch's genus-0 existence result) | `RS.homeoSphere_of_exists_simple_pole` |
| **final assembly** (`ContMDiff.degree`, `pushforward_pullback`) | the challenge-signature degree, junk-0, functoriality | `_root_.ContMDiff.degree`, `.degree_eq`, `.degree_of_forall_eq`, `.degree_comp` |

No other unit needs anything further from `proper-map-degree` per the current blueprint edges
(corrected as in §2).
