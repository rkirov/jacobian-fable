# Requests: meromorphic-and-divisors

## From cech-cohomology (designer, see docs/design/cech-cohomology.md §8)

All three are small; if inconvenient to absorb, cech-cohomology will prove them locally in a
marked `Compat` section — nothing blocks either unit.

1. `linSysOn_mono (h : D ≤ D') : LinSysOn D U ≤ LinSysOn D' U`
   (carrier implication: `-(D' x) ≤ -(D x) ≤ ord`; one line next to `linSys_mono`).

2. `MeroGermOn.evalAt_eq_zero_iff (hU : IsOpen U) (hx : x ∈ U) (h : 0 ≤ φ.ord x) :
       φ.evalAt x = 0 ↔ 0 < φ.ord x`
   (from `tendsto_evalAt` + planar `tendsto_zero_iff_meromorphicOrderAt_pos` transported
   through the chart + `Filter.Tendsto.limUnder_eq` uniqueness — all atoms already in your
   verified list; natural home is `OrderEval.lean` next to `evalAt`).

3. Nice-to-have: `MeroGermOn.congrSet (h : U = V) : MeroGermOn X U ≃ₗ[ℂ] MeroGermOn X V`
   (restrict along `h.le`/`h.ge`, inverse by `restrict_restrict` + `restrict_id`), with
   `ord_congrSet`/`evalAt_congrSet` rigidity. Used to transport gluing targets
   `⋃ i, ↑(U i)` vs `↑Ω`. If skipped, cech builds it in Compat.

## From meromorphic-trace (design phase, 2026-07-06, non-blocking)

1. **DAG correction.** `clean_room_blueprint.md`'s `meromorphic-trace` entry omits
   `meromorphic-and-divisors` from "Builds on" even though there is no way to state "`f`
   meromorphic on `X`" without your `MeromorphicAtX`/`ordAtX` (`Predicates.lean`, already built)
   and the identity dichotomy (`CodiscreteBridge.lean`, already built). Please ask the
   orchestrator to add this edge; nothing blocks on it.

2. **`GermSpace.lean`/`OrderEval.lean` (`ℳ X`, `evalAt`, `holoRepr`) not yet built — we did not
   wait.** We needed a "canonical `ℙ¹`-valued value of a meromorphic function at a point" bridge
   for the argument principle (`f : X → ℂ` meromorphic ⇒ induced `F : X → ℙ¹` holomorphic). Built
   it locally and independently in `Jacobian/MeromorphicTrace/ToP1.lean` via a bespoke
   `limUnder (𝓝[≠]x) f`-based `toP1`, using only your **already-built**
   `MeromorphicAtX`/`ordAtX`/`tendsto_nhds_iff_ordAtX_nonneg` (`Predicates.lean`) — no dependency
   on the not-yet-built `evalAt`/`holoRepr` (D5 of your design doc).
   - Once `OrderEval.lean` lands with `evalAt`/`holoRepr`/`holoRepr_contMDiffAt` as designed,
     `toP1` should be re-expressed as `fun x => if 0 ≤ φ.ord x then ↑(φ.evalAt x) else ∞` for
     `φ : ℳ X`, and our `ToP1.lean` becomes a thin wrapper (or is dropped in favor of a genuine
     `ℳ.toP1` if you build one, per your own `docs/design/projective-line.md` §3.3
     "deliverable-for-later" note — coordinate with `projective-line` too, see
     `docs/requests/projective-line.md`). Non-blocking; we are not proposing to change your
     recorded `evalAt`/`holoRepr` signatures.
   - We also independently need (and re-derive, for now, inside `ArgumentPrinciple.lean`) a fact
     close to "if `MeromorphicOnX g univ` and `∀x, 0<ordAtX g x` then `g =ᶠ[codiscrete X] 0`" for
     our nonconstancy-transfer lemma (`toP1_not_const`). If `OrderEval.lean`'s `holoRepr` +
     `holoRepr_eventuallyEq_nhdsNE` land first, this becomes a two-line corollary of those
     ("`holoRepr g` is a genuine global holomorphic function, `0` everywhere by hypothesis,
     hence literally the zero function, hence `g` agrees with it off a codiscrete set") rather
     than the from-scratch argument we planned — happy to switch once available, no action
     needed from you now.

3. **Confirmation of exports we consume unchanged**: `MeromorphicAtX`, `MeromorphicOnX`,
   `ordAtX`, `ordAtX_def`, `ordAtX_congr` (meromorphy-free), `ordAtX_inv` (unconditional —
   load-bearing for our pole-case sign flip), `ordAtX_mul`, `tendsto_nhds_iff_ordAtX_nonneg`,
   `ordAtX_eq_of_mem_source`, `ordAtX_of_contMDiffAt_eq_zero`,
   `MeromorphicOnX.eventuallyEq_zero_or_forall_ordAtX_ne_top`,
   `MeromorphicOnX.codiscrete_setOf_ne_zero`, `eventuallyEq_codiscrete_iff`.

---

## From dbar-solvability (designer; see `docs/design/dbar-solvability.md` §8)

4. **Analytic ⇒ mero + nonnegative order** (for our `DiskAcyclic.lean` germ transport):
   (a) `meromorphicOnX_of_contMDiffOn_omega (hU : IsOpen U) (hu : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω u U) :
       MeromorphicOnX u U`;
   (b) for such `u`, `∀ x ∈ U, 0 ≤ (MeroGermOn.mk u ‹_›).ord x` (equivalently
       `0 ≤ ordAtX u x`), so `mk u ∈ LinSysOn 0 U`.
   Both are chart-transport one-liners over mathlib's `AnalyticAt.meromorphicAt` /
   `meromorphicOrderAt`-nonneg-of-analytic lemmas (`Analysis/Meromorphic/Order.lean`). If not
   absorbed, we prove them locally in a marked `Compat` section of `Jacobian/Dbar/DiskAcyclic.lean`
   — no blocking either way.
5. **(nice-to-have)** an `Iff.rfl`-grade `mem_linSysOn_iff : φ ∈ LinSysOn D U ↔ ∀ x ∈ U,
   (-(D x) : WithTop ℤ) ≤ φ.ord x` unfolding lemma, so consumers never touch the carrier.
