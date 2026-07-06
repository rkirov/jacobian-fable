import Jacobian.Abel.Loops
import Jacobian.Abel.WeakToMero
import Jacobian.Abel.Sufficiency
import Jacobian.Abel.OfCurveInj

/-!
# abel-theorem: Abel's theorem (Forster 20.7, dissection-free), `ofCurve_inj`

Unit: abel-theorem (`docs/design/abel-theorem.md`). Blueprint #29: "Abel's theorem (Forster 20.7,
dissection-free): the two-point Abel–Jacobi value is nonzero for distinct points on `g ≥ 1`, hence
`ofCurve` is **injective**." Namespace `RS.Abel` for the internal proof pipeline; `Jacobian` for
the challenge-shaped final exports. No fundamental-polygon/cut-surface machinery anywhere (the
blueprint's ⚠ is honored); no `Jacobian.Monodromy`/`Jacobian.FormTrace` import anywhere in this
unit (confirmed at build time, matching the design's DAG audit §3).

**PARTIAL UNIT** — one theorem (`RS.Abel.exists_mero_of_pathIntegral_mem`) has ONE documented
admitted step, precisely isolated, for a genuine EXTERNAL blocker (`serre-duality-tails`, entirely
unbuilt — see `Sufficiency.lean`'s own status section for the full account). Everything else,
including the general multi-chart weak-solution gap this builder was separately authorized to
close inside `Jacobian/AbelWeak/`, is complete with zero admitted steps. `scripts/check.sh
Jacobian/Abel` therefore reports exactly one flagged line (the one admitted step), not a build
error — flagged loudly here, in `Sufficiency.lean`'s own docstring, and in the final build-log
entry.

## The AbelWeak gap closure (authorized edit, not part of this unit's own files)

This unit's design (`docs/design/abel-theorem.md` §2.1) needs the FULLY GENERAL two-point weak
solution `RS.AbelWeak.exists_weakSolutionOfPair` (for an arbitrary connecting path, not confined
to one chart) — `abel-weak-solutions`' own build pass had explicitly left this as a documented
gap (a missing "rechart" lemma for `IsWeakSolutionAt` across chart transitions). This builder
closed it, as authorized, inside `Jacobian/AbelWeak/` (`Rechart.lean` + `GeneralChain.lean`, zero
sorries, `scripts/check.sh Jacobian/AbelWeak` passes) — see that unit's own root docstring for the
full mathematical account (the removable-singularity-theorem rechart lemma, the general
order-additive `IsWeakSolutionAt.mul`, and the chain induction gluing `SingleChart` pieces at
every breakpoint, including the case where the path revisits its own basepoint).

## API summary

* **`Loops.lean`** (§4.2 D2, §2.1 steps 1-3): `mem_periodSubgroup_iff_exists_loop` (`RS.
  periodSubgroup X`'s generating set is already closed under the loop operations, so its closure
  is exactly the based-loop period vectors, via `AddSubgroup.closure_induction`) and
  `exists_zeroPeriod_path` (the loop-cancellation construction: given `δ`'s basis-period vector in
  `RS.periodSubgroup X`, produces `δ'` with EXACT zero integral against every `ω ∈ RS.Form1 X`,
  not just the basis — extended via `RS.pathIntegralₗ` + `Module.Basis.ext`). Zero sorries.

* **`WeakToMero.lean`** (§4.2 D2, §2.1 step 7, §2.2): `wirtingerDbar_exp_neg_mul_eq_zero` (the
  `∂̄F = 0` computation for `F := exp(-u) * f`, via `wirtingerDbar_mul` + a new holomorphic-outer
  chain rule for `Complex.exp` built from mathlib's `HasDerivAt.comp_hasFDerivAt`) and
  `genus_eq_zero_of_exists_simple_pole` (Forster's necessity shortcut, composing the ALREADY-BUILT
  `RS.homeoSphere_of_exists_simple_pole` + `RS.SphereTopology.genus_eq_zero_of_homeo_sphere` —
  `form-trace-tower` is not imported anywhere in this unit, confirming the design's DAG-audit
  finding). Zero sorries.

* **`Sufficiency.lean`** (§4.1 D1, the unit's centerpiece): `exists_mero_of_pathIntegral_mem` (the
  two-point sufficiency direction) and `genus_eq_zero_of_pathIntegral_mem` (the composed
  necessity-direction corollary `ofCurve_inj'` consumes). See the file's own docstring for the
  ONE documented admitted step (the Dolbeault-upgrade bridge, blocked on `serre-duality-tails`).
  **NOT built**: the `k`-point Finset generalization (`RS.Abel.exists_mero_of_periodVector_mem`,
  design §4.1) — did not fit this pass's time budget on top of everything else, AND would inherit
  the same external blocker anyway; the design's own account is that its bookkeeping is
  mechanical (`Finset`-indexed product/sum) once the two-point case is in hand, ~80 lines. Flagged
  as a genuine gap (this one IS a scheduling/scope gap of this pass, not an external blocker) —
  see "Notes for period-lattice-rank" below.

* **`OfCurveInj.lean`** (§4.4 D4): `Jacobian.ofCurve_inj'` (gated on
  `[DiscreteTopology (RS.periodSubgroup X)]`, Forster 21.4(i) exactly — proved via the frozen
  ordering-resolution bridge `AddSubgroup.isClosed_of_discrete` + `AddSubgroup.
  topologicalClosure_minimal`/`le_topologicalClosure`, spike-verified in the design §9) and
  `Jacobian.ofCurve_inj` (present here as a gated wrapper too — see the file's own docstring for
  why the design's literal UNGATED final shape cannot be stated until `period-lattice-rank`
  registers the instance globally). Both inherit `Sufficiency.lean`'s one admitted step
  transitively; no new one is introduced here.

## Notes for `period-lattice-rank` (#31), the primary consumer

1. **The `k`-point sufficiency direction is NOT exported** (`RS.Abel.exists_mero_of_
   periodVector_mem`, design §4.1/§6 — this design's own finding, §1.4, is that Forster 21.4(b)'s
   own proof needs this general form, not just the two-point case). Only the two-point
   specialization (`exists_mero_of_pathIntegral_mem`) is built here, and even it carries the one
   documented admitted step. Building the `k`-point generalization is expected to be mechanical
   (`Finset`-indexed, no new mathematical idea) once (a) `serre-duality-tails` lands and (b) the
   two-point case's admitted step is discharged — do both first, then the `k`-point wrapper.
2. Once `period-lattice-rank` proves discreteness (Forster 21.4(b), which itself CITES this
   unit's sufficiency direction — see the design's §1.2 ordering-resolution account), please
   register **both** `instance : DiscreteTopology (RS.periodSubgroup X)` (feeds `ofCurve_inj'`
   directly) and `instance : DiscreteTopology (RS.periodSubgroup X).topologicalClosure` (feeds
   `jacobian-construction`'s existing gates) — both are cheap corollaries of the same
   discreteness proof via `AddSubgroup.isClosed_of_discrete` (§4.4/§9 of the design).
3. **Final assembly discharge shape**: once (1) `serre-duality-tails` lands, (2) `Sufficiency.
   lean`'s one admitted step is filled in, and (3) the `DiscreteTopology (RS.periodSubgroup X)`
   instance
   above is registered globally, `Jacobian.ofCurve_inj` becomes literally callable with NO
   explicit instance argument (the gate discharges by instance search) — the exact statement at
   `docs/Jacobian_challenge.lean:99` is already what `ofCurve_inj'`'s conclusion states verbatim,
   so final assembly is a zero-content rewrap, not new proof work.
-/
