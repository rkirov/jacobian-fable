import Jacobian.Abel.Loops
import Jacobian.Abel.WeakToMero
import Jacobian.Abel.DolbeaultBridge
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

**Status**: the external blocker (`serre-duality-tails` not existing at all) has CLEARED —
`DolbeaultBridge.lean`'s `exists_dbar_eq_zero_of_forall_basis_pairing_eq_zero` proves the abstract
Dolbeault-upgrade bridge in full, zero sorries, gated only on `serre-duality-tails`'s own one
remaining external fact (`Function.Surjective (RS.LaurentTail.tailToH1 (0 : RS.Divisor X))`, a
genuine out-of-scope Cousin-I/Mittag-Leffler existence theorem). What remains is a *different*,
non-external, precisely-isolated gap: packaging a weak solution's chart-local `d''f/f` data into a
global `Form01 X` object with a proven vanishing pairing (design §4.1 step 5) — substantial new
analytic content that this pass's investigation found tractable in outline but did not complete on
top of everything else (see `Sufficiency.lean`'s own docstring for the full account and exact
discharge roadmap). It is isolated as the explicit hypothesis `RS.Abel.WeakSolutionUpgrade`
(two-point) / `RS.Abel.WeakSolutionUpgradeFinset` (`k`-point) — both theorems below are gated
theorems (no admitted-step placeholder), matching this project's established idiom (e.g. `Jacobian.ofCurve_inj'`'s
own `[DiscreteTopology (RS.periodSubgroup X)]` gate). `scripts/check.sh Jacobian/Abel` reports
**zero sorries**; the general multi-chart weak-solution gap this builder was separately authorized
to close inside `Jacobian/AbelWeak/` is complete with zero admitted steps.

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

* **`DolbeaultBridge.lean`** (§4.3 D3, restated at the tail level): `formDualEquiv` (the perfect
  pairing `Form1 X ≃ₗ[ℂ] Dual (H1Tail 0)`, unconditional) and
  `exists_dbar_eq_zero_of_forall_basis_pairing_eq_zero` (the abstract bridge itself — a vanishing
  residue pairing forces `d''`-exactness — PROVEN, gated only on
  `Function.Surjective (RS.LaurentTail.tailToH1 (0 : RS.Divisor X))`, `serre-duality-tails`'s own
  remaining external fact). Zero sorries.

* **`Sufficiency.lean`** (§4.1 D1, the unit's centerpiece): `exists_mero_of_pathIntegral_mem` (the
  two-point sufficiency direction) and `genus_eq_zero_of_pathIntegral_mem` (the composed
  necessity-direction corollary `ofCurve_inj'` consumes), both gated on the explicit hypothesis
  `RS.Abel.WeakSolutionUpgrade X` (design steps 5+7, the packaging-into-`Form01`-plus-CR-promotion
  content — see that def's docstring for the precise, investigated-but-not-completed discharge
  roadmap). **Also built**: the `k`-point `Finset` generalization
  (`RS.Abel.exists_mero_of_periodVector_mem`, design §4.1), gated on the analogous
  `RS.Abel.WeakSolutionUpgradeFinset X ι` — steps 1-4 (the `k`-point loop-cancellation against the
  TOTAL period, a weak solution per pair via `exists_weakSolutionOfPair`, and Forster's Lemma 20.1
  multiplicativity assembling the product via the ALREADY-BUILT `isWeakSolutionOfFinset_prod`) are
  fully proved, no gate beyond `WeakSolutionUpgradeFinset` itself. Zero sorries throughout.

* **`OfCurveInj.lean`** (§4.4 D4): `Jacobian.ofCurve_inj'` (gated on
  `[DiscreteTopology (RS.periodSubgroup X)]`, Forster 21.4(i) exactly — proved via the frozen
  ordering-resolution bridge `AddSubgroup.isClosed_of_discrete` + `AddSubgroup.
  topologicalClosure_minimal`/`le_topologicalClosure`, spike-verified in the design §9 — AND on
  the explicit hypothesis `RS.Abel.WeakSolutionUpgrade X`) and `Jacobian.ofCurve_inj` (same two
  gates — see the file's own docstring for why the design's literal UNGATED final shape cannot be
  stated until `period-lattice-rank` registers the instance globally AND
  `WeakSolutionUpgrade X` is proved). Zero sorries.

## Notes for `period-lattice-rank` (#31), the primary consumer

1. **The `k`-point sufficiency direction IS now exported** (`RS.Abel.exists_mero_of_
   periodVector_mem`, design §4.1/§6 — this design's own finding, §1.4, is that Forster 21.4(b)'s
   own proof needs this general form, not just the two-point case), gated on
   `RS.Abel.WeakSolutionUpgradeFinset X ι` (the `Finset` analogue of `WeakSolutionUpgrade`, same
   remaining content, see `Sufficiency.lean`'s docstring).
2. Once `period-lattice-rank` proves discreteness (Forster 21.4(b), which itself CITES this
   unit's sufficiency direction — see the design's §1.2 ordering-resolution account), please
   register **both** `instance : DiscreteTopology (RS.periodSubgroup X)` (feeds `ofCurve_inj'`
   directly) and `instance : DiscreteTopology (RS.periodSubgroup X).topologicalClosure` (feeds
   `jacobian-construction`'s existing gates) — both are cheap corollaries of the same
   discreteness proof via `AddSubgroup.isClosed_of_discrete` (§4.4/§9 of the design).
3. **Final assembly discharge shape**: once (1) `RS.Abel.WeakSolutionUpgrade`/
   `WeakSolutionUpgradeFinset` are proved (design steps 5+7 — `serre-duality-tails`'s own external
   blocker has already cleared, see `DolbeaultBridge.lean`) and (2) the
   `DiscreteTopology (RS.periodSubgroup X)` instance above is registered globally,
   `Jacobian.ofCurve_inj` becomes literally callable with NO explicit hypothesis/instance argument
   — the exact statement at `docs/Jacobian_challenge.lean:99` is already what `ofCurve_inj'`'s
   conclusion states verbatim, so final assembly is a zero-content rewrap, not new proof work.
4. **Exact `k`-point export signature** (for direct citation):
   ```
   theorem RS.Abel.exists_mero_of_periodVector_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
       (hupgradeFinset : RS.Abel.WeakSolutionUpgradeFinset X ι)
       (a x : ι → X) (ha : Function.Injective a) (hx : Function.Injective x)
       (hax : ∀ i j, a i ≠ x j) (γ : (i : ι) → Path (a i) (x i))
       (hmem : (fun k => ∑ i, RS.pathIntegral (γ i) (RS.basis X k)) ∈ RS.periodSubgroup X) :
       ∃ F : RS.Mero X, F ≠ 0 ∧ (∀ i, F.ord (x i) = 1) ∧ (∀ i, F.ord (a i) = -1) ∧
         ∀ z, (∀ i, z ≠ a i) → (∀ i, z ≠ x i) → F.ord z = 0
   ```
-/
