import Jacobian.JacFunctorial.Pullback
import Jacobian.JacFunctorial.PullbackIntegral
import Jacobian.JacFunctorial.Density
import Jacobian.JacFunctorial.PeriodMaps
import Jacobian.JacFunctorial.Challenge

/-!
# `jacobian-functoriality` (unit root)

Task #33 (blueprint-gap unit, flagged by `jacobian-construction`'s `Functorial.lean` §9.4/R4).
Target: `Jacobian.pushforward`, `Jacobian.pullback`, and the functoriality laws /
`pushforward_pullback` demanded by `docs/Jacobian_challenge.lean:104-153`, built from pullback
and trace of holomorphic `1`-forms.

## LEDGER — what is built (zero sorries) vs. what is not

### Built, zero sorries, `scripts/check.sh Jacobian/JacFunctorial` covers these:

* **`Jacobian/JacFunctorial/Pullback.lean`** (the centerpiece "easy direction"):
  `RS.Form1.pullback f hf : Form1 Y →ₗ[ℂ] Form1 X` (chain-rule pullback of a holomorphic `1`-form
  along *any* `f : X → Y`, `ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω`), `RS.coeffAt_pullback`/`RS.coeffIn_pullback`
  (chart-coefficient formulas), `RS.Form1.pullback_id`, `RS.Form1.pullback_comp` (`Form1`-level
  functoriality). Also a small `Compat` section (`RS.analyticAt_of_mem_maximalAtlas`,
  `RS.mfderiv_chartAt_self`, `RS.tangentCoord_mfderiv_chart_comp`) generalizing two-manifold
  chart-reading bridges from `holomorphic-forms`/`surfaces-and-charts` — recommended for upstream
  adoption, not yet requested there.
* **`Jacobian/JacFunctorial/PullbackIntegral.lean`**: `RS.IsPrimitiveAlongMap.pullback_comp`
  (a primitive of `η` along `f ∘ K` pulls back to a primitive of `Form1.pullback f hf η` along
  `K`) and its corollary `RS.pathIntegral_pullback` — naturality of `pathIntegral` under pullback,
  `pathIntegral γ (Form1.pullback f hf η) = pathIntegral (γ.map hf.continuous) η`.
* **`Jacobian/JacFunctorial/Density.lean`**: `RS.Form1.eq_of_eqOn_dense` ("Lemma A" — two `Form1`s
  agreeing on a dense set of `coeffAt`s are equal), proved via a chart-cancellation argument that
  **avoids** the design's proposed `Form1.continuous_coeffAt` (a genuine tangent-bundle
  continuity-in-the-basepoint fact this builder could not close; see §0 below).
* **`Jacobian/JacFunctorial/PeriodMaps.lean`**: `RS.periodCoordEquiv`, `RS.pushforwardT`
  (the period-space linear map induced by `Form1.pullback`'s `dualMap`),
  `RS.periodSubgroup_le_comap_pushforwardT` (`hT` for the pushforward direction — **exact**
  membership, no closure/density needed, via `pathIntegral_pullback` + the basepoint-flexible
  `periodVector_mem_periodSubgroup`), and the assembly **`Jacobian.pushforward`** via
  `Jacobian.inducedHom`. **UNIVERSE WARNING** (hard-won, cost hours of build time to diagnose):
  `Jacobian.inducedHom` is declared for `X Y : Type u` in the SAME universe
  (`JacobianConstruction/Functorial.lean`). Instantiating it at `X : Type*`/`Y : Type*` (distinct
  universe metavariables) does not fail cleanly — the elaborator grinds through `ULift`/quotient
  defeq indefinitely (>40 minutes of CPU observed, never finishing) instead of reporting the
  universe mismatch. `Jacobian.pushforward`/`pushforward_contMDiff` therefore fix one shared
  `Type u` for both surfaces (elaborates in milliseconds stated that way). The same constraint
  binds the final assembly; a cross-universe `Jacobian.inducedHom` (lifting the two `ULift`
  shells to different universes) is possible upstream if ever needed.
* **`Jacobian/JacFunctorial/Challenge.lean`**: `Jacobian.pushforward_contMDiff` (holomorphy of the
  pushforward map, free from `jacobian-construction`'s `Jacobian.contMDiff_inducedHom`).

### NOT built (documented gap, not silently dropped)

* **`Form1.trace`** (§6 of the design — the fibrewise trace of a `1`-form via `traceZkForm`
  root-sums) is **not constructed**. The regular-value case is genuinely elementary (an honest
  finite sum of transported local coefficients, no `traceZk` machinery), but the branch-value
  case (the design's own flagged "hardest content") needs more than the closed-form
  `RS.FormTrace.laurentCoeffAt_traceZkForm` identity suggested: `traceZkForm h k`'s *literal*
  value at the branch coordinate `0` (via `RS.MTrace.traceZk_zero_apply`'s junk convention) does
  **not**, in general, equal the removable-singularity's actual limit for `k > 1` — see
  `RS.FormTrace.traceZkForm_hAdapted_eq_apply`'s own `w ≠ 0` guard and module docstring, which
  already flags exactly this failure mode. A correct construction needs the coefficient
  *repaired* at branch points (e.g. via `Function.update` to the value supplied by
  `MeromorphicAt.exists_principalPart_add_analyticAt`'s analytic continuation), not merely a
  closed-form identity check. This is a genuinely new piece of analysis beyond what any upstream
  unit already proved; not completed in the time budget.
* **`Jacobian/JacFunctorial/TraceIntegral.lean`** (the `FiberChain`/monodromy construction, §7 —
  the design's own highest-risk item) — **not attempted**, since it is downstream of `Form1.trace`
  and is itself, independently, the single largest new piece of engineering the design
  anticipated (~150–200 lines of new structure).
* Consequently **`Jacobian.pullback`, `pullback_contMDiff`, `pullback_id_apply`,
  `pullback_comp_apply`, `pushforward_pullback`** (the projection formula) are **not built**: all
  of them need `Form1.trace`, and the last two also need `Jacobian.pushforward`/`Jacobian.pullback`
  as a pair.
* **`pushforward_id_apply`/`pushforward_comp_apply`** are also not built: they need
  `Torus.inducedHom_id`/`Torus.inducedHom_comp` (composition functoriality of the abstract
  `V ⧸ L →ₜ+ V' ⧸ L'` substrate), confirmed **absent** from
  `Jacobian/JacobianConstruction/Torus.lean` by this unit's own research (the design doc's claim
  that a request was filed to `jacobian-construction` for these is **stale** —
  `docs/requests/jacobian-construction.md` does not exist on disk). A local `Compat` proof is
  sketched but not completed (see the final report).

### §0: why `Form1.continuous_coeffAt` was replaced, not merely worked around

The design's `Density.lean` sketch routes "Lemma A" through a standalone
`Form1.continuous_coeffAt : Continuous (fun x => coeffAt x η)`. Proving this **directly** needs
continuity of `mfderiv (chartAt ℂ x)` *as its base point `x` varies* — a genuine tangent-bundle
fact this builder investigated at length (`ContMDiffOn.continuousOn_tangentMapWithin`,
`ContMDiffAt.mfderiv_const`/`.mfderiv_apply`/`inTangentCoordinates`) without finding a clean
closing move. **This unit does not need that fact**: `Form1.eq_of_eqOn_dense` is proved instead by
comparing against one *fixed* reference chart and cancelling a provably-nonzero transition
factor, reducing everything to `Form1.continuousOn_coeffIn` (already built, purely planar, no
gap). Anyone needing `Form1.continuous_coeffAt` itself for some other purpose should know it
remains open.

## Gate inheritance

`Jacobian.pushforward_contMDiff` inherits `[DiscreteTopology (periodSubgroup _).topologicalClosure]`
transparently from `jacobian-construction`'s `Jacobian.contMDiff_inducedHom` — the same gate every
`ChartedSpace`/`IsManifold`/`LieAddGroup`/`CompactSpace (Jacobian _)` instance and
`ofCurve_contMDiff` already need. No new gate is introduced by this unit.
-/
