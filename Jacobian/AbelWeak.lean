import Jacobian.AbelWeak.PlanarLogBranch
import Jacobian.AbelWeak.WeakSolution
import Jacobian.AbelWeak.SingleChart
import Jacobian.AbelWeak.ChainAssembly

/-!
# abel-weak-solutions: weak solutions, the planar log-branch, and chain assembly (Forster §20.1–20.4)

Unit: abel-weak-solutions (`docs/design/abel-weak-solutions.md`). Builds the weak-solution
machinery Forster's Abel's-theorem proof (§20.5–20.7) needs, staying in planar pieces glued by
explicit chart formulas (no monodromy/homotopy machinery). Namespace `RS.AbelWeak` unless noted.
NOT registered in `Jacobian.lean` (orchestrator's job, per this unit's task hard rules).

## API summary

* **`WeakSolution.lean`** (Forster §20.1–20.2, D1):
  `IsWeakSolutionAt f a k` — the local model `f = ψ(e·)·(e· − e a)^k` near `a` in some
  `maximalAtlas` chart `e`, `ψ` smooth (`ℝ`-`C^∞`, i.e. `ContDiffAt ℝ ∞`) and non-vanishing near
  `e a`. `IsWeakSolutionOfPair f P Q` — the two-point structure this unit's deliverable produces
  (`ℝ`-smooth off `Q`, non-vanishing off `{P, Q}`, local model `+1` at `P`, `-1` at `Q`).
  **SCOPE ADDITION** (`docs/design/abel-theorem.md` §1.4/§4.1's finding that Thm 21.4(b) needs
  the `k`-point case): `IsWeakSolutionOfFinset f a x` (Finset-indexed generalization) and
  `isWeakSolutionOfFinset_prod` (Forster's Lemma 20.1 — weak solutions of pairwise-disjoint pairs
  multiply). Also: the `ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞` ↔ planar `ContDiffAt ℝ ∞` chart bridges
  (`contMDiffAt_finsetProd_real`, `contDiffAt_comp_symm_of_contMDiffAt`,
  `contMDiffAt_comp_of_contDiffAt`) and the multiplicativity step
  `IsWeakSolutionAt.mul_of_contMDiffAt`.

* **`PlanarLogBranch.lean`** (§6.1, no manifold imports, pure `ℂ → ℂ`):
  `exists_logBranch_disk` (disk case: a log branch of any non-vanishing holomorphic `h` on a
  ball, via mathlib's disk-Morera primitive + a zero-derivative uniqueness argument — no
  `Complex.log`/`Complex.arg` branch-cut case analysis) and `exists_exteriorLogBranch` (the
  engine Forster's construction needs: a log branch of `(z−b)/(z−a)` on `{ρ < ‖z‖}` for
  `a, b ∈ ball 0 ρ`, via the inversion `w = 1/z` transporting the exterior region to a genuine
  disk with no excluded point at all).

* **`SingleChart.lean`** (§6.2–6.3): `exists_weakSolutionOfPair_chart` — the single-chart weak
  solution: given `P, Q` inside a common chart `e`, both within `ball c ρ`, and a
  `ContDiffBump (0 : ℂ)` cutoff interpolating the rational function `(z−eP)/(z−eQ)` (near `c`) to
  the constant `1` (outside `closedBall c ψ.rOut`), produces `f` with `IsWeakSolutionOfPair f P Q`,
  equal to `1` outside the open set `e.symm '' ball c ψ.rOut` (compact closure).

* **`ChainAssembly.lean`** (§7): three deliverables —
  * `exists_weakSolutionOfFinset` — the **SCOPE ADDITION** `k`-point layer, assembled directly
    from `exists_weakSolutionOfPair_chart` (one call per pairwise-disjoint pair, each already
    living inside its own chart neighbourhood — exactly the shape `abel-theorem`'s own Thm
    21.4(a) disjoint-chart construction produces, per its design's own §1.4 account) plus
    `isWeakSolutionOfFinset_prod`.
  * `pathIntegral_eq_sum_chartChain` — the CC6-compliant telescoped path-integral identity
    (§7.1's `(1/2πi) ∬_X (df/f) ∧ ω` replacement, D5): for any `ChartChain` `C` and holomorphic
    `η`, `pathIntegral γ η` equals the finite sum of chart-local primitive differences. Pure
    `Path`-API bookkeeping, no Stokes.
  * `residue_identity_two_point` / `logDeriv_rat_eq` — the Lemma-20.3-specialized residue
    identity (Stokes-driven): for the two-puncture kernel `(w−b)⁻¹ − (w−a)⁻¹` (a weak solution's
    own log-derivative shape, `logDeriv_rat_eq`) and any `C¹` compactly-supported `g`, the area
    integral of `∂̄g` against that kernel recovers `g b − g a` — no local-constancy hypothesis on
    `g` needed (citing `planar-stokes-atoms`' own hypothesis-free two-puncture export
    `RS.integral_wirtingerDbar_mul_inv_sub_sub_inv_sub_eq` directly).

## Status: the general multi-chart `exists_weakSolutionOfPair` is NOT built

The design's §6.3/§7.1 deliverable — a weak solution of `(P, Q)` for an **arbitrary** path
`γ : Path Q P` not confined to one chart, assembled by taking the pointwise product of
`SingleChart` pieces over a full `RS.ChartChain` — is **not built in this pass**. The gap: two
adjacent `ChartChain` pieces meeting at an interior breakpoint `M` generally use *different*
charts, so showing the product of their weak solutions is smooth *at* `M` (where one piece's
`+1`-order zero must cancel the next piece's `-1`-order pole) needs a "rechart" lemma for
`IsWeakSolutionAt`: transporting a simple-zero/pole local model across a holomorphic chart
transition. This is provable — mathlib's removable-singularity theorem
(`Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`, applied to the
transition map's difference quotient, which tends to the transition's derivative at the
breakpoint by `hasDerivAt_iff_tendsto_slope`) supplies exactly the missing "linear factor
division" fact — but assembling it together with the chain induction (plus the per-piece radius
bookkeeping needed so only *adjacent* pieces' transition supports can overlap) did not fit this
pass's time budget. Flagged as risk R3 in the design's own §11, which underestimated it as
"mechanical, ~20 lines"; it is real, correct, buildable content but genuinely more than that.

**Consumer impact** (`abel-theorem`, #29): its `k`-point/Finset use (§1.4, `RS.Abel.exists_mero_of_periodVector_mem`)
does **not** need the general case — its own account of Thm 21.4(a)'s construction is exactly
the disjoint-single-chart-per-pair shape `exists_weakSolutionOfFinset` above already covers. Its
two-point sufficiency direction (§2.1, `RS.Abel.exists_mero_of_pathIntegral_mem`) is the one
consumer that *would* need the fully general version, since the path `δ'` it builds (via loop
cancellation) is not generally confined to one chart. `abel-theorem`'s builder should either (a)
build the rechart lemma + induction themselves on top of `SingleChart.exists_weakSolutionOfPair_chart`
and `WeakSolution.IsWeakSolutionAt.mul_of_contMDiffAt` (the multiplicativity step already built
here is exactly what the induction's *disjoint* pieces would need; only the *adjacent*-breakpoint
rechart step is missing), or (b) find an alternative route (e.g. the third-kind-differential
construction this unit's design §4 examined and deferred, gated on Riemann–Roch).

## DAG audit (confirmed at build time)

Only `paths-and-integrals` (`Jacobian.Path`) and `planar-stokes-atoms` (`Jacobian.PlanarStokes`)
are imported, matching the design's recommended tightened `Builds on:` line (§2.5). No file here
imports `Jacobian.Monodromy`, `Jacobian.FormTrace`, or `Jacobian.Meromorphic`.
-/
