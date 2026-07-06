import Jacobian.MeromorphicTrace.ToP1
import Jacobian.MeromorphicTrace.OrderMultiplicity
import Jacobian.MeromorphicTrace.ArgumentPrinciple
import Jacobian.MeromorphicTrace.PlanarTrace
import Jacobian.MeromorphicTrace.FunctionTrace

/-!
# meromorphic-trace: the argument principle and the fibre trace of functions (namespace `RS.MTrace`)

API summary (see `docs/design/meromorphic-trace.md`). Standing surface hypotheses throughout
(`CONVENTIONS.md`); `f g : X → ℂ`, `h : ℂ → ℂ` for the planar atom.

* **`toP1`** (`ToP1.lean`): `toP1 f : X → OnePoint ℂ` lifts a raw meromorphic `f` to a holomorphic
  map into `ℙ¹` (`∞` at poles, the punctured limit elsewhere); `toP1_contMDiff` is the honest
  holomorphy proof, routed through `meromorphic-and-divisors`'s `MeroGermOn.holoRepr` (built after
  this unit's design was frozen, so the proof is shorter than originally planned — see the file's
  deviation note). `NotEventuallyConstX`/`toP1_not_const` (D3) translate raw-`f`-side
  nonconstancy into `toP1 f`'s. Reusable `holoRepr`/`toP1` facts are exported for
  `OrderMultiplicity.lean`'s and `ArgumentPrinciple.lean`'s own use.
* **`OrderMultiplicity.lean`**: `multiplicity_toP1_of_ordAtX_pos`/`_neg` — the order↔multiplicity
  bridges at zeros/poles of `f` (CC4's multiplicity of `toP1 f`, read in `coeChart`/`invChart`,
  equals `f`'s vanishing order/pole order). The design's third claimed lemma
  (`ordAtX f x = 0 → multiplicity (toP1 f) x = 1`) is **mathematically false**
  (`f = 1 + z²` at `0`: order `0`, multiplicity `2`) and is not proved — see the file's deviation
  note; it is flagged in the design itself as non-essential.
* **`ArgumentPrinciple.lean`**: **THE argument principle**, `finsum_ordAtX_eq_zero` — for `f`
  meromorphic everywhere and nonconstant on compact connected `X`,
  `∑ᶠ x, (ordAtX f x).untop₀ = 0` (zeros cancel poles), via `fiberMultSum_eq_degree` at `0`/`∞` on
  `ℙ¹` (mapping-degree's counting engine — **not** the residue theorem/Stokes, per the design's
  routing warning). `sum_ordAtX_eq_zero_of_finite` is the `Finset` form; `finsum_ordAtX_eq_zero'`
  takes the raw `NotEventuallyConstX` hypothesis. This is the engine `proper-map-degree` needs for
  `deg(divisor f) = 0` — see the downstream note below for the exact repackaging.
* **`PlanarTrace.lean`** (pure planar, independent of the above): `traceZk h k w`, the trace of
  `h` along `z ↦ z ^ k` at `w`. `analyticAt_traceZk` (analyticity away from `0`, via local root
  branches, no monodromy), `meromorphicAt_traceZk` (meromorphy at `0`, via a norm/`zpow` growth
  bound + Riemann's removable-singularity theorem — **zero sorries**, the unit's hardest theorem).
  **One documented blocker**: `laurentCoeffAt_traceZk` (the Laurent-coefficient formula
  `laurentCoeffAt (traceZk h k) 0 m = k · laurentCoeffAt h 0 (k·m)`) is left as the file's one
  admitted goal — see its inline comment for the two candidate proof routes identified
  (a `tsum`/power-series substitution as designed, or a `tsum`-free finite-remainder route found
  during this build) and why neither was completed in the time budget. Existence of `traceZk`'s
  meromorphy (needed everywhere else in this unit and by `form-trace-tower`) does **not** depend
  on this lemma.
* **`FunctionTrace.lean`**: `trace F h y₀` (`Tr_F h`, D7), the surface-level fibre trace, defined
  totally via an `if`-dispatch on `Nonempty (FiberStack F y₀)`. `trace_of_forall_eq` (the
  constant-`F` junk guard) is proved in full, including the case the design worried might need to
  stay an "open sub-case" (resolved via a short infiniteness-of-`X` argument). **Scope decision**:
  `meromorphicAtX_trace` (the design's centerpiece for this file) and `trace_of_regular` are
  **not proved** — both need `trace`'s well-definedness against the `FiberStack` choice (the
  design's own flagged risk R1), which this build traced one level further (see the file's
  module docstring for the exact resolution route found: routing through the naive fibre sum
  `∑ᶠ x ∈ F⁻¹{y}, h x`, which needs a `mapping-degree`-style bijection argument not completed) but
  did not finish. This is the documented, sanctioned fallback from the design's own §7 Risks 2/7.

## Downstream notes

* **proper-map-degree** needs `deg(divisor f) = 0`: take `finsum_ordAtX_eq_zero`/
  `sum_ordAtX_eq_zero_of_finite` and repackage `(ordAtX f x).untop₀` as `divisor f` values (their
  own `Divisor`/`degree` bookkeeping) — the finsum/Finset-sum identity here is *exactly*
  `Divisor.degree`'s shape (`Function.locallyFinsuppWithin.degree`), so the repackaging is a
  rewrite, not a re-derivation.
* **form-trace-tower** needs the planar trace atom + its Laurent behavior, and `Tr_F h` as a
  black box: `traceZk`, `analyticAt_traceZk`, `meromorphicAt_traceZk` are ready;
  `laurentCoeffAt_traceZk` is the one blocked lemma (see `PlanarTrace.lean`'s docstring for the
  two routes to finish it); `RS.MTrace.trace`/`trace_of_forall_eq` are ready, but
  `meromorphicAtX_trace` (needed for `Tr_F(h·ω)`'s own meromorphy) is not yet available — see
  `FunctionTrace.lean`'s module docstring for the precise remaining gap and resolution route.
* **laurent-tails (CC8)**: no direct edge (per the design, nothing here is laurent-tails-facing
  beyond what `residue-calculus`/`form-trace-tower` already mediate).
-/
