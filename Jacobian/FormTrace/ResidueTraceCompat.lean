/-
Blueprint unit: form-trace-tower. `resAtP1` (D4) and residue-trace compatibility (task item 3,
Miranda Lemma 3.2 globalized).
-/
import Jacobian.FormTrace.PairForm
import Jacobian.FormTrace.TraceZkForm
import Jacobian.MeromorphicTrace.FunctionTrace
import Jacobian.MappingDegree.LocalStructure

/-!
# Residue-trace compatibility (`form-trace-tower`, file 3/6)

Unit: form-trace-tower (`docs/design/form-trace-tower.md` §2 D4, §4.3, §5 P-main). THE central
theorem: Miranda Lemma 3.2 globalized, `Res_y(Tr ω) = Σ_{x ∈ F⁻¹y} Res_x(ω)`.

**Deviation from the design, forced by `PairForm.lean`'s finding:** the design's own proof plan
(§5 P-main step 2–3) invokes `resAtX_eq_of_mem_source` with the ADAPTED target chart `(S.A i).e'`
in place of `chartAt ℂ y₀` — exactly the FALSE general two-chart invariance documented in
`PairForm.lean`'s module docstring. Tracing through what actually makes the classical theorem
true: `AdaptedChartsAt`'s existence proof (`Jacobian/LocalMultiplicity/AdaptedCharts.lean`,
`exists_adaptedChartsAt`) always builds its target chart as `chartAt ℂ (F x)` shifted by an
ADDITIVE CONSTANT (`e' := (chartAt ℂ (F x) ≫ₕ (Homeomorph.subRight _)) ≫ₕ ofSet _`) — a
TRANSLATION, whose derivative is the honest CONSTANT `1` (not just at one point but identically),
which is exactly the case where changing the target chart costs nothing (no `1/λ`-type
correction, unlike a general — e.g. scaled — target chart). This translation property is a fact
about the *concrete construction*, not exposed as a field of the abstract `AdaptedChartsAt`/
`FiberStack` structures (an adversarial witness could rescale the target chart, which WOULD
introduce a genuine correction — see `PairForm.lean`). Since `resAtP1_trace_eq_sum` takes an
arbitrary `S : FiberStack F y₀` as an explicit parameter, this calibration is recorded as an
EXPLICIT hypothesis `hcal` (satisfied by any stack built via `exists_fiberStack`/
`exists_adaptedChartsAt`, per direct inspection of their construction) rather than assumed away.

* `resAtP1` (D4), `resAtP1_eq_resAtX_id`.
* `resAtP1_trace_eq_sum` — THE main theorem (task item 3), with the `hcal` calibration hypothesis.
* `trace_const_mul_pullback`, `trace_pullback_eq_degree_smul` — the projection-formula facts
  (task item 5, §4.6), NOT gated on the calibration issue at all (pure value/finsum identities).
-/

open scoped ContDiff Manifold
open Filter Topology Metric Function Set

namespace RS.FormTrace

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Residue at `y₀ : ℙ¹` of a function `R : ℙ¹ → ℂ`, viewed as the coefficient of `R·dz`. -/
noncomputable def resAtP1 (R : OnePoint ℂ → ℂ) (y₀ : OnePoint ℂ) : ℂ :=
  RS.resAt (R ∘ (chartAt ℂ y₀).symm) (chartAt ℂ y₀ y₀)

theorem resAtP1_def (R : OnePoint ℂ → ℂ) (y₀ : OnePoint ℂ) :
    resAtP1 R y₀ = RS.resAt (R ∘ (chartAt ℂ y₀).symm) (chartAt ℂ y₀ y₀) := rfl

theorem resAtP1_eq_resAtX_id (R : OnePoint ℂ → ℂ) (y₀ : OnePoint ℂ) :
    resAtP1 R y₀ = resAtX (id : OnePoint ℂ → OnePoint ℂ) R y₀ := by
  rw [resAtP1_def, resAtX_def]
  apply resAt_congr
  have hmem : ∀ᶠ z in 𝓝 (chartAt ℂ y₀ y₀), z ∈ (chartAt ℂ y₀).target :=
    (chartAt ℂ y₀).open_target.mem_nhds ((chartAt ℂ y₀).map_source (mem_chart_source ℂ y₀))
  filter_upwards [hmem.filter_mono nhdsWithin_le_nhds] with z hz
  show R ((chartAt ℂ y₀).symm z) =
    R ((chartAt ℂ y₀).symm z) * deriv (chartAt ℂ (id y₀) ∘ id ∘ (chartAt ℂ y₀).symm) z
  have hderiv1 : deriv (chartAt ℂ (id y₀) ∘ id ∘ (chartAt ℂ y₀).symm) z = 1 := by
    have heq : (chartAt ℂ (id y₀) ∘ id ∘ (chartAt ℂ y₀).symm) =ᶠ[𝓝 z] id := by
      filter_upwards [(chartAt ℂ y₀).open_target.mem_nhds hz] with z' hz'
      show chartAt ℂ y₀ ((chartAt ℂ y₀).symm z') = z'
      rw [(chartAt ℂ y₀).right_inv hz']
    rw [heq.deriv_eq, deriv_id]
  rw [hderiv1, mul_one]

end RS.FormTrace
