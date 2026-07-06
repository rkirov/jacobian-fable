import Jacobian.Forms

/-!
# `Form1.pullback` — the easy direction (jacobian-functoriality §3)

Unit: jacobian-functoriality. Pullback of a holomorphic `1`-form along *any* holomorphic
`f : X → Y` (chain rule via `mfderiv`, no branch-point subtlety).

Main declarations:
* `RS.Form1.pullback f hf : Form1 Y →ₗ[ℂ] Form1 X`.
* `RS.coeffAt_pullback` — the preferred-chart coefficient formula.
* `RS.coeffIn_pullback` — the any-maximal-atlas-chart coefficient formula.
* `RS.Form1.pullback_id`, `RS.Form1.pullback_comp` — functoriality at the `Form1` level.

## `Compat` (to be filed upstream, `docs/requests/holomorphic-forms.md`)

* `RS.analyticAt_of_mem_maximalAtlas` — reading a `ContMDiffAt f x` map through *arbitrary*
  maximal-atlas charts on source and target is analytic (mathlib's own
  `contMDiffWithinAt_iff_of_mem_maximalAtlas` specialized to `𝓘(ℂ)`/`ω`, generalizing
  `RS.contMDiffAt_iff_analyticAt_of_mem_source` from a `ℂ`-valued target to an arbitrary charted
  target).
* `RS.mfderiv_chartAt_self` — the (forward) chart map's own `mfderiv` at its base point is the
  identity (the symmetric counterpart of `RS.mfderiv_chartAt_symm_chartAt_self`).
* `RS.tangentCoord_mfderiv_chart_comp` — two-manifold generalization of
  `RS.tangentCoord_mfderiv_comp`, reading the target through its own preferred chart.
-/

open scoped ContDiff Manifold Bundle
open Set IsManifold

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-! ### `Compat`: two-manifold chart bridges (requested upstream, proved locally) -/

/-- Reading a `ContMDiffAt` map through arbitrary maximal-atlas charts on both source and target
is analytic. Generalizes `RS.contMDiffAt_iff_analyticAt_of_mem_source` (`f : X → ℂ`) to an
arbitrary charted target `Y`. -/
theorem analyticAt_of_mem_maximalAtlas {f : X → Y} {x : X} (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) (hx : x ∈ e.source)
    {e' : OpenPartialHomeomorph Y ℂ} (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω Y) (hy : f x ∈ e'.source) :
    AnalyticAt ℂ (⇑e' ∘ f ∘ ⇑e.symm) (e x) := by
  have h := (contMDiffWithinAt_iff_of_mem_maximalAtlas he he' hx hy).mp
    (hf.contMDiffWithinAt : ContMDiffWithinAt 𝓘(ℂ) 𝓘(ℂ) ω f Set.univ x)
  simp only [preimage_univ, univ_inter, modelWithCornersSelf_coe, Set.range_id,
    contDiffWithinAt_univ] at h
  exact h.2.analyticAt

set_option backward.isDefEq.respectTransparency false in
/-- The (forward) preferred chart's own `mfderiv` at its base point is the identity — the
symmetric counterpart of `RS.mfderiv_chartAt_symm_chartAt_self`. -/
theorem mfderiv_chartAt_self (y : Y) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ y) y = ContinuousLinearMap.id ℂ ℂ := by
  have h := mfderiv_extChartAt_self (I := 𝓘(ℂ)) (x := y)
  simpa only [extChartAt_coe] using h

omit [IsManifold 𝓘(ℂ) ω X] in
set_option backward.isDefEq.respectTransparency false in
/-- Two-manifold generalization of `RS.tangentCoord_mfderiv_comp`: the composite `mfderiv`,
read in the *target's own preferred chart*, is the planar derivative of the chart-composite. -/
theorem tangentCoord_mfderiv_chart_comp {F : X → Y} {g : ℂ → X} {z : ℂ}
    (hF : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F (g z)) (hg : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g z) :
    tangentCoord (mfderiv 𝓘(ℂ) 𝓘(ℂ) F (g z) (mfderiv 𝓘(ℂ) 𝓘(ℂ) g z (1 : ℂ))) =
      deriv (⇑(chartAt ℂ (F (g z))) ∘ F ∘ g) z := by
  have hchartCM : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ (F (g z))) (F (g z)) :=
    contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas (F (g z)))
      (mem_chart_source ℂ (F (g z)))
  have hchart : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ (F (g z))) (F (g z)) :=
    hchartCM.mdifferentiableAt (by simp)
  have hcompFg : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ (F (g z)) ∘ F) (g z) := hchart.comp _ hF
  have h1 : tangentCoord (mfderiv 𝓘(ℂ) 𝓘(ℂ) F (g z) (mfderiv 𝓘(ℂ) 𝓘(ℂ) g z (1 : ℂ))) =
      tangentCoord (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ (F (g z))) (F (g z))
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) F (g z) (mfderiv 𝓘(ℂ) 𝓘(ℂ) g z (1 : ℂ)))) := by
    rw [mfderiv_chartAt_self]; rfl
  have h2 : mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ (F (g z))) (F (g z))
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) F (g z) (mfderiv 𝓘(ℂ) 𝓘(ℂ) g z (1 : ℂ))) =
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ (F (g z)) ∘ F) (g z) (mfderiv 𝓘(ℂ) 𝓘(ℂ) g z (1 : ℂ)) := by
    rw [mfderiv_comp (g z) hchart hF]; rfl
  rw [h1, h2]
  exact tangentCoord_mfderiv_comp hcompFg hg

end RS

end
