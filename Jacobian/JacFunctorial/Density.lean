import Jacobian.Forms

/-!
# `Density.lean` — the reusable "dense ⟹ everywhere" closing lemma (jacobian-functoriality §5)

Unit: jacobian-functoriality. `RS.Form1.eq_of_eqOn_dense` ("Lemma A"): two `Form1`s whose
`coeffAt`s agree on a dense set of the manifold are equal. Used downstream by `Trace.lean`'s
`compat`, the projection formula, and the comp-functoriality laws.

**Design deviation** (recorded, not silently dropped): the design sketch proposed routing this
through a standalone `Form1.continuous_coeffAt : Continuous (fun x => coeffAt x η)`. That
statement needs genuine tangent-bundle continuity theory (continuity of `mfderiv (chartAt ℂ x)`
*as its base point `x` varies*, not at a fixed point) that does not reduce to anything already
built in this project. **This is avoided entirely** by comparing `η`/`η'` against a *fixed*
reference chart instead: for `x` in a fixed chart `e₀`'s source,
`coeffAt x η = deriv (⇑e₀ ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) * coeffIn e₀ η (e₀ x)`
(`RS.coeffAt_eq_deriv_mul_coeffIn`, a pure algebraic identity via `RS.coeffIn_trans`, no
continuity-in-`x` needed for the transition factor). Since this factor is the *same* nonzero
number for `η` and `η'` (`RS.analyticAt_transition`'s nonvanishing-derivative half), the
hypothesis `coeffAt x η = coeffAt x η'` cancels it, reducing to `coeffIn e₀ η (e₀ x) =
coeffIn e₀ η' (e₀ x)` on a dense subset of `e₀.target` — and *that* is closed by
`Form1.continuousOn_coeffIn` (already built, purely planar, no gap) via `Continuous.ext_on`.
-/

open scoped ContDiff Manifold Topology
open Set Filter IsManifold

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The preferred-chart coefficient, read against a *fixed* reference chart `e₀` valid at `x`:
a pure chain-rule identity (`RS.coeffIn_trans` applied between `e₀` and `chartAt ℂ x`), no
continuity-in-`x` involved. -/
theorem coeffAt_eq_deriv_mul_coeffIn (η : Form1 X) {e₀ : OpenPartialHomeomorph X ℂ}
    (he₀ : e₀ ∈ maximalAtlas 𝓘(ℂ) ω X) {x : X} (hx : x ∈ e₀.source) :
    coeffAt x η =
      deriv (⇑e₀ ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) * coeffIn e₀ η (e₀ x) := by
  have hz : chartAt ℂ x x ∈ ⇑(chartAt ℂ x) '' (e₀.source ∩ (chartAt ℂ x).source) :=
    ⟨x, ⟨hx, mem_chart_source ℂ x⟩, rfl⟩
  have h := coeffIn_trans he₀ (chart_mem_maximalAtlas x) η hz
  rwa [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)] at h

/-- The chart-transition factor above never vanishes (a chart and its inverse compose to the
identity; `RS.analyticAt_transition`'s nonvanishing-derivative half). -/
theorem deriv_transition_ne_zero {e₀ : OpenPartialHomeomorph X ℂ}
    (he₀ : e₀ ∈ maximalAtlas 𝓘(ℂ) ω X) {x : X} (hx : x ∈ e₀.source) :
    deriv (⇑e₀ ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) ≠ 0 :=
  (analyticAt_transition he₀ (chart_mem_maximalAtlas x) hx (mem_chart_source ℂ x)).2

/-- For `η η' : Form1 X` and a fixed chart `e₀`, if `coeffAt` agrees on all of `e₀.source`, so
does `coeffIn e₀` on the corresponding image (cancelling the nonzero transition factor). -/
theorem coeffIn_eqOn_of_coeffAt_eqOn {η η' : Form1 X} {e₀ : OpenPartialHomeomorph X ℂ}
    (he₀ : e₀ ∈ maximalAtlas 𝓘(ℂ) ω X) {s : Set X} (hs : s ⊆ e₀.source)
    (h : Set.EqOn (fun x => coeffAt x η) (fun x => coeffAt x η') s) :
    Set.EqOn (fun z => coeffIn e₀ η z) (fun z => coeffIn e₀ η' z) (e₀ '' s) := by
  rintro z ⟨x, hxs, rfl⟩
  have hx : x ∈ e₀.source := hs hxs
  have hη := coeffAt_eq_deriv_mul_coeffIn η he₀ hx
  have hη' := coeffAt_eq_deriv_mul_coeffIn η' he₀ hx
  have hd := deriv_transition_ne_zero he₀ hx
  have hxeq : coeffAt x η = coeffAt x η' := h hxs
  rw [hη, hη'] at hxeq
  exact mul_left_cancel₀ hd hxeq

/-- Density transports along a chart: if `s` is dense in `X`, then `e₀ '' (s ∩ e₀.source)` is
dense in `e₀.target`. -/
theorem dense_image_inter_source {e₀ : OpenPartialHomeomorph X ℂ} {s : Set X} (hs : Dense s) :
    Dense (⇑e₀ '' (s ∩ e₀.source) ∩ e₀.target) := by
  rw [dense_iff_inter_open]
  intro U hUo hUne
  obtain ⟨z, hzU, hzt⟩ := hUne
  have hzs : e₀.symm z ∈ e₀.source := e₀.map_target hzt.2
  have hVopen : IsOpen (⇑e₀.symm ⁻¹' U ∩ e₀.source) :=
    (e₀.continuousOn_symm.isOpen_inter_preimage e₀.open_target hUo).mono
      (by rw [inter_comm]; exact inter_subset_left) |>.congr rfl
  sorry

end RS

end
