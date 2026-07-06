import Jacobian.JacobianConstruction.Basic

/-!
# `ofCurve`, well-definedness, `ofCurve_self` (CC9, §8)

Unit: jacobian-construction. The Abel–Jacobi map `Jacobian.ofCurve`, its any-path recipe
(well-definedness, `ofCurve_eq_of_path`), and `ofCurve_self`. Path-connectedness of `X` is derived
locally (§8.1; filed as a request to surfaces-and-charts, non-blocking).

`ofCurve_contMDiff` (§8.3 — holomorphy of the Abel–Jacobi map) is **not** in this file: see the
module docstring of `Jacobian/JacobianConstruction.lean` for its status.
-/

open scoped ContDiff Manifold
open IsManifold

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### §8.1: path-connectedness of `X` (small gap, filled here; `Compat`) -/

/-- `Compat`: `X` is locally path-connected, via its charts into `ℂ` (a locally convex space).
Filed as a request to surfaces-and-charts (`docs/requests/surfaces-and-charts.md`); carried here
as a local instance since no upstream unit currently provides it. -/
instance : LocPathConnectedSpace X := ChartedSpace.locPathConnectedSpace (H := ℂ)

/-- `Compat`: `X` is path-connected (`ConnectedSpace X` + `LocPathConnectedSpace X`). -/
instance : PathConnectedSpace X := .of_locPathConnectedSpace

/-! ### `periodVector` of a loop, at *any* basepoint, lies in `periodSubgroup X` -/

/-- Basepoint-independence of the period subgroup: for any based loop `γ` at any point `x` (not
just at `periodSubgroup`'s defining basepoint), `periodVector (basis X) γ` still lies in
`periodSubgroup X`, via conjugation by a connecting path (`RS.period_conj`). -/
theorem RS.periodVector_mem_periodSubgroup {x : X} (γ : Path x x) :
    RS.periodVector (RS.basis X) γ ∈ RS.periodSubgroup X := by
  set x₀ := Classical.arbitrary X
  set σ : Path x₀ x := PathConnectedSpace.somePath x₀ x
  have heq : RS.periodVector (RS.basis X) γ
      = RS.periodVector (RS.basis X) ((σ.trans γ).trans σ.symm) := by
    funext i
    exact (RS.period_conj σ γ (RS.basis X i)).symm
  rw [heq]
  exact AddSubgroup.subset_closure ⟨(σ.trans γ).trans σ.symm, rfl⟩

namespace Jacobian

/-! ### `ofCurve` (§8.2) -/

/-- The Abel–Jacobi map from a compact Riemann surface to its Jacobian
(`docs/Jacobian_challenge.lean:92`): integrate the basis of holomorphic `1`-forms along *some*
path from `P` to `x` (any choice; well-defined mod periods, `ofCurve_eq_of_path`). -/
noncomputable def ofCurve (P : X) : X → Jacobian X := fun x =>
  ULift.up (QuotientAddGroup.mk
    (fun i => RS.pathIntegral (PathConnectedSpace.somePath P x) (RS.basis X i)))

/-- `ofCurve` computed along *any* path `σ : Path P x`, not just the canonical
`PathConnectedSpace.somePath` — the any-path recipe, and the source of well-definedness. -/
theorem ofCurve_eq_of_path (P x : X) (σ : Path P x) :
    ofCurve P x = ULift.up (QuotientAddGroup.mk (fun i => RS.pathIntegral σ (RS.basis X i))) := by
  show ULift.up (QuotientAddGroup.mk
      (fun i => RS.pathIntegral (PathConnectedSpace.somePath P x) (RS.basis X i)))
    = ULift.up (QuotientAddGroup.mk (fun i => RS.pathIntegral σ (RS.basis X i)))
  congr 1
  set σ₀ := PathConnectedSpace.somePath P x with hσ₀_def
  rw [QuotientAddGroup.eq_iff_sub_mem]
  have hmem : RS.periodVector (RS.basis X) (σ.trans σ₀.symm) ∈ RS.periodSubgroup X :=
    RS.periodVector_mem_periodSubgroup (σ.trans σ₀.symm)
  have heq : (fun i => RS.pathIntegral σ₀ (RS.basis X i)) - (fun i => RS.pathIntegral σ (RS.basis X i))
      = -RS.periodVector (RS.basis X) (σ.trans σ₀.symm) := by
    funext i
    show _ = -(RS.pathIntegral (σ.trans σ₀.symm) (RS.basis X i))
    rw [RS.pathIntegral_trans, RS.pathIntegral_symm]
    ring
  rw [heq]
  exact (RS.periodSubgroup X).topologicalClosure.neg_mem
    (AddSubgroup.le_topologicalClosure _ hmem)

@[simp] theorem ofCurve_self (P : X) : ofCurve P P = 0 := by
  rw [ofCurve_eq_of_path P P (Path.refl P)]
  simp [RS.pathIntegral_refl]

end Jacobian

end
