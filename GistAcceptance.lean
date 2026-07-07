import Jacobian
import Jacobian.Challenge

/-!
# Acceptance test for `Jacobian/Challenge.lean`

`docs/Jacobian_challenge.lean` (v0.4) with its `import Mathlib` replaced by
`import Jacobian` + `import Jacobian.Challenge`, and every placeholder declaration replaced by
an `example` stating the gist item verbatim and proved by the (now-existing) providing name.
The gist's own declarations cannot be redeclared literally — they already exist in the imported
environment (that is the point) — so each is witnessed as an `example` in the gist's own shape.

Universe note: the gist's `variable {X Y Z : Type*}` blocks give the functorial items
independent universes; the built `Jacobian`-level functorial API requires one shared universe
(see `Jacobian/Challenge.lean`'s module docstring), so items 15–22 and 24 are stated in a
single `universe u`. Everything else, including `ContMDiff.degree`, is cross-universe verbatim.
-/

open scoped ContDiff -- for ω notation

open scoped Manifold -- for 𝓘 notation

universe u

-- item 1: `genus` (gist line 46)
noncomputable example (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : ℕ := genus X

-- let X be a compact Riemann surface
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

-- item 2: `genus_eq_zero_iff_homeo` (gist line 54)
example : genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  genus_eq_zero_iff_homeo

-- item 3: `Jacobian` (gist line 61), `Type u → Type u`
noncomputable example (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type u := Jacobian X

-- item 4: `instance : AddCommGroup (Jacobian X)` (gist line 68)
noncomputable example : AddCommGroup (Jacobian X) := inferInstance

-- item 5: `instance : TopologicalSpace (Jacobian X)` (gist line 72)
noncomputable example : TopologicalSpace (Jacobian X) := inferInstance

-- item 6: `instance : T2Space (Jacobian X)` (gist line 75)
example : T2Space (Jacobian X) := inferInstance

-- item 7: `instance : CompactSpace (Jacobian X)` (gist line 78)
example : CompactSpace (Jacobian X) := inferInstance

-- item 8: `instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` (gist line 83)
noncomputable example : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X) := inferInstance

-- item 9: `instance : IsManifold 𝓘(ℂ, Fin (genus X) → ℂ) ω (Jacobian X)` (gist line 86)
example : IsManifold 𝓘(ℂ, Fin (genus X) → ℂ) ω (Jacobian X) := inferInstance

-- item 10: `instance : LieAddGroup 𝓘(ℂ, Fin (genus X) → ℂ) ω (Jacobian X)` (gist line 89)
example : LieAddGroup 𝓘(ℂ, Fin (genus X) → ℂ) ω (Jacobian X) := inferInstance

-- item 11: `Jacobian.ofCurve` (gist line 92)
noncomputable example (P : X) : X → Jacobian X := Jacobian.ofCurve P

-- item 12: `Jacobian.ofCurve_contMDiff` (gist line 94)
example (P : X) : ContMDiff 𝓘(ℂ) 𝓘(ℂ, Fin (genus X) → ℂ) ω (Jacobian.ofCurve P) :=
  Jacobian.ofCurve_contMDiff P

-- item 13: `Jacobian.ofCurve_self` (gist line 96)
example (P : X) : Jacobian.ofCurve P P = 0 := Jacobian.ofCurve_self P

-- item 14: `Jacobian.ofCurve_inj` (gist line 99) — provided by `Jacobian.ofCurve_inj`
example (P : X) (h : 0 < genus X) : Function.Injective (Jacobian.ofCurve P) :=
  Jacobian.ofCurve_inj P h

-- item 23: `ContMDiff.degree` (gist line 147) — cross-universe, `f` explicit
noncomputable example {X' : Type*} {Y' : Type*} [TopologicalSpace X'] [T2Space X']
    [CompactSpace X'] [ConnectedSpace X'] [ChartedSpace ℂ X'] [IsManifold 𝓘(ℂ) ω X']
    [TopologicalSpace Y'] [T2Space Y'] [CompactSpace Y'] [ConnectedSpace Y']
    [ChartedSpace ℂ Y'] [IsManifold 𝓘(ℂ) ω Y']
    (f : X' → Y') (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ := ContMDiff.degree f hf

section SharedUniverseFunctorial

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
variable (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)

-- item 15: `Jacobian.pushforward` (gist line 107)
noncomputable example : Jacobian X →ₜ+ Jacobian Y := Jacobian.pushforward f hf

-- item 16: `Jacobian.pushforward_contMDiff` (gist line 112)
example : ContMDiff 𝓘(ℂ, Fin (genus X) → ℂ) 𝓘(ℂ, Fin (genus Y) → ℂ) ω
    (Jacobian.pushforward f hf) :=
  Jacobian.pushforward_contMDiff f hf

-- item 17: `Jacobian.pushforward_id_apply` (gist line 116)
example (P : Jacobian X) : Jacobian.pushforward id contMDiff_id P = P :=
  Jacobian.pushforward_id_apply P

-- item 18: `Jacobian.pushforward_comp_apply` (gist line 124)
example (P : Jacobian X) :
    Jacobian.pushforward (g ∘ f) (hg.comp hf) P
      = Jacobian.pushforward g hg (Jacobian.pushforward f hf P) :=
  Jacobian.pushforward_comp_apply f hf g hg P

-- item 19: `Jacobian.pullback` (gist line 130)
noncomputable example : Jacobian Y →ₜ+ Jacobian X := Jacobian.pullback f hf

-- item 20: `Jacobian.pullback_contMDiff` (gist line 135)
example : ContMDiff 𝓘(ℂ, Fin (genus Y) → ℂ) 𝓘(ℂ, Fin (genus X) → ℂ) ω
    (Jacobian.pullback f hf) :=
  Jacobian.pullback_contMDiff f hf

-- item 21: `Jacobian.pullback_id_apply` (gist line 139)
example (P : Jacobian X) : Jacobian.pullback id contMDiff_id P = P :=
  Jacobian.pullback_id_apply P

-- item 22: `Jacobian.pullback_comp_apply` (gist line 142)
example (P : Jacobian Z) :
    Jacobian.pullback (g.comp f) (hg.comp hf) P
      = Jacobian.pullback f hf (Jacobian.pullback g hg P) :=
  Jacobian.pullback_comp_apply f hf g hg P

-- item 24: `Jacobian.pushforward_pullback` (gist line 151)
example (P : Jacobian Y) :
    Jacobian.pushforward f hf (Jacobian.pullback f hf P) = (ContMDiff.degree f hf) • P :=
  Jacobian.pushforward_pullback f hf P

end SharedUniverseFunctorial

/-! ### Axiom audit on the six main items -/

#print axioms genus
#print axioms Jacobian
#print axioms Jacobian.ofCurve_inj
#print axioms genus_eq_zero_iff_homeo
#print axioms Jacobian.pushforward_pullback
#print axioms ContMDiff.degree
