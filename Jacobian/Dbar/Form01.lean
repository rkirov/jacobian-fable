import Jacobian.Surface
import Jacobian.Forms.Analyticity

/-!
# `Form01 X`: smooth `(0,1)`-forms as chart-coefficient families (`Jacobian/Dbar/Form01.lean`)

Unit: dbar-solvability (`docs/design/dbar-solvability.md` D5/D8, §4.6).

Per design D5, `Form01 X` is **not** a bundled `ContMDiffSection` (unlike `Form1`, CC1): there is
no anti-linear Hom-bundle in mathlib at the pin, and the blueprint's `restrictScalars ℂ→ℝ`
diamond warning rules out building one. Instead `Form01 X` is a plain structure: a
`chartAt`-indexed family of coefficient functions (the coefficient of `dz̄`), zero off chart
targets (junk-normalized so `ext` is honest), smooth on targets, with the anti-holomorphic
transition rule `coeff_y = conj (deriv τ) * (coeff_x ∘ τ)`. This mirrors the frozen CC1
`coeffIn` philosophy (`Jacobian/Forms/Coeffs.lean`) with `conj` inserted, reusing
`analyticAt_trans`/`deriv_trans_comp` from `Jacobian/Forms/Analyticity.lean`.

(Note: `η, η'` are used for `Form01` variables rather than the more suggestive `ω` — `ω` is a
reserved token in the ambient `ContDiff` scope's regularity level and cannot be reused as an
ordinary identifier.)
-/

open scoped ContDiff Manifold
open Set IsManifold

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- A smooth `(0,1)`-form on `X`: a `chartAt`-indexed coefficient family for `dz̄`, junk-zero off
chart targets, smooth on targets, related on overlaps by the anti-holomorphic transition rule. -/
structure Form01 (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] where
  /-- The coefficient function in the preferred chart at each point. -/
  coeffAt : X → ℂ → ℂ
  coeffAt_zero_off : ∀ x, ∀ z ∉ (chartAt ℂ x).target, coeffAt x z = 0
  contDiffOn_coeffAt : ∀ x, ContDiffOn ℝ ∞ (coeffAt x) (chartAt ℂ x).target
  compat : ∀ x y : X, ∀ z ∈ ⇑(chartAt ℂ y) '' ((chartAt ℂ x).source ∩ (chartAt ℂ y).source),
    coeffAt y z = (starRingEnd ℂ) (deriv (⇑(chartAt ℂ x) ∘ ⇑(chartAt ℂ y).symm) z) *
      coeffAt x (chartAt ℂ x ((chartAt ℂ y).symm z))

namespace Form01

/-- A `(0,1)`-form is determined by its preferred-chart coefficients on chart targets. -/
@[ext]
theorem ext {η η' : Form01 X}
    (h : ∀ x, ∀ z ∈ (chartAt ℂ x).target, η.coeffAt x z = η'.coeffAt x z) : η = η' := by
  have hcoeff : η.coeffAt = η'.coeffAt := by
    funext x z
    by_cases hz : z ∈ (chartAt ℂ x).target
    · exact h x z hz
    · rw [η.coeffAt_zero_off x z hz, η'.coeffAt_zero_off x z hz]
  obtain ⟨c1, _, _, _⟩ := η
  obtain ⟨c2, _, _, _⟩ := η'
  simp only at hcoeff
  subst hcoeff
  rfl

instance : Zero (Form01 X) where
  zero := ⟨fun _ _ => 0, fun _ _ _ => rfl, fun _ => contDiffOn_const, fun _ _ _ _ => by simp⟩

instance : Add (Form01 X) where
  add η η' := ⟨fun x z => η.coeffAt x z + η'.coeffAt x z,
    fun x z hz => by dsimp only; rw [η.coeffAt_zero_off x z hz, η'.coeffAt_zero_off x z hz, add_zero],
    fun x => (η.contDiffOn_coeffAt x).add (η'.contDiffOn_coeffAt x),
    fun x y z hz => by dsimp only; rw [η.compat x y z hz, η'.compat x y z hz]; ring⟩

instance : Neg (Form01 X) where
  neg η := ⟨fun x z => -η.coeffAt x z,
    fun x z hz => by dsimp only; rw [η.coeffAt_zero_off x z hz, neg_zero],
    fun x => (η.contDiffOn_coeffAt x).neg,
    fun x y z hz => by dsimp only; rw [η.compat x y z hz]; ring⟩

instance : Sub (Form01 X) where
  sub η η' := ⟨fun x z => η.coeffAt x z - η'.coeffAt x z,
    fun x z hz => by dsimp only; rw [η.coeffAt_zero_off x z hz, η'.coeffAt_zero_off x z hz, sub_zero],
    fun x => (η.contDiffOn_coeffAt x).sub (η'.contDiffOn_coeffAt x),
    fun x y z hz => by dsimp only; rw [η.compat x y z hz, η'.compat x y z hz]; ring⟩

instance : SMul ℂ (Form01 X) where
  smul c η := ⟨fun x z => c * η.coeffAt x z,
    fun x z hz => by dsimp only; rw [η.coeffAt_zero_off x z hz, mul_zero],
    fun x => contDiffOn_const.mul (η.contDiffOn_coeffAt x),
    fun x y z hz => by dsimp only; rw [η.compat x y z hz]; ring⟩

@[simp] theorem coeffAt_zero (x : X) (z : ℂ) : (0 : Form01 X).coeffAt x z = 0 := rfl

@[simp] theorem coeffAt_add (η η' : Form01 X) (x : X) (z : ℂ) :
    (η + η').coeffAt x z = η.coeffAt x z + η'.coeffAt x z := rfl

@[simp] theorem coeffAt_neg (η : Form01 X) (x : X) (z : ℂ) :
    (-η).coeffAt x z = -η.coeffAt x z := rfl

@[simp] theorem coeffAt_sub (η η' : Form01 X) (x : X) (z : ℂ) :
    (η - η').coeffAt x z = η.coeffAt x z - η'.coeffAt x z := rfl

@[simp] theorem coeffAt_smul (c : ℂ) (η : Form01 X) (x : X) (z : ℂ) :
    (c • η).coeffAt x z = c * η.coeffAt x z := rfl

instance : AddCommGroup (Form01 X) where
  add_assoc a b c := by ext x z _; simp; ring
  zero_add a := by ext x z _; simp
  add_zero a := by ext x z _; simp
  add_comm a b := by ext x z _; simp; ring
  neg_add_cancel a := by ext x z _; simp
  sub_eq_add_neg a b := by ext x z _; simp; ring
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module ℂ (Form01 X) where
  smul_zero a := by ext x z _; simp
  smul_add a b c := by ext x z _; simp; ring
  add_smul a b c := by ext x z _; simp; ring
  zero_smul a := by ext x z _; simp
  one_smul a := by ext x z _; simp
  mul_smul a b c := by ext x z _; simp; ring

end Form01

end RS
