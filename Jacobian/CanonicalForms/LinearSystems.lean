import Jacobian.CanonicalForms.Differential

/-!
# `Ω(D)`-style linear systems and Mittag-Leffler form data (D11/D13, partial)

Unit: canonical-forms (`docs/design/canonical-forms.md` §2 D11/D13, §4.5).

* `MForm.OmegaSpace D` (Miranda's `L⁽¹⁾(D)`/Forster's `Γ(X,Ω_D)`): meromorphic 1-forms with
  divisor `≥ -D`, defined order-wise (mirrors `LinSys`'s own primary definition,
  `Jacobian/Meromorphic/LinearSystem.lean:52`) so that submodule closure is a direct transcription
  of `MForm.ord`'s arithmetic; `mem_omegaSpace_iff` recovers the divisor-level disjunction as a
  *theorem*, mirroring `mem_linSys_iff_eq_zero_or_le_divisor`.
* `i D` (index of speciality): `Module.finrank ℂ (OmegaSpace D)`.
* `MLFormData` (D13, Forster §17.1–17.2): a thin `X`-level wrapper around residue-calculus's
  already-built `PrincipalPartData`, one datum per point read in that point's own preferred chart.

**Deferred** (documented, not sorried — see the unit root's deferral notes): `Ω_iso_linSys`,
`i_eq_l_add_canonicalDivisorOf`, `holomorphicMFormsEquiv`, `genus_eq_finrank_omegaSpace_zero`.
All four need either `canonicalDivisorOf`/one-dimensionality (D8/D10, themselves blocked on the
deferred zero-dichotomy D5) or the "nonnegative order at a chart center propagates to analyticity
on the WHOLE, possibly disconnected, target" upgrade (P6 step 3) — the same junk-value-at-
removable-points subtlety documented in `Differential.lean`'s module-docstring, here appearing as
design's own flagged risk (§7 item 2). `MForm.OmegaSpace`, `i`, and the *forward* holomorphic
embedding (`Form1.toMForm` composed with `ofForm1_ord_nonneg`, already built in `Differential.lean`)
are unaffected and fully proved.
-/

open scoped ContDiff Manifold Classical
open Set IsManifold Filter Topology

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace MForm

/-! ### Order arithmetic (junk-robust, needed for `OmegaSpace`'s submodule closure) -/

theorem ord_add (θ η : MForm X) (x : X) : min (θ.ord x) (η.ord x) ≤ (θ + η).ord x := by
  have hf : (θ + η).coeffAt x = θ.coeffAt x + η.coeffAt x := funext fun z => coeffAt_add θ η x z
  show min (θ.ord x) (η.ord x) ≤ meromorphicOrderAt ((θ + η).coeffAt x) (chartAt ℂ x x)
  rw [hf]
  exact meromorphicOrderAt_add (θ.meromorphicAt_coeffAt x) (η.meromorphicAt_coeffAt x)

theorem ord_smul {c : ℂ} (hc : c ≠ 0) (θ : MForm X) (x : X) : (c • θ).ord x = θ.ord x := by
  have hf : (c • θ).coeffAt x = c • θ.coeffAt x := funext fun z => by
    rw [coeffAt_smul]; rfl
  show meromorphicOrderAt ((c • θ).coeffAt x) (chartAt ℂ x x) = θ.ord x
  rw [hf]
  exact meromorphicOrderAt_smul_of_ne_zero analyticAt_const hc

/-! ### `MForm.OmegaSpace` (D11) -/

variable [T1Space X] [T2Space X] [CompactSpace X]

/-- Meromorphic 1-forms with divisor `≥ -D` (Miranda's `L⁽¹⁾(D)`/Forster's `Γ(X, Ω_D)`), defined
order-wise (mirrors `LinSys`'s own primary definition). -/
def OmegaSpace (D : Divisor X) : Submodule ℂ (MForm X) where
  carrier := {θ | ∀ x, ((-(D x) : ℤ) : WithTop ℤ) ≤ θ.ord x}
  zero_mem' := by
    intro x
    have h0 : (0 : MForm X).ord x = ⊤ := by
      show meromorphicOrderAt (0 : ℂ → ℂ) (chartAt ℂ x x) = ⊤
      simp
    rw [h0]; exact le_top
  add_mem' := by
    intro θ η hθ hη x
    exact le_trans (le_min (hθ x) (hη x)) (ord_add θ η x)
  smul_mem' := by
    intro c θ hθ x
    rcases eq_or_ne c 0 with rfl | hc
    · have h0 : (0 : MForm X).ord x = ⊤ := by
        show meromorphicOrderAt (0 : ℂ → ℂ) (chartAt ℂ x x) = ⊤
        simp
      rw [zero_smul]
      rw [h0]; exact le_top
    · rw [ord_smul hc]; exact hθ x

theorem mem_omegaSpace_iff {D : Divisor X} {θ : MForm X} :
    θ ∈ OmegaSpace D ↔ ∀ x, ((-(D x) : ℤ) : WithTop ℤ) ≤ θ.ord x := Iff.rfl

/-- Index of speciality: `dim Ω(D)`. -/
noncomputable def i (D : Divisor X) : ℕ := Module.finrank ℂ (OmegaSpace D)

end MForm

/-! ### `MLFormData` (D13, Forster §17.1–17.2) -/

/-- A form-level Mittag-Leffler datum: at finitely many points of `X`, a principal part read in
the preferred chart. A thin wrapper around residue-calculus's already-built `PrincipalPartData`. -/
structure MLFormData (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] where
  pts : Finset X
  data : ∀ x ∈ pts, PrincipalPartData (chartAt ℂ x).target

/-- `μ` realizes the principal parts of `θ` at every point of `μ.pts` (read in each point's own
preferred chart). -/
def MLFormData.Realizes (μ : MLFormData X) (θ : MForm X) : Prop :=
  ∀ x (hx : x ∈ μ.pts), ∀ k < 0,
    laurentCoeffAt (θ.coeffAt x) (chartAt ℂ x x) k = (μ.data x hx).coeff (chartAt ℂ x x) k

/-- The total residue prescribed by the datum. -/
noncomputable def MLFormData.totalRes (μ : MLFormData X) : ℂ :=
  ∑ x ∈ μ.pts.attach, (μ.data x.1 x.2).coeff (chartAt ℂ x.1 x.1) (-1)

theorem MLFormData.Realizes.resAt_eq {μ : MLFormData X} {θ : MForm X} (h : μ.Realizes θ)
    {x : X} (hx : x ∈ μ.pts) : θ.resAt x = (μ.data x hx).coeff (chartAt ℂ x x) (-1) :=
  h x hx (-1) (by norm_num)

end RS
