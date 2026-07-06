import Jacobian.LaurentTail.Truncation

/-!
# The comparison `H1Tail D ≃ₗ Cech.H1 D` (laurent-tails, design §4.3/§5)

Unit: laurent-tails (`docs/design/laurent-tails.md`).

Work in progress: see the file-end note for exact status.
-/

open scoped ContDiff Manifold Classical
open Set TopologicalSpace RS.Cech

set_option maxHeartbeats 1000000

namespace RS.LaurentTail

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [CompactSpace X] [ConnectedSpace X] [T1Space X] [DecidableEq X]

/-! ### Small helper lemmas towards the construction -/

/-- Isolated-singularity fact for a general (not necessarily connected/global) germ: away from
`p`, `φ` is regular (order `≥ 0`) on some open neighbourhood of `p` inside its domain. -/
theorem exists_clean_nhds {U : Set X} (hU : IsOpen U) (φ : RS.MeroGermOn X U) {p : X}
    (hp : p ∈ U) :
    ∃ V : Opens X, p ∈ V ∧ (V : Set X) ⊆ U ∧
      ∀ x ∈ (V : Set X), x ≠ p → (0 : WithTop ℤ) ≤ φ.ord x := by
  obtain ⟨t, ht, hfin⟩ := (φ.divisorOn).supportLocallyFiniteWithinDomain p hp
  set F : Set X := (t ∩ (φ.divisorOn).support) \ {p} with hF_def
  have hFfin : F.Finite := hfin.subset (fun x hx => hx.1)
  have hpF : p ∉ F := fun h => h.2 rfl
  refine ⟨⟨(interior t \ F) ∩ U, (isOpen_interior.sdiff hFfin.isClosed).inter hU⟩,
    ⟨⟨mem_interior_iff_mem_nhds.2 ht, hpF⟩, hp⟩, inter_subset_right, fun x hx hxp => ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  have hxF : x ∈ F := by
    refine ⟨⟨interior_subset hx.1.1, ?_⟩, hxp⟩
    show (φ.divisorOn) x ≠ 0
    rw [RS.MeroGermOn.divisorOn_apply]
    intro heq
    rw [WithTop.untop₀_eq_zero] at heq
    rcases heq with heq | heq
    · rw [heq] at hcon; exact absurd hcon (lt_irrefl 0)
    · rw [heq] at hcon; exact absurd hcon (by simp)
  exact hx.1.2 hxF

/-- `C1.retype` commutes with restriction along a refinement index (both sides are literally the
same restriction of the same underlying germ). -/
theorem resC1_retype {D D' : RS.Divisor X} {Ω : Opens X} {𝒰 𝒱 : RS.Cech.FinCover Ω}
    (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : RS.Cech.IsRefIdx 𝒰 𝒱 τ) (f : RS.Cech.C1 D' 𝒰)
    (hf : f.MemLD D) (hf' : (RS.Cech.resC1 D' τ hτ f).MemLD D) :
    RS.Cech.resC1 D τ hτ (RS.Cech.C1.retype f hf) =
      RS.Cech.C1.retype (RS.Cech.resC1 D' τ hτ f) hf' := by
  funext p
  apply Subtype.ext
  have hL : (RS.Cech.resC1 D τ hτ (RS.Cech.C1.retype f hf) p : RS.MeroGermOn X _) =
      RS.MeroGermOn.restrict (inf_le_inf (hτ p.1) (hτ p.2))
        (f (τ p.1, τ p.2) : RS.MeroGermOn X _) := by
    rw [RS.Cech.resC1_apply, RS.Cech.restrictL_apply_coe, RS.Cech.C1.retype_apply_coe]
  have hR : (RS.Cech.C1.retype (RS.Cech.resC1 D' τ hτ f) hf' p : RS.MeroGermOn X _) =
      RS.MeroGermOn.restrict (inf_le_inf (hτ p.1) (hτ p.2))
        (f (τ p.1, τ p.2) : RS.MeroGermOn X _) := by
    rw [RS.Cech.C1.retype_apply_coe, RS.Cech.resC1_apply, RS.Cech.restrictL_apply_coe]
  rw [hL, hR]

/-- `mlClass` is compatible with refining the underlying cover: pulling the realizing `0`-cochain
back along a refinement index gives the same class in `H1 D`. -/
theorem mlClass_res {D D' : RS.Divisor X} {𝒰 𝒱 : RS.Cech.FinCover (⊤ : Opens X)}
    (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : RS.Cech.IsRefIdx 𝒰 𝒱 τ) (g : RS.Cech.C0 D' 𝒰)
    (hg : (RS.Cech.d0 D' 𝒰 g).MemLD D)
    (hg' : (RS.Cech.d0 D' 𝒱 (RS.Cech.resC0 D' τ hτ g)).MemLD D) :
    RS.Cech.mlClass 𝒰 g hg = RS.Cech.mlClass 𝒱 (RS.Cech.resC0 D' τ hτ g) hg' := by
  have hd0 : RS.Cech.d0 D' 𝒱 (RS.Cech.resC0 D' τ hτ g) =
      RS.Cech.resC1 D' τ hτ (RS.Cech.d0 D' 𝒰 g) :=
    (LinearMap.congr_fun (RS.Cech.resC1_comp_d0 D' τ hτ) g).symm
  have hg'' : (RS.Cech.resC1 D' τ hτ (RS.Cech.d0 D' 𝒰 g)).MemLD D := hd0 ▸ hg'
  have key : RS.Cech.resZ1 D τ hτ
      ⟨RS.Cech.C1.retype (RS.Cech.d0 D' 𝒰 g) hg, RS.Cech.C1.retype_mem_Z1 hg⟩ =
      ⟨RS.Cech.C1.retype (RS.Cech.d0 D' 𝒱 (RS.Cech.resC0 D' τ hτ g)) hg',
        RS.Cech.C1.retype_mem_Z1 hg'⟩ := by
    apply Subtype.ext
    rw [RS.Cech.resZ1_apply_coe]
    show RS.Cech.resC1 D τ hτ (RS.Cech.C1.retype (RS.Cech.d0 D' 𝒰 g) hg) =
      (RS.Cech.C1.retype (RS.Cech.d0 D' 𝒱 (RS.Cech.resC0 D' τ hτ g)) hg' : RS.Cech.C1 D 𝒱)
    rw [resC1_retype τ hτ (RS.Cech.d0 D' 𝒰 g) hg hg'']
    congr 1
    exact hd0.symm
  rw [RS.Cech.mlClass, RS.Cech.mlClass, ← RS.Cech.toH1_resH1 D τ hτ, RS.Cech.resH1_mk, key]

/-! ### The per-point construction: realizing a clean representative -/

/-- The 2-member cover `{V, X ∖ {p}}`, used to realize a single tail datum at `p`. -/
noncomputable def pairCover (p : X) (V : Opens X) (hpV : p ∈ V) :
    RS.Cech.FinCover (⊤ : Opens X) where
  n := 2
  U := ![V, ⟨{p}ᶜ, isOpen_compl_singleton⟩]
  le_base _ := le_top
  covers x _ := by
    by_cases hx : x = p
    · exact ⟨0, by simpa [hx] using hpV⟩
    · exact ⟨1, by simpa using hx⟩

end RS.LaurentTail
