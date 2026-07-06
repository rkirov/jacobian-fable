import Jacobian.Cech.Injectivity
import Jacobian.Dbar.DiskAcyclic
import Jacobian.Meromorphic.Gluing

/-!
# Leray's theorem and the cocycle-trade lemma (`Jacobian/DolbeaultComparison/Leray.lean`)

Unit: dolbeault-comparison (`docs/design/dolbeault-comparison.md` §5). This is the FIRST file of
the unit and the gate for `finiteness-and-chi` (§0.1 of the design): everything here uses only
cech's cover/cochain/colimit machinery, mero's gluing sheaf axioms, and dbar's disk acyclicity
(`subsingleton_h1Cover_of_isChartDisk`, general-`D`, added to `Jacobian/Dbar/DiskAcyclic.lean`
under this unit's authorization) as black boxes — no `Form01`, no PoU, no ∂̄-solving.

* `FinCover.induced 𝒱 V : FinCover V`: the induced cover of a member `V` of `⊤`'s cover `𝒱`.
* `exists_goodCover`: good covers exist (3-line corollary of cech's `exists_good_refinement`).
* `exists_trade` (Forster 14.6(a), qualitative): cocycles on any refinement of a good cover are,
  up to coboundary, restrictions of cocycles on the good cover — the Schwartz surjectivity input
  for finiteness-and-chi.
* `resH1_surjective_of_isGood` / `toH1_surjective_of_isGood` (Leray 12.8 surjectivity;
  injectivity is cech's `toH1_injective`, ALREADY on disk) / `h1CoverEquiv`.
-/

open scoped ContDiff Manifold
open Set TopologicalSpace RS.Cech

namespace RS.Cech

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### A reusable lattice fact -/

theorem inf_inf_inf_le (a b c : Opens X) : (a ⊓ b) ⊓ (a ⊓ c) ≤ b ⊓ c :=
  le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)

/-! ### The induced cover of a member -/

/-- The induced cover of a member: `(V ⊓ 𝒱.U α)_α : FinCover V` for `V ≤ ⊤`. -/
def FinCover.induced (𝒱 : FinCover (⊤ : Opens X)) (V : Opens X) : FinCover V where
  n := 𝒱.n
  U := fun α => V ⊓ 𝒱.U α
  le_base := fun _ => inf_le_left
  covers := fun x hx => by
    obtain ⟨α, hα⟩ := 𝒱.covers x trivial
    exact ⟨α, hx, hα⟩

@[simp] theorem FinCover.induced_n (𝒱 : FinCover (⊤ : Opens X)) (V : Opens X) :
    (𝒱.induced V).n = 𝒱.n := rfl

@[simp] theorem FinCover.induced_U (𝒱 : FinCover (⊤ : Opens X)) (V : Opens X) (α : Fin 𝒱.n) :
    (𝒱.induced V).U α = V ⊓ 𝒱.U α := rfl

/-- Good covers exist (§6.3 of cech-cohomology, applied to the trivial cover). -/
theorem exists_goodCover [T2Space X] [CompactSpace X] :
    ∃ 𝒰 : FinCover (⊤ : Opens X), 𝒰.IsGood := by
  obtain ⟨𝒲, -, hgood⟩ := exists_good_refinement (FinCover.single (⊤ : Opens X))
  exact ⟨𝒲, hgood⟩

/-! ### §5 step 1: the induced cocycle -/

variable {𝒰 𝒱 : FinCover (⊤ : Opens X)} (D : RS.Divisor X)

/-- The induced cocycle on `𝒱.induced (𝒰.U i)` (§5 step 1): componentwise restriction of `f`
along the "drop the `𝒰.U i` factor" lattice map. -/
noncomputable def indCocycle (i : Fin 𝒰.n) (f : C1 D 𝒱) : C1 D (𝒱.induced (𝒰.U i)) :=
  fun p => LinSysOn.restrictL D (inf_inf_inf_le (𝒰.U i) (𝒱.U p.1) (𝒱.U p.2)) (f p)

theorem indCocycle_mem_Z1 (i : Fin 𝒰.n) {f : C1 D 𝒱} (hf : f ∈ Z1 D 𝒱) :
    indCocycle D i f ∈ Z1 D (𝒱.induced (𝒰.U i)) := by
  rw [mem_Z1_iff]
  rintro ⟨α, β, γ⟩
  have hβγ𝒱ᵢ : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ⊓ (𝒱.induced (𝒰.U i)).U γ ≤
      (𝒱.induced (𝒰.U i)).U β ⊓ (𝒱.induced (𝒰.U i)).U γ :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hαγ𝒱ᵢ : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ⊓ (𝒱.induced (𝒰.U i)).U γ ≤
      (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U γ :=
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hαβ𝒱ᵢ : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ⊓ (𝒱.induced (𝒰.U i)).U γ ≤
      (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β := inf_le_left
  have hβγ : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ⊓ (𝒱.induced (𝒰.U i)).U γ ≤
      𝒱.U β ⊓ 𝒱.U γ := hβγ𝒱ᵢ.trans (inf_inf_inf_le (𝒰.U i) (𝒱.U β) (𝒱.U γ))
  have hαγ : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ⊓ (𝒱.induced (𝒰.U i)).U γ ≤
      𝒱.U α ⊓ 𝒱.U γ := hαγ𝒱ᵢ.trans (inf_inf_inf_le (𝒰.U i) (𝒱.U α) (𝒱.U γ))
  have hαβ : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ⊓ (𝒱.induced (𝒰.U i)).U γ ≤
      𝒱.U α ⊓ 𝒱.U β := hαβ𝒱ᵢ.trans (inf_inf_inf_le (𝒰.U i) (𝒱.U α) (𝒱.U β))
  have hW : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ⊓ (𝒱.induced (𝒰.U i)).U γ ≤
      𝒱.U α ⊓ 𝒱.U β ⊓ 𝒱.U γ := le_inf hαβ (inf_le_right.trans inf_le_right)
  have key := Z1.rel_res D hf α β γ hW hβγ hαγ hαβ
  have hkey : (RS.MeroGermOn.restrict hβγ (f (β, γ) : RS.MeroGermOn X (𝒱.U β ⊓ 𝒱.U γ : Set X)) -
      RS.MeroGermOn.restrict hαγ (f (α, γ) : RS.MeroGermOn X (𝒱.U α ⊓ 𝒱.U γ : Set X)) +
      RS.MeroGermOn.restrict hαβ (f (α, β) : RS.MeroGermOn X (𝒱.U α ⊓ 𝒱.U β : Set X)) :
      RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ⊓
        (𝒱.induced (𝒰.U i)).U γ : Set X)) = 0 := by
    have hcast := congrArg Subtype.val key
    simpa using hcast
  apply Subtype.ext
  rw [d1_apply]
  show (RS.MeroGermOn.restrict hβγ𝒱ᵢ
        (indCocycle D i f (β, γ) : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U β ⊓
          (𝒱.induced (𝒰.U i)).U γ : Set X)) -
      RS.MeroGermOn.restrict hαγ𝒱ᵢ
        (indCocycle D i f (α, γ) : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U α ⊓
          (𝒱.induced (𝒰.U i)).U γ : Set X)) +
      RS.MeroGermOn.restrict hαβ𝒱ᵢ
        (indCocycle D i f (α, β) : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U α ⊓
          (𝒱.induced (𝒰.U i)).U β : Set X)) :
      RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ⊓
        (𝒱.induced (𝒰.U i)).U γ : Set X)) = 0
  show (RS.MeroGermOn.restrict hβγ𝒱ᵢ
        (RS.MeroGermOn.restrict (inf_inf_inf_le (𝒰.U i) (𝒱.U β) (𝒱.U γ))
          (f (β, γ) : RS.MeroGermOn X (𝒱.U β ⊓ 𝒱.U γ : Set X))) -
      RS.MeroGermOn.restrict hαγ𝒱ᵢ
        (RS.MeroGermOn.restrict (inf_inf_inf_le (𝒰.U i) (𝒱.U α) (𝒱.U γ))
          (f (α, γ) : RS.MeroGermOn X (𝒱.U α ⊓ 𝒱.U γ : Set X))) +
      RS.MeroGermOn.restrict hαβ𝒱ᵢ
        (RS.MeroGermOn.restrict (inf_inf_inf_le (𝒰.U i) (𝒱.U α) (𝒱.U β))
          (f (α, β) : RS.MeroGermOn X (𝒱.U α ⊓ 𝒱.U β : Set X))) :
      RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ⊓
        (𝒱.induced (𝒰.U i)).U γ : Set X)) = 0
  have e1 : (RS.MeroGermOn.restrict hβγ𝒱ᵢ
      (RS.MeroGermOn.restrict (inf_inf_inf_le (𝒰.U i) (𝒱.U β) (𝒱.U γ))
        (f (β, γ) : RS.MeroGermOn X (𝒱.U β ⊓ 𝒱.U γ : Set X)))) =
      RS.MeroGermOn.restrict hβγ (f (β, γ) : RS.MeroGermOn X (𝒱.U β ⊓ 𝒱.U γ : Set X)) :=
    RS.MeroGermOn.restrict_restrict (inf_inf_inf_le (𝒰.U i) (𝒱.U β) (𝒱.U γ)) hβγ𝒱ᵢ _
  have e2 : (RS.MeroGermOn.restrict hαγ𝒱ᵢ
      (RS.MeroGermOn.restrict (inf_inf_inf_le (𝒰.U i) (𝒱.U α) (𝒱.U γ))
        (f (α, γ) : RS.MeroGermOn X (𝒱.U α ⊓ 𝒱.U γ : Set X)))) =
      RS.MeroGermOn.restrict hαγ (f (α, γ) : RS.MeroGermOn X (𝒱.U α ⊓ 𝒱.U γ : Set X)) :=
    RS.MeroGermOn.restrict_restrict (inf_inf_inf_le (𝒰.U i) (𝒱.U α) (𝒱.U γ)) hαγ𝒱ᵢ _
  have e3 : (RS.MeroGermOn.restrict hαβ𝒱ᵢ
      (RS.MeroGermOn.restrict (inf_inf_inf_le (𝒰.U i) (𝒱.U α) (𝒱.U β))
        (f (α, β) : RS.MeroGermOn X (𝒱.U α ⊓ 𝒱.U β : Set X)))) =
      RS.MeroGermOn.restrict hαβ (f (α, β) : RS.MeroGermOn X (𝒱.U α ⊓ 𝒱.U β : Set X)) :=
    RS.MeroGermOn.restrict_restrict (inf_inf_inf_le (𝒰.U i) (𝒱.U α) (𝒱.U β)) hαβ𝒱ᵢ _
  rw [e1, e2, e3]
  exact hkey

end RS.Cech
