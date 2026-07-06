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

/-! ### §5 step 2: member splitting via disk acyclicity -/

variable [T2Space X] [CompactSpace X]

/-- Step 2: each induced cocycle splits, since `𝒰.U i` is a chart disk (disk acyclicity). -/
theorem exists_splitting (h𝒰 : 𝒰.IsGood) {f : C1 D 𝒱} (hf : f ∈ Z1 D 𝒱) :
    ∃ gFam : ∀ i : Fin 𝒰.n, C0 D (𝒱.induced (𝒰.U i)),
      ∀ i, d0 D (𝒱.induced (𝒰.U i)) (gFam i) = indCocycle D i f := by
  choose gFam hgFam using fun i : Fin 𝒰.n =>
    ((subsingleton_h1Cover_iff D (𝒱.induced (𝒰.U i))).mp
      (subsingleton_h1Cover_of_isChartDisk (h𝒰 i) D (𝒱.induced (𝒰.U i)))) (indCocycle_mem_Z1 D i hf)
  exact ⟨gFam, hgFam⟩

/-- The pointwise splitting identity extracted from `exists_splitting`, at `LinSysOn`
(submodule) level (used both for the cross-glue compatibility and for the final comparison,
§5 steps 3/5). -/
theorem splitting_eq {f : C1 D 𝒱} {gFam : ∀ i : Fin 𝒰.n, C0 D (𝒱.induced (𝒰.U i))}
    (hgFam : ∀ i, d0 D (𝒱.induced (𝒰.U i)) (gFam i) = indCocycle D i f) (i : Fin 𝒰.n)
    (α β : Fin 𝒱.n) :
    LinSysOn.restrictL D
        (inf_le_right : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ≤
          (𝒱.induced (𝒰.U i)).U β) (gFam i β) -
      LinSysOn.restrictL D
        (inf_le_left : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ≤
          (𝒱.induced (𝒰.U i)).U α) (gFam i α) =
    indCocycle D i f (α, β) := by
  have hd := congrFun (hgFam i) (α, β)
  rw [d0_apply] at hd
  exact hd

/-- Raw `MeroGermOn`-level form of `splitting_eq`. -/
theorem splitting_eq' {f : C1 D 𝒱} {gFam : ∀ i : Fin 𝒰.n, C0 D (𝒱.induced (𝒰.U i))}
    (hgFam : ∀ i, d0 D (𝒱.induced (𝒰.U i)) (gFam i) = indCocycle D i f) (i : Fin 𝒰.n)
    (α β : Fin 𝒱.n) :
    (RS.MeroGermOn.restrict
        (inf_le_right : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ≤
          (𝒱.induced (𝒰.U i)).U β)
        (gFam i β : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U β : Set X)) -
      RS.MeroGermOn.restrict
        (inf_le_left : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ≤
          (𝒱.induced (𝒰.U i)).U α)
        (gFam i α : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U α : Set X)) :
      RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β : Set X)) =
    RS.MeroGermOn.restrict (inf_inf_inf_le (𝒰.U i) (𝒱.U α) (𝒱.U β))
      (f (α, β) : RS.MeroGermOn X (𝒱.U α ⊓ 𝒱.U β : Set X)) := by
  exact congrArg Subtype.val (splitting_eq D hgFam i α β)

/-- `splitting_eq'`, restricted down to an arbitrary smaller open `W` (§5 step 3's workhorse:
lets us compare the splittings at TWO different good-cover members `i`, `j` on their common
overlap with a member of `𝒱`). -/
theorem splitting_eq_restrict {f : C1 D 𝒱} {gFam : ∀ i : Fin 𝒰.n, C0 D (𝒱.induced (𝒰.U i))}
    (hgFam : ∀ i, d0 D (𝒱.induced (𝒰.U i)) (gFam i) = indCocycle D i f) (i : Fin 𝒰.n)
    (α β : Fin 𝒱.n) {W : Opens X} (hWα : W ≤ (𝒱.induced (𝒰.U i)).U α)
    (hWβ : W ≤ (𝒱.induced (𝒰.U i)).U β) (hWαβ : W ≤ 𝒱.U α ⊓ 𝒱.U β) :
    RS.MeroGermOn.restrict hWβ (gFam i β : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U β : Set X)) -
      RS.MeroGermOn.restrict hWα (gFam i α : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U α : Set X)) =
    RS.MeroGermOn.restrict hWαβ (f (α, β) : RS.MeroGermOn X (𝒱.U α ⊓ 𝒱.U β : Set X)) := by
  have hWαβ' : W ≤ (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β := le_inf hWα hWβ
  have hcast := congrArg (RS.MeroGermOn.restrict hWαβ') (splitting_eq' D hgFam i α β)
  rw [map_sub] at hcast
  have e1 : (RS.MeroGermOn.restrict hWαβ'
      (RS.MeroGermOn.restrict
        (inf_le_right : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ≤
          (𝒱.induced (𝒰.U i)).U β)
        (gFam i β : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U β : Set X)))) =
      RS.MeroGermOn.restrict hWβ (gFam i β : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U β : Set X)) :=
    RS.MeroGermOn.restrict_restrict inf_le_right hWαβ' _
  have e2 : (RS.MeroGermOn.restrict hWαβ'
      (RS.MeroGermOn.restrict
        (inf_le_left : (𝒱.induced (𝒰.U i)).U α ⊓ (𝒱.induced (𝒰.U i)).U β ≤
          (𝒱.induced (𝒰.U i)).U α)
        (gFam i α : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U α : Set X)))) =
      RS.MeroGermOn.restrict hWα (gFam i α : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U α : Set X)) :=
    RS.MeroGermOn.restrict_restrict inf_le_left hWαβ' _
  have e3 : (RS.MeroGermOn.restrict hWαβ'
      (RS.MeroGermOn.restrict (inf_inf_inf_le (𝒰.U i) (𝒱.U α) (𝒱.U β))
        (f (α, β) : RS.MeroGermOn X (𝒱.U α ⊓ 𝒱.U β : Set X)))) =
      RS.MeroGermOn.restrict hWαβ (f (α, β) : RS.MeroGermOn X (𝒱.U α ⊓ 𝒱.U β : Set X)) :=
    RS.MeroGermOn.restrict_restrict (inf_inf_inf_le (𝒰.U i) (𝒱.U α) (𝒱.U β)) hWαβ' _
  rw [e1, e2, e3] at hcast
  exact hcast

/-! ### §5 step 3: cross-glue -/

/-- The local candidate for the glued section on `𝒰.U i ⊓ 𝒰.U j` (§5 step 3). -/
noncomputable def patch (gFam : ∀ i : Fin 𝒰.n, C0 D (𝒱.induced (𝒰.U i))) (i j : Fin 𝒰.n)
    (α : Fin 𝒱.n) : RS.LinSysOn D (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α : Set X) :=
  LinSysOn.restrictL D
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ≤ (𝒱.induced (𝒰.U j)).U α) (gFam j α) -
    LinSysOn.restrictL D
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ≤ (𝒱.induced (𝒰.U i)).U α) (gFam i α)

theorem patch_coe (gFam : ∀ i : Fin 𝒰.n, C0 D (𝒱.induced (𝒰.U i))) (i j : Fin 𝒰.n)
    (α : Fin 𝒱.n) :
    (patch D gFam i j α : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α : Set X)) =
      (RS.MeroGermOn.restrict
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
            𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ≤ (𝒱.induced (𝒰.U j)).U α)
          (gFam j α : RS.MeroGermOn X ((𝒱.induced (𝒰.U j)).U α : Set X))) -
        (RS.MeroGermOn.restrict
          (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ≤ (𝒱.induced (𝒰.U i)).U α)
          (gFam i α : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U α : Set X))) := rfl

/-- Compatibility of the patches on overlaps (§5 step 3). -/
theorem patch_compat {f : C1 D 𝒱} {gFam : ∀ i : Fin 𝒰.n, C0 D (𝒱.induced (𝒰.U i))}
    (hgFam : ∀ i, d0 D (𝒱.induced (𝒰.U i)) (gFam i) = indCocycle D i f) (i j : Fin 𝒰.n)
    (α β : Fin 𝒱.n) :
    RS.MeroGermOn.restrict
        (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ⊓ (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β) ≤ 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α)
        (patch D gFam i j α : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α : Set X)) =
      RS.MeroGermOn.restrict
        (inf_le_right : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ⊓ (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β) ≤ 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β)
        (patch D gFam i j β : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β : Set X)) := by
  have hWα : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ⊓ (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β) ≤ 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α := inf_le_left
  have hWβ : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ⊓ (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β) ≤ 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β := inf_le_right
  have hWαj : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ⊓ (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β) ≤ (𝒱.induced (𝒰.U j)).U α :=
    hWα.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  have hWαi : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ⊓ (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β) ≤ (𝒱.induced (𝒰.U i)).U α :=
    hWα.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  have hWβj : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ⊓ (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β) ≤ (𝒱.induced (𝒰.U j)).U β :=
    hWβ.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  have hWβi : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ⊓ (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β) ≤ (𝒱.induced (𝒰.U i)).U β :=
    hWβ.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  have hWαβ𝒱 : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ⊓ (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β) ≤ 𝒱.U α ⊓ 𝒱.U β :=
    le_inf (hWα.trans inf_le_right) (hWβ.trans inf_le_right)
  have hj := splitting_eq_restrict D hgFam j α β hWαj hWβj hWαβ𝒱
  have hi := splitting_eq_restrict D hgFam i α β hWαi hWβi hWαβ𝒱
  have hcompute : RS.MeroGermOn.restrict hWα
      (patch D gFam i j α : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α : Set X)) -
      RS.MeroGermOn.restrict hWβ
        (patch D gFam i j β : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β : Set X)) =
      (RS.MeroGermOn.restrict hWαj
          (gFam j α : RS.MeroGermOn X ((𝒱.induced (𝒰.U j)).U α : Set X)) -
        RS.MeroGermOn.restrict hWβj
          (gFam j β : RS.MeroGermOn X ((𝒱.induced (𝒰.U j)).U β : Set X))) -
      (RS.MeroGermOn.restrict hWαi
          (gFam i α : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U α : Set X)) -
        RS.MeroGermOn.restrict hWβi
          (gFam i β : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U β : Set X))) := by
    rw [patch_coe, patch_coe, map_sub, map_sub]
    have e1 : (RS.MeroGermOn.restrict hWα
        (RS.MeroGermOn.restrict
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
            𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ≤ (𝒱.induced (𝒰.U j)).U α)
          (gFam j α : RS.MeroGermOn X ((𝒱.induced (𝒰.U j)).U α : Set X)))) =
        RS.MeroGermOn.restrict hWαj (gFam j α : RS.MeroGermOn X ((𝒱.induced (𝒰.U j)).U α : Set X)) :=
      RS.MeroGermOn.restrict_restrict _ hWα _
    have e2 : (RS.MeroGermOn.restrict hWα
        (RS.MeroGermOn.restrict
          (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ≤ (𝒱.induced (𝒰.U i)).U α)
          (gFam i α : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U α : Set X)))) =
        RS.MeroGermOn.restrict hWαi (gFam i α : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U α : Set X)) :=
      RS.MeroGermOn.restrict_restrict _ hWα _
    have e3 : (RS.MeroGermOn.restrict hWβ
        (RS.MeroGermOn.restrict
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
            𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β ≤ (𝒱.induced (𝒰.U j)).U β)
          (gFam j β : RS.MeroGermOn X ((𝒱.induced (𝒰.U j)).U β : Set X)))) =
        RS.MeroGermOn.restrict hWβj (gFam j β : RS.MeroGermOn X ((𝒱.induced (𝒰.U j)).U β : Set X)) :=
      RS.MeroGermOn.restrict_restrict _ hWβ _
    have e4 : (RS.MeroGermOn.restrict hWβ
        (RS.MeroGermOn.restrict
          (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β ≤ (𝒱.induced (𝒰.U i)).U β)
          (gFam i β : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U β : Set X)))) =
        RS.MeroGermOn.restrict hWβi (gFam i β : RS.MeroGermOn X ((𝒱.induced (𝒰.U i)).U β : Set X)) :=
      RS.MeroGermOn.restrict_restrict _ hWβ _
    rw [e1, e2, e3, e4]
    abel
  have hfinal : RS.MeroGermOn.restrict hWα
      (patch D gFam i j α : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α : Set X)) -
      RS.MeroGermOn.restrict hWβ
        (patch D gFam i j β : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U β : Set X)) = 0 := by
    rw [hcompute]
    linear_combination hi - hj
  exact sub_eq_zero.mp hfinal

/-- The glued section `F_{ij}` on `𝒰.U i ⊓ 𝒰.U j`, restricting back to `patch` on each
`Uᵢ⊓Uⱼ⊓Vα` (§5 step 3). -/
theorem exists_crossGlue {f : C1 D 𝒱} (hf : f ∈ Z1 D 𝒱)
    {gFam : ∀ i : Fin 𝒰.n, C0 D (𝒱.induced (𝒰.U i))}
    (hgFam : ∀ i, d0 D (𝒱.induced (𝒰.U i)) (gFam i) = indCocycle D i f) (i j : Fin 𝒰.n) :
    ∃ Φ : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j : Set X), ∀ α : Fin 𝒱.n,
      RS.MeroGermOn.restrict (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ≤ 𝒰.U i ⊓ 𝒰.U j) Φ =
        (patch D gFam i j α : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α : Set X)) := by
  have hWopen : ∀ α : Fin 𝒱.n, IsOpen ((𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α : Opens X) : Set X) :=
    fun α => (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α).2
  have hunion : (⋃ α : Fin 𝒱.n, ((𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α : Opens X) : Set X)) =
      (𝒰.U i ⊓ 𝒰.U j : Set X) := iUnion_inf_eq (𝒰.U i ⊓ 𝒰.U j) le_top
  obtain ⟨Ψ, hΨ⟩ := RS.MeroGermOn.exists_glue hWopen
    (fun α => (patch D gFam i j α : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α : Set X)))
    (fun α β => patch_compat D hgFam i j α β)
  refine ⟨MeroGermOn.congrSet hunion Ψ, fun α => ?_⟩
  have hstep : RS.MeroGermOn.restrict
      (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ≤ 𝒰.U i ⊓ 𝒰.U j)
      (RS.MeroGermOn.restrict hunion.ge Ψ) =
      RS.MeroGermOn.restrict
        (Set.subset_iUnion (fun α => ((𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α : Opens X) : Set X)) α) Ψ :=
    RS.MeroGermOn.restrict_restrict hunion.ge inf_le_left Ψ
  show RS.MeroGermOn.restrict (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α ≤ 𝒰.U i ⊓ 𝒰.U j)
      (MeroGermOn.congrSet hunion Ψ) =
      (patch D gFam i j α : RS.MeroGermOn X (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒱.U α : Set X))
  exact hstep.trans (hΨ α)

end RS.Cech
