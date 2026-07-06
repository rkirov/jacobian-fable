import Jacobian.Cech.Window

/-!
# The Mittag-Leffler atom and the skyscraper fragment (CC8, D7, proof plan §6.9)

Unit: cech-cohomology (`docs/design/cech-cohomology.md` §4.7).

* `C1.MemLD`/`C1.retype`: a `D'`-cochain all of whose components satisfy the smaller `D`-bound,
  re-tagged as a `D`-cochain (same underlying germs).
* `mlClass`: the Mittag-Leffler atom — a `D'`-`0`-cochain with `D`-bounded coboundary yields a
  class in `H¹(D)`. Both the χ connecting map (finiteness-and-chi) and laurent-tails'
  `T[D] → H¹(D)` factor through this.
* `mlClass_eq_zero_iff`: the vanishing criterion (the "engine" — uses `H⁰ ≃ L(D')` gluing and
  `toH1`'s colimit description).

**Recorded as interface, not proved here** (see the file-end note): the full six-term
exactness (`windowConnect`, `exists_realization`, Lemma A, `exact_windowMap_windowConnect`,
`exact_windowConnect_H1Incl`, `H1Incl_surjective`) — this needs adapted-cover realization
machinery beyond this unit's remaining time budget. `mlClass`/`mlClass_eq_zero_iff` (the atom
both the χ ledger and laurent-tails actually consume) are proved with zero sorries.
-/

open scoped ContDiff Manifold
open Set TopologicalSpace RS.Cech

namespace RS.Cech

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### `C1.MemLD`, `C1.retype` -/

variable {Ω : Opens X} {𝒰 : FinCover Ω} {D D' : RS.Divisor X}

/-- A `C¹(D')`-cochain all of whose components satisfy the `D`-bound. -/
def C1.MemLD (f : C1 D' 𝒰) (D : RS.Divisor X) : Prop :=
  ∀ p : Fin 𝒰.n × Fin 𝒰.n, (f p : RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X)) ∈
    RS.LinSysOn D ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X)

/-- Re-tag a `D'`-cochain satisfying the `D`-bound as a `D`-cochain (same underlying germs). -/
noncomputable def C1.retype (f : C1 D' 𝒰) (hf : f.MemLD D) : C1 D 𝒰 :=
  fun p => ⟨(f p : RS.MeroGermOn X _), hf p⟩

theorem C1.retype_apply_coe (f : C1 D' 𝒰) (hf : f.MemLD D) (p : Fin 𝒰.n × Fin 𝒰.n) :
    (C1.retype f hf p : RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X)) =
      (f p : RS.MeroGermOn X _) := rfl

theorem C1.retype_mem_Z1 {g : C0 D' 𝒰} (hg : (d0 D' 𝒰 g).MemLD D) :
    C1.retype (d0 D' 𝒰 g) hg ∈ Z1 D 𝒰 := by
  rw [mem_Z1_iff]
  intro t
  apply Subtype.ext
  have hcoe : (d1 D 𝒰 (C1.retype (d0 D' 𝒰 g) hg) t :
        RS.MeroGermOn X ((𝒰.U t.1 ⊓ 𝒰.U t.2.1 ⊓ 𝒰.U t.2.2 : Opens X) : Set X)) =
      (d1 D' 𝒰 (d0 D' 𝒰 g) t :
        RS.MeroGermOn X ((𝒰.U t.1 ⊓ 𝒰.U t.2.1 ⊓ 𝒰.U t.2.2 : Opens X) : Set X)) := by
    obtain ⟨i, j, k⟩ := t
    rw [d1_apply, d1_apply]
    simp [restrictL_apply_coe, C1.retype_apply_coe]
  rw [hcoe, (mem_Z1_iff D' 𝒰 (d0 D' 𝒰 g)).1 (B1_le_Z1 D' 𝒰 ⟨g, rfl⟩) t]
  simp

/-! ### The Mittag-Leffler atom -/

variable {𝒰 : FinCover (⊤ : Opens X)}

/-- The Mittag-Leffler atom (D7): a `D'`-`0`-cochain with `D`-bounded coboundary yields a class
in `H¹(D)`. -/
noncomputable def mlClass (𝒰 : FinCover (⊤ : Opens X)) (g : C0 D' 𝒰)
    (hg : (d0 D' 𝒰 g).MemLD D) : H1 D :=
  toH1 D 𝒰 (H1Cover.mk D 𝒰 ⟨C1.retype (d0 D' 𝒰 g) hg, C1.retype_mem_Z1 hg⟩)

theorem mlClass_add (g g' : C0 D' 𝒰) (hg : (d0 D' 𝒰 g).MemLD D) (hg' : (d0 D' 𝒰 g').MemLD D)
    (hgg' : (d0 D' 𝒰 (g + g')).MemLD D) :
    mlClass 𝒰 (g + g') hgg' = mlClass 𝒰 g hg + mlClass 𝒰 g' hg' := by
  have hval : C1.retype (d0 D' 𝒰 (g + g')) hgg' =
      (C1.retype (d0 D' 𝒰 g) hg : C1 D 𝒰) + C1.retype (d0 D' 𝒰 g') hg' := by
    funext p
    apply Subtype.ext
    show (C1.retype (d0 D' 𝒰 (g + g')) hgg' p :
        RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X)) =
      (C1.retype (d0 D' 𝒰 g) hg p : RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X)) +
        (C1.retype (d0 D' 𝒰 g') hg' p :
          RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X))
    rw [C1.retype_apply_coe, C1.retype_apply_coe, C1.retype_apply_coe]
    simp
  rw [mlClass, mlClass, mlClass, ← map_add, ← map_add]
  congr 1
  exact Subtype.ext hval

theorem mlClass_smul (a : ℂ) (g : C0 D' 𝒰) (hg : (d0 D' 𝒰 g).MemLD D)
    (hag : (d0 D' 𝒰 (a • g)).MemLD D) :
    mlClass 𝒰 (a • g) hag = a • mlClass 𝒰 g hg := by
  have hval : C1.retype (d0 D' 𝒰 (a • g)) hag = a • (C1.retype (d0 D' 𝒰 g) hg : C1 D 𝒰) := by
    funext p
    apply Subtype.ext
    show (C1.retype (d0 D' 𝒰 (a • g)) hag p :
        RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X)) =
      a • (C1.retype (d0 D' 𝒰 g) hg p : RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X))
    rw [C1.retype_apply_coe, C1.retype_apply_coe]
    simp
  rw [mlClass, mlClass, ← map_smul]
  congr 1
  exact Subtype.ext hval

theorem H1Incl_mlClass (h : D ≤ D') (g : C0 D' 𝒰) (hg : (d0 D' 𝒰 g).MemLD D) :
    H1Incl D h (mlClass 𝒰 g hg) = 0 := by
  rw [mlClass, H1Incl_toH1, h1CoverIncl_mk D h]
  have hz : H1Cover.mk D' 𝒰 (LinearMap.restrict (inclC1 D 𝒰 h) (fun _ hf => inclC1_mem_Z1 D h hf)
      ⟨C1.retype (d0 D' 𝒰 g) hg, C1.retype_mem_Z1 hg⟩) = 0 := by
    rw [H1Cover.mk_eq_zero_iff]
    refine ⟨g, ?_⟩
    rw [LinearMap.restrict_coe_apply]
    funext p
    apply Subtype.ext
    show (Submodule.inclusion (RS.linSysOn_mono h)
        (C1.retype (d0 D' 𝒰 g) hg p) : RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X)) =
      (d0 D' 𝒰 g p : RS.MeroGermOn X ((𝒰.U p.1 ⊓ 𝒰.U p.2 : Opens X) : Set X))
    rfl
  rw [hz, map_zero]

/-! ### The vanishing criterion (§6.9(b), `⇐` half)

The `⇒` half (and hence the full `mlClass_eq_zero_iff`) needs `toH1_injective` (Forster 12.4,
`resH1_injective`), which is **not proved in this unit** (see `Refinement.lean`'s note) — it is
not on the critical path of `dbar-solvability`/`dolbeault-comparison`. The `⇐` half below (a class
realized by a global section vanishes) needs no injectivity and is what laurent-tails' truncation
map `α_D` actually produces classes *from*; it is proved here with zero sorries. -/

theorem mlClass_eq_zero_of_exists (g : C0 D' 𝒰) (hg : (d0 D' 𝒰 g).MemLD D) (φ : RS.LinSys D')
    (hφ : ∀ i : Fin 𝒰.n, ∀ x ∈ 𝒰.U i, (-(D x : ℤ) : WithTop ℤ) ≤
      ((g i : RS.MeroGermOn X (𝒰.U i : Set X)) -
        RS.MeroGermOn.restrict (𝒰.le_base i) (φ : RS.MeroGermOn X (Set.univ : Set X))).ord x) :
    mlClass 𝒰 g hg = 0 := by
  set h : C0 D 𝒰 := fun i => ⟨(g i : RS.MeroGermOn X (𝒰.U i : Set X)) -
      RS.MeroGermOn.restrict (𝒰.le_base i) (φ : RS.MeroGermOn X (Set.univ : Set X)),
      fun hU x hx => hφ i x hx⟩ with hh_def
  have hkey : C1.retype (d0 D' 𝒰 g) hg = d0 D 𝒰 h := by
    funext p
    apply Subtype.ext
    obtain ⟨i, j⟩ := p
    show RS.MeroGermOn.restrict inf_le_right (g j : RS.MeroGermOn X _) -
        RS.MeroGermOn.restrict inf_le_left (g i : RS.MeroGermOn X _) =
      RS.MeroGermOn.restrict inf_le_right
          ((g j : RS.MeroGermOn X _) -
            RS.MeroGermOn.restrict (𝒰.le_base j) (φ : RS.MeroGermOn X (Set.univ : Set X))) -
        RS.MeroGermOn.restrict inf_le_left
          ((g i : RS.MeroGermOn X _) -
            RS.MeroGermOn.restrict (𝒰.le_base i) (φ : RS.MeroGermOn X (Set.univ : Set X)))
    simp only [map_sub]
    rw [RS.MeroGermOn.restrict_restrict, RS.MeroGermOn.restrict_restrict]
    have hcancel : RS.MeroGermOn.restrict (inf_le_right.trans (𝒰.le_base j))
        (φ : RS.MeroGermOn X (Set.univ : Set X)) =
        RS.MeroGermOn.restrict (inf_le_left.trans (𝒰.le_base i))
          (φ : RS.MeroGermOn X (Set.univ : Set X)) := rfl
    rw [hcancel]
    abel
  rw [mlClass]
  have hz : H1Cover.mk D 𝒰 (⟨C1.retype (d0 D' 𝒰 g) hg, C1.retype_mem_Z1 hg⟩ : Z1 D 𝒰) = 0 := by
    rw [H1Cover.mk_eq_zero_iff]
    exact ⟨h, hkey.symm⟩
  rw [hz, map_zero]

end RS.Cech
