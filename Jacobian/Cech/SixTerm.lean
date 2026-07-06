import Jacobian.Cech.Skyscraper

/-!
# The six-term skyscraper fragment: `H1Incl_surjective` (CC8, D7, proof plan §6.9(g))

Unit: cech-cohomology (`docs/design/cech-cohomology.md` §4.7, §6.9(g)).

* `C1.retype_mem_Z1'`: the general (non-coboundary) retype-preserves-`Z1` fact.
* `h1CoverIncl_mk_retype`: the `D`-inclusion of a retyped `Z1 D 𝒰` class recovers the original
  `Z1 D' 𝒰` class.
* `memLD_of_isAdapted`: on a cover adapted to `diffSupp D D'`, every `Z1 D' 𝒰`-cocycle already
  satisfies the (smaller) `D`-bound — diagonal components vanish to order `⊤`
  (`Z1.ord_diag`), off-diagonal components avoid the finite set where `D ≠ D'`
  (`FinCover.IsAdapted.not_mem_inf`), so `D = D'` pointwise there.
* `H1Incl_surjective`: **no `H²`, no long exact sequence, no snake lemma** — every class of
  `H1 D'` is already represented, on a suitably adapted cover, by a genuine `Z1 D`-cocycle.

**Recorded as interface, not proved here** (see `Skyscraper.lean`'s file-end note): the
`windowConnect` connecting map, `exists_realization`, Lemma A, and the two exactness statements
`exact_windowMap_windowConnect`/`exact_windowConnect_H1Incl` — these need the adapted-cover
*realization* machinery (§6.9(c)-(f)), which did not fit this unit's remaining time budget.
-/

open scoped ContDiff Manifold
open Set TopologicalSpace RS.Cech

namespace RS.Cech

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Ω : Opens X} {𝒰 : FinCover Ω} {D D' : RS.Divisor X}

/-- General (non-coboundary) version of `C1.retype_mem_Z1`: retyping a `Z1 D'`-cocycle whose
components all satisfy the `D`-bound gives a `Z1 D`-cocycle. -/
theorem C1.retype_mem_Z1' {f : C1 D' 𝒰} (hf : f ∈ Z1 D' 𝒰) (hmem : f.MemLD D) :
    C1.retype f hmem ∈ Z1 D 𝒰 := by
  rw [mem_Z1_iff]
  intro t
  apply Subtype.ext
  have hcoe : (d1 D 𝒰 (C1.retype f hmem) t :
      RS.MeroGermOn X ((𝒰.U t.1 ⊓ 𝒰.U t.2.1 ⊓ 𝒰.U t.2.2 : Opens X) : Set X)) =
      (d1 D' 𝒰 f t :
      RS.MeroGermOn X ((𝒰.U t.1 ⊓ 𝒰.U t.2.1 ⊓ 𝒰.U t.2.2 : Opens X) : Set X)) := rfl
  rw [hcoe, (mem_Z1_iff D' 𝒰 f).1 hf t]
  simp

/-- The `D`-inclusion of a retyped `Z1 D 𝒰` class recovers the original `Z1 D' 𝒰` class. -/
theorem h1CoverIncl_mk_retype (h : D ≤ D') {f : C1 D' 𝒰} (hf : f ∈ Z1 D' 𝒰) (hmem : f.MemLD D) :
    h1CoverIncl D 𝒰 h (H1Cover.mk D 𝒰 ⟨C1.retype f hmem, C1.retype_mem_Z1' hf hmem⟩) =
      H1Cover.mk D' 𝒰 ⟨f, hf⟩ := by
  rw [h1CoverIncl_mk]
  congr 1

variable [T2Space X] [CompactSpace X]

/-- On a cover adapted to `diffSupp D D'`, every `Z1 D'`-cocycle already satisfies the `D`-bound
componentwise: diagonal components vanish to order `⊤`, off-diagonal components avoid the finite
set where `D ≠ D'` (adaptedness), hence `D = D'` there and the `D'`-bound *is* the `D`-bound. -/
theorem memLD_of_isAdapted {𝒲 : FinCover (⊤ : Opens X)} (hadapt : 𝒲.IsAdapted (diffSupp D D'))
    {f : C1 D' 𝒲} (hf : f ∈ Z1 D' 𝒲) : f.MemLD D := by
  rintro ⟨i, j⟩
  by_cases hij : i = j
  · subst hij
    rw [RS.mem_linSysOn_iff_of_isOpen (𝒲.U i ⊓ 𝒲.U i).isOpen]
    intro x hx
    rw [Z1.ord_diag D' 𝒲 hf i hx]
    exact le_top
  · rw [RS.mem_linSysOn_iff_of_isOpen (𝒲.U i ⊓ 𝒲.U j).isOpen]
    intro x hx
    have hxDeq : D x = D' x := by
      by_contra hne
      exact hadapt.not_mem_inf (mem_diffSupp_iff.2 hne) hij hx
    have hbound := (RS.mem_linSysOn_iff_of_isOpen (𝒲.U i ⊓ 𝒲.U j).isOpen).1 (f (i, j)).2 x hx
    rwa [hxDeq]

-- **The six-term fragment, part (g)**: `H1Incl` is surjective — no `H²`, no long exact
-- sequence, no snake lemma anywhere. Every class of `H1 D'` is already, on a cover adapted to
-- `diffSupp D D'`, represented by a genuine `Z1 D`-cocycle (retyping across the finite set where
-- `D ≠ D'` costs nothing since cocycles vanish there anyway).
set_option maxHeartbeats 1000000 in
theorem H1Incl_surjective (h : D ≤ D') : Function.Surjective (H1Incl D h) := by
  intro ξ'
  obtain ⟨𝒰₀, f'c, hf'c⟩ := exists_rep D' ξ'
  obtain ⟨f', hf'⟩ := H1Cover.mk_surjective D' 𝒰₀ f'c
  obtain ⟨𝒲, hle, hadapt, -⟩ := exists_adapted_refinement 𝒰₀ (diffSupp D D')
    (fun _ _ => trivial) (fun _ => ⊤) (fun _ _ => trivial)
  set τ := chosenRefIdx hle with hτ_def
  have hτspec := chosenRefIdx_spec hle
  set g' := resZ1 D' τ hτspec f' with hg'_def
  have hgmem : (g' : C1 D' 𝒲) ∈ Z1 D' 𝒲 := g'.2
  have hmemld : (g' : C1 D' 𝒲).MemLD D := memLD_of_isAdapted hadapt hgmem
  refine ⟨toH1 D 𝒲 (H1Cover.mk D 𝒲 ⟨C1.retype (g' : C1 D' 𝒲) hmemld,
    C1.retype_mem_Z1' hgmem hmemld⟩), ?_⟩
  rw [H1Incl_toH1, h1CoverIncl_mk_retype h hgmem hmemld]
  show toH1 D' 𝒲 (H1Cover.mk D' 𝒲 (resZ1 D' τ hτspec f')) = ξ'
  rw [← resH1_mk, hf', toH1_resH1 D' τ hτspec, hf'c]

end RS.Cech
