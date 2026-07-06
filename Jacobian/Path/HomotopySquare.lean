import Jacobian.Path.Continuation

/-!
# Homotopy invariance: the 2D grid argument (CC6)

Unit: paths-and-integrals (`docs/design/paths-and-integrals.md` §5). A primitive of `η` along a
continuous homotopy square exists (hand-rolled grid via mathlib's 2D Lebesgue-number lemma
`exists_monotone_Icc_subset_open_cover_unitInterval_prod_self`), subsuming both rel-endpoint and
free-loop homotopy invariance of `pathIntegral`.

Main declarations:
* `RS.gridK H` — the clamped map `ℝ × ℝ → X` associated to `H : C(I × I, X)`.
* `RS.GridChain H`, `RS.exists_gridChain` — the 2D chart-ball subdivision.
* `RS.exists_primitive_along_square` — existence of a primitive along the (clamped) square.
* `RS.pathIntegral_congr_homotopic`, `RS.pathIntegralQ`, `RS.pathIntegral_congr_freeHomotopic`,
  `RS.pathIntegral_eq_of_simplyConnected`, `RS.period_eq_zero_of_homotopic_refl`.
-/

open scoped ContDiff Manifold Topology unitInterval
open IsManifold Metric Set Filter

noncomputable section

namespace RS

open scoped Classical

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {x y z : X}

/-! ### The clamped map of a homotopy square -/

/-- The map `ℝ × ℝ → X` obtained by clamping both coordinates of `H : C(I × I, X)` into `[0,1]`. -/
def gridK (H : C(↥unitInterval × ↥unitInterval, X)) (p : ℝ × ℝ) : X :=
  H (projIcc 0 1 zero_le_one p.1, projIcc 0 1 zero_le_one p.2)

theorem continuous_gridK (H : C(↥unitInterval × ↥unitInterval, X)) : Continuous (gridK H) :=
  H.continuous.comp ((continuous_projIcc.comp continuous_fst).prodMk
    (continuous_projIcc.comp continuous_snd))

/-! ### The 2D chart-ball subdivision -/

/-- A grid subdivision of `[0,1]²` with chart-and-ball data adapted to `H`: on each cell
`Icc (t j) (t (j+1)) ×ˢ Icc (t k) (t (k+1))`, `gridK H` stays inside a single chart-ball. -/
structure GridChain (H : C(↥unitInterval × ↥unitInterval, X)) where
  m : ℕ
  t : ℕ → ℝ
  ht0 : t 0 = 0
  ht1 : ∀ k, m ≤ k → t k = 1
  mono : Monotone t
  e : ℕ → ℕ → OpenPartialHomeomorph X ℂ
  he : ∀ j k, e j k ∈ maximalAtlas 𝓘(ℂ) ω X
  c : ℕ → ℕ → ℂ
  r : ℕ → ℕ → ℝ
  hr : ∀ j k, 0 < r j k
  ball_subset : ∀ j k, ball (c j k) (r j k) ⊆ (e j k).target
  maps : ∀ j k, ∀ p ∈ Icc (t j) (t (j+1)) ×ˢ Icc (t k) (t (k+1)),
    gridK H p ∈ (e j k).source ∧ e j k (gridK H p) ∈ ball (c j k) (r j k)

private theorem exists_chart_nhds2 (H : C(↥unitInterval × ↥unitInterval, X))
    (p : ↥unitInterval × ↥unitInterval) :
    ∃ V : Set (↥unitInterval × ↥unitInterval), IsOpen V ∧ p ∈ V ∧
      ∃ (e : OpenPartialHomeomorph X ℂ) (c : ℂ) (r : ℝ), e ∈ maximalAtlas 𝓘(ℂ) ω X ∧ 0 < r ∧
        ball c r ⊆ e.target ∧ ∀ q ∈ V, H q ∈ e.source ∧ e (H q) ∈ ball c r := by
  set eτ : OpenPartialHomeomorph X ℂ := chartAt ℂ (H p) with heτ_def
  obtain ⟨rτ, hrτ, hballτ⟩ := Metric.isOpen_iff.mp eτ.open_target (eτ (H p))
    (mem_chart_target ℂ (H p))
  set U : Set X := eτ.source ∩ eτ ⁻¹' (ball (eτ (H p)) rτ) with hU_def
  have hUopen : IsOpen U := eτ.isOpen_inter_preimage isOpen_ball
  set V : Set (↥unitInterval × ↥unitInterval) := H ⁻¹' U with hV_def
  have hVopen : IsOpen V := H.continuous.isOpen_preimage U hUopen
  have hpV : p ∈ V := ⟨mem_chart_source ℂ (H p), mem_ball_self hrτ⟩
  exact ⟨V, hVopen, hpV, eτ, eτ (H p), rτ, chart_mem_maximalAtlas _, hrτ, hballτ, fun q hq => hq⟩

theorem exists_gridChain (H : C(↥unitInterval × ↥unitInterval, X)) : Nonempty (GridChain H) := by
  choose V hVopen hpV e c r he hr hballsub hmaps using exists_chart_nhds2 H
  obtain ⟨t, ht0, hmono, ⟨m, htm⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self hVopen
      (fun p _ => mem_iUnion.2 ⟨p, hpV p⟩)
  choose iOf hiOf using hsub
  refine ⟨⟨m, fun k => (t k : ℝ), by simp [ht0], ?_, ?_, fun j k => e (iOf j k),
    fun j k => he (iOf j k), fun j k => c (iOf j k), fun j k => r (iOf j k),
    fun j k => hr (iOf j k), fun j k => hballsub (iOf j k), ?_⟩⟩
  · intro k hk; simp [htm k hk]
  · intro a b hab; exact hmono hab
  · intro j k p hp
    obtain ⟨hp1, hp2⟩ := hp
    have hp1' : (t j : ℝ) ≤ p.1 ∧ p.1 ≤ (t (j+1) : ℝ) := hp1
    have hp2' : (t k : ℝ) ≤ p.2 ∧ p.2 ≤ (t (k+1) : ℝ) := hp2
    have hu1 : p.1 ∈ (unitInterval : Set ℝ) :=
      ⟨(t j).2.1.trans hp1'.1, hp1'.2.trans (t (j+1)).2.2⟩
    have hu2 : p.2 ∈ (unitInterval : Set ℝ) :=
      ⟨(t k).2.1.trans hp2'.1, hp2'.2.trans (t (k+1)).2.2⟩
    have hmem : ((⟨p.1, hu1⟩ : ↥unitInterval), (⟨p.2, hu2⟩ : ↥unitInterval)) ∈
        Icc (t j) (t (j+1)) ×ˢ Icc (t k) (t (k+1)) := ⟨hp1', hp2'⟩
    have hres := hmaps (iOf j k) _ (hiOf j k hmem)
    have hgeq : gridK H p = H (⟨p.1, hu1⟩, ⟨p.2, hu2⟩) := by
      show H (projIcc 0 1 zero_le_one p.1, projIcc 0 1 zero_le_one p.2) = _
      rw [projIcc_of_mem zero_le_one hu1, projIcc_of_mem zero_le_one hu2]
    rw [hgeq]; exact hres

/-! ### Product `hcov`/preconnectedness helpers (the only genuinely new bookkeeping vs 1D) -/

/-- Adjacent horizontal strips `A ×ˢ Icc l c`, `A ×ˢ Icc c d` (fixed first factor, split
second coordinate): the `hcov` discharger for gluing along a row. -/
private theorem hcov_prod_snd {A : Set ℝ} {l c d : ℝ} (hlc : l ≤ c) (hcd : c ≤ d) :
    ∀ p : ℝ × ℝ, p ∈ A ×ˢ Icc l c ∪ A ×ˢ Icc c d →
      A ×ˢ Icc l c ∈ 𝓝[A ×ˢ Icc l c ∪ A ×ˢ Icc c d] p ∨
      A ×ˢ Icc c d ∈ 𝓝[A ×ˢ Icc l c ∪ A ×ˢ Icc c d] p ∨
      p ∈ (A ×ˢ Icc l c) ∩ (A ×ˢ Icc c d) := by
  intro p hp
  have hpA : p.1 ∈ A := hp.elim (fun h => h.1) (fun h => h.1)
  rcases lt_trichotomy p.2 c with hac | hac | hac
  · refine Or.inl ?_
    rw [mem_nhdsWithin]
    refine ⟨Set.univ ×ˢ Iio c, isOpen_univ.prod isOpen_Iio, ⟨trivial, hac⟩, ?_⟩
    rintro w ⟨hw1, hw2⟩
    rcases hw2 with hw2 | hw2
    · exact hw2
    · exact absurd hw2.2.1 (not_le.mpr hw1.2)
  · exact Or.inr (Or.inr ⟨⟨hpA, hlc.trans_eq hac.symm, hac.le⟩, ⟨hpA, hac.ge, hac.le.trans hcd⟩⟩)
  · refine Or.inr (Or.inl ?_)
    rw [mem_nhdsWithin]
    refine ⟨Set.univ ×ˢ Ioi c, isOpen_univ.prod isOpen_Ioi, ⟨trivial, hac⟩, ?_⟩
    rintro w ⟨hw1, hw2⟩
    rcases hw2 with hw2 | hw2
    · exact absurd hw2.2.2 (not_le.mpr hw1.2)
    · exact hw2

/-- Adjacent vertical strips `Icc l c ×ˢ B`, `Icc c d ×ˢ B` (fixed second factor, split first
coordinate): the `hcov` discharger for stacking rows. -/
private theorem hcov_prod_fst {B : Set ℝ} {l c d : ℝ} (hlc : l ≤ c) (hcd : c ≤ d) :
    ∀ p : ℝ × ℝ, p ∈ Icc l c ×ˢ B ∪ Icc c d ×ˢ B →
      Icc l c ×ˢ B ∈ 𝓝[Icc l c ×ˢ B ∪ Icc c d ×ˢ B] p ∨
      Icc c d ×ˢ B ∈ 𝓝[Icc l c ×ˢ B ∪ Icc c d ×ˢ B] p ∨
      p ∈ (Icc l c ×ˢ B) ∩ (Icc c d ×ˢ B) := by
  intro p hp
  have hpB : p.2 ∈ B := hp.elim (fun h => h.2) (fun h => h.2)
  rcases lt_trichotomy p.1 c with hac | hac | hac
  · refine Or.inl ?_
    rw [mem_nhdsWithin]
    refine ⟨Iio c ×ˢ Set.univ, isOpen_Iio.prod isOpen_univ, ⟨hac, trivial⟩, ?_⟩
    rintro w ⟨hw1, hw2⟩
    rcases hw2 with hw2 | hw2
    · exact hw2
    · exact absurd hw2.1.1 (not_le.mpr hw1.1)
  · exact Or.inr (Or.inr ⟨⟨⟨hlc.trans_eq hac.symm, hac.le⟩, hpB⟩, ⟨hac.ge, hac.le.trans hcd⟩, hpB⟩)
  · refine Or.inr (Or.inl ?_)
    rw [mem_nhdsWithin]
    refine ⟨Ioi c ×ˢ Set.univ, isOpen_Ioi.prod isOpen_univ, ⟨hac, trivial⟩, ?_⟩
    rintro w ⟨hw1, hw2⟩
    rcases hw2 with hw2 | hw2
    · exact absurd hw2.1.2 (not_le.mpr hw1.1)
    · exact hw2

private theorem isPreconnected_prod_snd_inter {A : Set ℝ} (hA : IsPreconnected A) {l c d : ℝ}
    (hlc : l ≤ c) (hcd : c ≤ d) : IsPreconnected ((A ×ˢ Icc l c) ∩ (A ×ˢ Icc c d)) := by
  have heq : (A ×ˢ Icc l c) ∩ (A ×ˢ Icc c d) = A ×ˢ ({c} : Set ℝ) := by
    rw [Set.prod_inter_prod, Set.inter_self, Icc_inter_Icc, sup_eq_right.mpr hlc,
      inf_eq_left.mpr hcd, Icc_self]
  rw [heq]
  exact hA.prod isPreconnected_singleton

private theorem isPreconnected_prod_fst_inter {B : Set ℝ} (hB : IsPreconnected B) {l c d : ℝ}
    (hlc : l ≤ c) (hcd : c ≤ d) : IsPreconnected ((Icc l c ×ˢ B) ∩ (Icc c d ×ˢ B)) := by
  have heq : (Icc l c ×ˢ B) ∩ (Icc c d ×ˢ B) = ({c} : Set ℝ) ×ˢ B := by
    rw [Set.prod_inter_prod, Set.inter_self, Icc_inter_Icc, sup_eq_right.mpr hlc,
      inf_eq_left.mpr hcd, Icc_self]
  rw [heq]
  exact isPreconnected_singleton.prod hB

/-! ### Row assembly (inner induction) -/

/-- Row assembly: for fixed `j`, a primitive on `Icc (t j) (t (j+1)) ×ˢ Icc 0 (t k)`, normalized
at the bottom-left corner. -/
private theorem exists_row {H : C(↥unitInterval × ↥unitInterval, X)} (C : GridChain H)
    (η : Form1 X) (j : ℕ) : ∀ k : ℕ, ∃ F : ℝ × ℝ → ℂ,
      IsPrimitiveAlongMap (gridK H) η F (Icc (C.t j) (C.t (j+1)) ×ˢ Icc 0 (C.t k)) ∧
        F (C.t j, 0) = 0 := by
  have hjmem : C.t j ∈ Icc (C.t j) (C.t (j+1)) := left_mem_Icc.mpr (C.mono (Nat.le_succ j))
  intro k
  induction k with
  | zero =>
    have h0mem : (0:ℝ) ∈ Icc (C.t 0) (C.t 1) := ⟨C.ht0.le, C.ht0 ▸ C.mono (Nat.zero_le 1)⟩
    have hz0mem : (C.e j 0) (gridK H (C.t j, 0)) ∈ ball (C.c j 0) (C.r j 0) :=
      (C.maps j 0 (C.t j, 0) ⟨hjmem, h0mem⟩).2
    obtain ⟨g, hg0, hg⟩ := exists_hasDerivAt_ball (η.analyticOnNhd_coeffIn (C.he j 0))
      (C.ball_subset j 0) hz0mem (w := 0)
    refine ⟨fun p => g (C.e j 0 (gridK H p)), ?_, hg0⟩
    apply isPrimitiveAlongMap_of_ball (C.he j 0) hg
    intro p hp
    apply C.maps j 0 p
    exact ⟨hp.1, C.ht0.le.trans hp.2.1, hp.2.2.trans (C.mono (Nat.zero_le 1))⟩
  | succ k ih =>
    obtain ⟨F, hF, hF0⟩ := ih
    obtain ⟨g, _, hg⟩ := exists_hasDerivAt_ball (c := C.c j k) (r := C.r j k) (z₀ := C.c j k)
      (w := 0) (η.analyticOnNhd_coeffIn (C.he j k)) (C.ball_subset j k) (mem_ball_self (C.hr j k))
    have hG : IsPrimitiveAlongMap (gridK H) η (fun p => g (C.e j k (gridK H p)))
        (Icc (C.t j) (C.t (j+1)) ×ˢ Icc (C.t k) (C.t (k+1))) :=
      isPrimitiveAlongMap_of_ball (C.he j k) hg (C.maps j k)
    have hG' : IsPrimitiveAlongMap (gridK H) η (fun p => g (C.e j k (gridK H p)) +
        (F (C.t j, C.t k) - g (C.e j k (gridK H (C.t j, C.t k)))))
        (Icc (C.t j) (C.t (j+1)) ×ˢ Icc (C.t k) (C.t (k+1))) := hG.add_const _
    have hval : F (C.t j, C.t k) = g (C.e j k (gridK H (C.t j, C.t k))) +
        (F (C.t j, C.t k) - g (C.e j k (gridK H (C.t j, C.t k)))) := by ring
    have h0k : (0:ℝ) ≤ C.t k := C.ht0 ▸ C.mono (Nat.zero_le k)
    have hmonok : C.t k ≤ C.t (k+1) := C.mono (Nat.le_succ k)
    have hjA : IsPreconnected (Icc (C.t j) (C.t (j+1)) : Set ℝ) := isPreconnected_Icc
    have hcont : ContinuousOn (gridK H) (Icc (C.t j) (C.t (j+1)) ×ˢ Icc 0 (C.t k) ∪
        Icc (C.t j) (C.t (j+1)) ×ˢ Icc (C.t k) (C.t (k+1))) := (continuous_gridK H).continuousOn
    have hL := isPreconnected_prod_snd_inter hjA h0k hmonok
    have ha0 : (C.t j, C.t k) ∈ (Icc (C.t j) (C.t (j+1)) ×ˢ Icc 0 (C.t k)) ∩
        (Icc (C.t j) (C.t (j+1)) ×ˢ Icc (C.t k) (C.t (k+1))) :=
      ⟨⟨hjmem, h0k, le_rfl⟩, ⟨hjmem, le_rfl, hmonok⟩⟩
    have hcov := hcov_prod_snd (A := Icc (C.t j) (C.t (j+1))) h0k hmonok
    have hglue := hF.glue hcont hG' hL ha0 hval hcov
    rw [← Set.prod_union, Icc_union_Icc_eq_Icc h0k hmonok] at hglue
    refine ⟨_, hglue, ?_⟩
    have h0mem : (0:ℝ) ∈ Icc (0:ℝ) (C.t k) := ⟨le_rfl, h0k⟩
    rw [Set.piecewise_eq_of_mem (Icc (C.t j) (C.t (j+1)) ×ˢ Icc 0 (C.t k)) F
      (fun p => g (C.e j k (gridK H p)) +
        (F (C.t j, C.t k) - g (C.e j k (gridK H (C.t j, C.t k))))) ⟨hjmem, h0mem⟩]
    exact hF0

end RS

end
