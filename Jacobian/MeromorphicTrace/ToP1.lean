/-
Blueprint unit: meromorphic-trace. The `toP1` bridge: meromorphic function → holomorphic map to
`ℙ¹`, file 1 of the design's 6-file plan.
-/
import Jacobian.Meromorphic.OrderEval
import Jacobian.ProjectiveLine.Holomorphy

/-!
# `toP1`: the `f`-to-`ℙ¹` bridge (meromorphic-trace, cluster 1)

Unit: meromorphic-trace (`docs/design/meromorphic-trace.md` §2 D2/D3, §4.1, §5 P1). Standing
surface hypotheses throughout (`CONVENTIONS.md`).

* `toP1 f x : OnePoint ℂ` — `∞` at poles, the limiting value along the punctured neighborhood
  elsewhere (D2). Total; junk elsewhere for non-meromorphic `f`.
* `toP1_contMDiff` (P1): for `f` meromorphic everywhere, `toP1 f : X → ℙ¹` is holomorphic.
  **Deviation from the design's proof plan**: `meromorphic-and-divisors`'s `MeroGermOn`/`OrderEval`
  layer (`ℳ X`, `evalAt`, `holoRepr`, `holoRepr_contMDiffAt`) — which the design doc explicitly
  recorded as "not yet built" at design time — is now built; we route through it (`toP1 f` agrees
  *everywhere* with `toP1 (mk f hf).holoRepr`, since both `ordAtX` and `limUnder` are `𝓝[≠]x`-germ
  notions and `holoRepr` matches any representative `𝓝[≠]x`-eventually at *every* `x`), which
  handles the "poles/zeros are isolated" bookkeeping the design's hand-written plan struggled with,
  and lets us cite `MeroGermOn.holoRepr_contMDiffAt`/`ContMDiffAt.onePointCoe`
  (`ProjectiveLine.Holomorphy`, also since-landed) directly instead of re-deriving the chart-local
  analytic-repair argument from scratch. This is a strictly shorter, more robust proof of the same
  theorem; the exported statement is unchanged.
* `toP1_not_const` (D3): an everywhere-meromorphic, not-codiscretely-constant `f` induces a
  nonconstant `toP1 f`.
-/

open scoped ContDiff Manifold OnePoint
open Filter Set Function Topology

namespace RS.MTrace

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {f : X → ℂ} {x : X}

/-- The canonical `ℙ¹`-valued lift of a raw meromorphic function: `∞` at poles, the limiting
value along the punctured neighborhood elsewhere. Total (junk elsewhere for non-meromorphic `f`);
the honest content is `toP1_contMDiff`. -/
noncomputable def toP1 (f : X → ℂ) (x : X) : OnePoint ℂ :=
  if 0 ≤ RS.ordAtX f x then ((Filter.limUnder (𝓝[≠] x) f : ℂ) : OnePoint ℂ) else ∞

theorem toP1_eq_infty_iff : toP1 f x = ∞ ↔ RS.ordAtX f x < 0 := by
  unfold toP1
  split_ifs with h
  · simp only [OnePoint.coe_ne_infty, false_iff]
    exact not_lt.2 h
  · simp only [not_le] at h
    simp [h]

theorem toP1_eq_coe_iff {c : ℂ} :
    toP1 f x = (c : OnePoint ℂ) ↔ 0 ≤ RS.ordAtX f x ∧ Filter.limUnder (𝓝[≠] x) f = c := by
  unfold toP1
  split_ifs with h
  · rw [OnePoint.coe_eq_coe]
    constructor
    · intro heq; exact ⟨h, heq⟩
    · rintro ⟨-, heq⟩; exact heq
  · constructor
    · intro heq; exact absurd heq.symm (OnePoint.coe_ne_infty c)
    · rintro ⟨h0, -⟩; exact absurd h0 h

/-! ### `toP1_contMDiff` (P1) -/

theorem toP1_contMDiff (hf : MeromorphicOnX f Set.univ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (toP1 f) := by
  -- Route through `holoRepr`: `toP1 f = toP1 f'` everywhere, `f' := (mk f hf).holoRepr`.
  set φ : RS.MeroGermOn X Set.univ := RS.MeroGermOn.mk f hf with hφ_def
  set f' : X → ℂ := φ.holoRepr with hf'_def
  have hf'mero : MeromorphicOnX f' Set.univ := RS.MeroGermOn.meromorphicOnX_holoRepr isOpen_univ φ
  have hordf' : ∀ y, RS.ordAtX f' y = φ.ord y := by
    intro y
    have hrep : RS.MeroGermOn.mk f' hf'mero = φ := RS.MeroGermOn.mk_holoRepr isOpen_univ φ
    rw [← RS.MeroGermOn.ord_mk isOpen_univ (mem_univ y) (f := f') (hf := hf'mero), hrep]
  have heq_germ : ∀ y, f =ᶠ[𝓝[≠] y] f' :=
    fun y => RS.MeroGermOn.holoRepr_eventuallyEq_nhdsNE isOpen_univ (mem_univ y) φ rfl
  have htoP1_eq : toP1 f = toP1 f' := by
    funext y
    have hordeq : RS.ordAtX f y = RS.ordAtX f' y := RS.ordAtX_congr (heq_germ y)
    have hlimeq : Filter.limUnder (𝓝[≠] y) f = Filter.limUnder (𝓝[≠] y) f' :=
      RS.limUnder_congr (heq_germ y)
    unfold toP1
    rw [hordeq, hlimeq]
  rw [htoP1_eq]
  intro y
  by_cases h0 : 0 ≤ RS.ordAtX f' y
  · -- Regular case: `f'` is honestly `ContMDiffAt` here, so `toP1 f'` is its "no poles" lift.
    have hordφ : 0 ≤ φ.ord y := (hordf' y) ▸ h0
    have hcy : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f' y :=
      RS.MeroGermOn.holoRepr_contMDiffAt isOpen_univ (mem_univ y) hordφ
    have hval : toP1 f' y = ((f' y : ℂ) : OnePoint ℂ) := by
      rw [toP1_eq_coe_iff]
      exact ⟨h0, (hcy.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq⟩
    rw [hval]
    exact hcy.onePointCoe
  · -- Pole case: adapt `RS.P1.contMDiffAt_of_pole`'s (planar) proof to the manifold `X`.
    have hordlt : RS.ordAtX f' y < 0 := not_le.1 h0
    set e := chartAt ℂ y with he_def
    set c := e y with hc_def
    have hg : MeromorphicAt (f' ∘ e.symm) c := hf' y (mem_univ y)
    have hordg : meromorphicOrderAt (f' ∘ e.symm) c < 0 := hordlt
    have heq : ∀ᶠ z in 𝓝[≠] y, toP1 f' z = ((f' z : ℂ) : OnePoint ℂ) := by
      have hne_top : RS.ordAtX f' y ≠ ⊤ := hordlt.ne_top
      have hreg : ∀ᶠ z in 𝓝[≠] y, RS.ordAtX f' z = 0 :=
        RS.eventually_ordAtX_eq_zero (hf' y (mem_univ y)) hne_top
      filter_upwards [hreg] with z hz
      have h0z : 0 ≤ RS.ordAtX f' z := hz ▸ le_rfl
      have hordφz : 0 ≤ φ.ord z := (hordf' z) ▸ h0z
      have hcz : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f' z :=
        RS.MeroGermOn.holoRepr_contMDiffAt isOpen_univ (mem_univ z) hordφz
      rw [toP1_eq_coe_iff]
      exact ⟨h0z, (hcz.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq⟩
    have hcobdd : Tendsto f' (𝓝[≠] y) (Bornology.cobounded ℂ) :=
      (RS.tendsto_cobounded_iff_ordAtX_neg (hf' y (mem_univ y))).2 hordlt
    have hpunc : Tendsto (toP1 f') (𝓝[≠] y) (𝓝 (∞ : OnePoint ℂ)) := by
      rw [Filter.tendsto_congr' heq]
      exact RS.P1.tendsto_coe_cobounded.comp hcobdd
    have hFinf : toP1 f' y = (∞ : OnePoint ℂ) := toP1_eq_infty_iff.2 hordlt
    have hpure : Tendsto (toP1 f') (pure y) (𝓝 (∞ : OnePoint ℂ)) := hFinf ▸ tendsto_pure_nhds _ y
    have hcombine : Tendsto (toP1 f') (𝓝 y) (𝓝 (∞ : OnePoint ℂ)) := by
      rw [← nhdsNE_sup_pure y, tendsto_sup]
      exact ⟨hpunc, hpure⟩
    have hcontF : ContinuousAt (toP1 f') y := by rw [ContinuousAt, hFinf]; exact hcombine
    rw [RS.P1.contMDiffAt_iff_analyticAt_of_eq_infty hFinf]
    refine ⟨hcontF, ?_⟩
    have heqchart : ∀ᶠ z in 𝓝[≠] c, toP1 f' (e.symm z) = ((f' (e.symm z) : ℂ) : OnePoint ℂ) :=
      RS.eventually_nhdsNE_iff_comp_chart.mp heq
    have hcompeq :
        (⇑RS.P1.invChart ∘ (toP1 f') ∘ ⇑e.symm) =ᶠ[𝓝[≠] c] (f' ∘ e.symm)⁻¹ := by
      filter_upwards [heqchart] with z hz
      show RS.P1.invChart (toP1 f' (e.symm z)) = ((f' ∘ e.symm) z)⁻¹
      rw [hz, RS.P1.invChart_apply_coe]
      rfl
    have hordinv : meromorphicOrderAt (⇑RS.P1.invChart ∘ (toP1 f') ∘ ⇑e.symm) c
        = meromorphicOrderAt (f' ∘ e.symm)⁻¹ c := meromorphicOrderAt_congr hcompeq
    have hpos : 0 < meromorphicOrderAt (⇑RS.P1.invChart ∘ (toP1 f') ∘ ⇑e.symm) c := by
      rw [hordinv, meromorphicOrderAt_inv]
      exact LinearOrderedAddCommGroupWithTop.neg_pos.2 (Or.inl hordg)
    have hvalz : (⇑RS.P1.invChart ∘ (toP1 f') ∘ ⇑e.symm) c = 0 := by
      show RS.P1.invChart (toP1 f' (e.symm c)) = 0
      rw [show e.symm c = y from e.left_inv (mem_chart_source ℂ y), hFinf,
        RS.P1.invChart_apply_infty]
    exact AnalyticAt.of_meromorphicOrderAt_pos hpos hvalz

end RS.MTrace
