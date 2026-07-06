import Jacobian.Path.Chain

/-!
# Perturbing a path off a finite set (CC6)

Unit: paths-and-integrals (`docs/design/paths-and-integrals.md` §7). Every path with endpoints
off a finite set `S` is homotopic (rel endpoints) to one whose whole range avoids `S`.

Main declarations:
* `RS.nonempty_open_diff_finite` — a nonempty open subset of a manifold minus a finite set is
  still nonempty.
* `RS.exists_homotopic_avoiding_of_ball` — the single-chart-ball base case (planar avoidance
  transported through the chart).
-/

open scoped ContDiff Manifold Topology unitInterval
open IsManifold Metric Set Filter

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {x y z : X}

omit [IsManifold 𝓘(ℂ) ω X] in
/-- A nonempty open subset of `X` minus a finite set is still nonempty (through a chart,
`ℂ`-minus-countable-is-dense). -/
theorem nonempty_open_diff_finite {U : Set X} (hU : IsOpen U) (hne : U.Nonempty)
    {S : Set X} (hS : S.Finite) : (U \ S).Nonempty := by
  obtain ⟨p, hp⟩ := hne
  set e := chartAt ℂ p with he_def
  have hUop : IsOpen (e '' (U ∩ e.source)) :=
    e.isOpen_image_of_subset_source (hU.inter e.open_source) inter_subset_right
  have hUne : (e '' (U ∩ e.source)).Nonempty := ⟨e p, p, ⟨hp, mem_chart_source ℂ p⟩, rfl⟩
  have hTcount : (e '' (S ∩ e.source)).Countable :=
    ((hS.inter_of_left e.source).image e).countable
  obtain ⟨z, hzT, hzU⟩ := (hTcount.dense_compl ℝ).exists_mem_open hUop hUne
  obtain ⟨q, ⟨hqU, hqsrc⟩, rfl⟩ := hzU
  refine ⟨q, hqU, ?_⟩
  intro hqS
  exact hzT ⟨q, ⟨hqS, hqsrc⟩, rfl⟩

/-- Base case: a path lying entirely inside one chart-ball `(e, ball c r)`, with endpoints off a
finite set `S`, is homotopic rel endpoints to a path whose range avoids `S` entirely. -/
theorem exists_homotopic_avoiding_of_ball {a b : X} (γ : Path a b)
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ maximalAtlas 𝓘(ℂ) ω X)
    {c : ℂ} {r : ℝ} (hballsub : ball c r ⊆ e.target)
    (hγsrc : range ⇑γ ⊆ e.source) (hγball : ∀ t : ↥unitInterval, e (γ t) ∈ ball c r)
    {S : Set X} (hS : S.Finite) (ha : a ∉ S) (hb : b ∉ S) :
    ∃ γ' : Path a b, γ.Homotopic γ' ∧ Disjoint (Set.range ⇑γ') S := by
  have haSrc : a ∈ e.source := hγsrc γ.source_mem_range
  have hbSrc : b ∈ e.source := hγsrc γ.target_mem_range
  have haeq : e.symm (e a) = a := e.left_inv haSrc
  have hbeq : e.symm (e b) = b := e.left_inv hbSrc
  have hcontE : ContinuousOn e (range ⇑γ) := e.continuousOn.mono hγsrc
  set p : Path (e a) (e b) := γ.map' hcontE with hp_def
  have hprange : ∀ t : ↥unitInterval, p t ∈ ball c r := hγball
  have heaB : e a ∈ ball c r := by have := hprange 0; rwa [p.source] at this
  have hebB : e b ∈ ball c r := by have := hprange 1; rwa [p.target] at this
  set T : Set ℂ := e '' (S ∩ e.source) with hT_def
  have hTcount : T.Countable := ((hS.inter_of_left e.source).image e).countable
  have heaT : e a ∉ T := by
    rintro ⟨w, ⟨hwS, hwsrc⟩, hwe⟩
    apply ha
    have : w = a := by rw [← e.left_inv hwsrc, hwe]; exact haeq
    rwa [this] at hwS
  have hebT : e b ∉ T := by
    rintro ⟨w, ⟨hwS, hwsrc⟩, hwe⟩
    apply hb
    have : w = b := by rw [← e.left_inv hwsrc, hwe]; exact hbeq
    rwa [this] at hwS
  have hpc := Convex.isPathConnected_diff_countable (convex_ball c r) isOpen_ball
    ⟨e a, heaB⟩ hTcount
  have hjoin : JoinedIn (ball c r \ T) (e a) (e b) :=
    hpc.joinedIn (e a) ⟨heaB, heaT⟩ (e b) ⟨hebB, hebT⟩
  set q : Path (e a) (e b) := hjoin.somePath with hq_def
  have hqmem : ∀ t, q t ∈ ball c r \ T := hjoin.somePath_mem
  have hpB : range ⇑p ⊆ ball c r := by rintro z ⟨t, rfl⟩; exact hprange t
  have hqB : range ⇑q ⊆ ball c r := by rintro z ⟨t, rfl⟩; exact (hqmem t).1
  obtain ⟨Hpq, hHrange⟩ := exists_homotopy_range_subset_of_convex (convex_ball c r) hpB hqB
  have hHcont : Continuous (fun z : ↥unitInterval × ↥unitInterval => e.symm (Hpq z)) :=
    e.continuousOn_symm.comp_continuous Hpq.continuous (fun z => hballsub (hHrange z))
  have hH0 : ∀ t : ↥unitInterval, e.symm (Hpq (t, 0)) = a := fun t => by
    rw [Hpq.source]; exact haeq
  have hH1 : ∀ t : ↥unitInterval, e.symm (Hpq (t, 1)) = b := fun t => by
    rw [Hpq.target]; exact hbeq
  have hHzero : ∀ u : ↥unitInterval, e.symm (Hpq (0, u)) = γ u := fun u => by
    have h1 : (Hpq.eval 0) u = Hpq (0, u) := rfl
    rw [Hpq.eval_zero] at h1
    rw [← h1]
    show e.symm (e (γ u)) = γ u
    exact e.left_inv (hγsrc (mem_range_self u))
  have hHone : ∀ u : ↥unitInterval, e.symm (Hpq (1, u)) = e.symm (q u) := fun u => by
    have h1 : (Hpq.eval 1) u = Hpq (1, u) := rfl
    rw [Hpq.eval_one] at h1
    rw [← h1]
  have hqcontS : ContinuousOn e.symm (range ⇑q) := e.continuousOn_symm.mono (hqB.trans hballsub)
  set γ'' : Path a b :=
    ⟨⟨fun u => e.symm (q u),
        hqcontS.comp_continuous q.continuous (fun u => mem_range_self u)⟩,
      by show e.symm (q 0) = a; rw [q.source]; exact haeq,
      by show e.symm (q 1) = b; rw [q.target]; exact hbeq⟩ with hγ''_def
  have hSdisjoint : ∀ z ∈ ball c r \ T, e.symm z ∉ S := by
    intro z hz hzS
    have hzTarget : z ∈ e.target := hballsub hz.1
    have hzSrc : e.symm z ∈ e.source := e.map_target hzTarget
    exact hz.2 ⟨e.symm z, ⟨hzS, hzSrc⟩, e.right_inv hzTarget⟩
  refine ⟨γ'', ⟨{ toFun := fun z => e.symm (Hpq z)
                  continuous_toFun := hHcont
                  map_zero_left := hHzero
                  map_one_left := hHone
                  prop' := fun t x hx => by
                    rcases hx with hx | hx
                    · rw [hx]
                      show e.symm (Hpq (t, 0)) = γ 0
                      rw [γ.source]; exact hH0 t
                    · rw [Set.mem_singleton_iff] at hx
                      rw [hx]
                      show e.symm (Hpq (t, 1)) = γ 1
                      rw [γ.target]; exact hH1 t }⟩, ?_⟩
  rw [Set.disjoint_left]
  rintro z ⟨t, ht⟩ hzS
  rw [← ht] at hzS
  exact hSdisjoint (q t) (hqmem t) hzS

/-!
### The general (multi-chart) theorem — BLOCKED (design risk R4)

`exists_homotopic_avoiding`/`Loop.exists_homotopic_avoiding` need, per the design's §7 proof plan,
a strong induction on `ChartChain` length that at each step (a) inserts a *new* breakpoint value
`b₁ := e.symm b₁'` chosen off `S` inside the shared chart-ball of two adjacent pieces
(`nonempty_open_diff_finite` above supplies exactly this), then (b) re-decomposes `γ` at that new
breakpoint via a homotopy `((γ.truncate 0 c).cast _ _).trans ((γ.truncate c 1).cast _ _)
≃ γ` (rel endpoints), then (c) combines the (inductively) avoiding head/tail via
`Path.Homotopy.hcomp`.

Step (b) — `homotopic_truncate_trans` — is the concentrated risk (R4). Worked out here precisely
(more actionable than the design sketch) for whoever resumes this:

* Let `h0c : 0 ≤ c`, `h1c : c ≤ 1`. Define
  `head := (γ.truncate 0 c).cast (h1 : a = γ.extend (min 0 c)) rfl`, where
  `h1 := by rw [min_eq_left h0c, γ.extend_zero]`, and
  `tail := (γ.truncate c 1).cast (h2 : γ.extend c = γ.extend (min c 1)) γ.extend_one.symm`, where
  `h2 := by rw [min_eq_left h1c]`. Then `head.trans tail : Path a b` typechecks with *no* further
  casting (`head`'s target `γ.extend c` matches `tail`'s source on the nose).
* Define `ρ : I → I` by `ρ u := if (u:ℝ) ≤ 1/2 then ⟨min (2*u) c, _⟩ else ⟨min (max (2*u-1) c) 1, _⟩`
  (membership proofs: both branches land in `[0,1]` since `c ∈ [0,1]`). Show `Continuous ρ` via
  `continuous_if_le` (the two branches agree at `u = 1/2`: `min (2*(1/2)) c = min 1 c` vs
  `min (max 0 c) 1 = min c 1`; equal iff `c ≤ 1`, true). `ρ 0 = 0`, `ρ 1 = 1` by `norm_num` + `h0c`/
  `h1c` (`min 0 c = 0`, `min (max 1 c) 1 = 1` since `c ≤ 1 ≤ 1`... check `max 1 c` when `c≤1`: `= 1`).
* Prove `∀ u : I, (head.trans tail) u = γ.extend (ρ u)` via `Path.trans_apply` (splits on
  `(u:ℝ) ≤ 1/2`, matching `ρ`'s own if-split) + the `truncate`/`cast` unfoldings
  (`Path.cast_coe`, `Path.extend_apply`) — routine but long case-by-case `ℝ`-arithmetic
  (`min`/`max` identities), the actual bulk of R4.
* Conclude `head.trans tail = γ.reparam ρ hρcont hρ0 hρ1` via `Path.ext` (both sides have the
  same underlying function `γ.extend ∘ (↑) ∘ ρ = γ ∘ ρ` on `I`), then
  `(Path.Homotopy.reparam γ ρ hρcont hρ0 hρ1).cast rfl (by rw [← that Path.ext equality])` gives
  `γ.Homotopic (head.trans tail)`.

Given this, the outer induction (base case = `exists_homotopic_avoiding_of_ball` above applied to
the whole chain when `C.n = 0`; inductive step = pick a fresh breakpoint via
`nonempty_open_diff_finite`, split via the lemma above, apply the base case to the new `head`
piece and the induction hypothesis to the re-clocked `tail` piece, combine via
`Path.Homotopy.hcomp` and `Path.trans_range`) is mechanical. Not attempted here: genuinely
time-boxed out (design's own R4 flag; gates only `abel-weak-solutions`, no other consumer of this
unit). `nonempty_open_diff_finite` and `exists_homotopic_avoiding_of_ball` above are the
ingredients a future pass needs; both are proved and sorry-free. -/

theorem exists_homotopic_avoiding {a b : X} (γ : Path a b) {S : Set X} (hS : S.Finite)
    (ha : a ∉ S) (hb : b ∉ S) :
    ∃ γ' : Path a b, γ.Homotopic γ' ∧ Disjoint (Set.range ⇑γ') S := by
  -- TODO(blocker): strong induction on `exists_chartChain γ`'s length; see the module-doc note
  -- above (`homotopic_truncate_trans`, design R4) for the precise missing step.
  sorry

/-- Loop version (the blueprint's deliverable). -/
theorem Loop.exists_homotopic_avoiding {x₀ : X} (γ : Path x₀ x₀) {S : Set X} (hS : S.Finite)
    (hx₀ : x₀ ∉ S) : ∃ γ' : Path x₀ x₀, γ.Homotopic γ' ∧ Disjoint (Set.range ⇑γ') S :=
  RS.exists_homotopic_avoiding γ hS hx₀ hx₀

end RS

end
