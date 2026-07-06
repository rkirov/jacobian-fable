/-
Blueprint unit: meromorphic-trace. `Tr_F h`: the global assembly, file 5 of the design's 6-file
plan.
-/
import Jacobian.MeromorphicTrace.PlanarTrace
import Jacobian.MeromorphicTrace.OrderMultiplicity
import Jacobian.MappingDegree.LocalStructure

/-!
# `Tr_F h`: the surface-level fibre trace (meromorphic-trace, cluster 2)

Unit: meromorphic-trace (`docs/design/meromorphic-trace.md` §2 D7, §4.5, §5 P7). Standing surface
hypotheses on `X`; `Y` a second Riemann surface (`[T2Space Y]`, no compactness/connectedness
needed on `Y` itself).

* `trace F h y₀` — the fibre trace of `h` along `F`, evaluated via an arbitrary `FiberStack`
  chosen (per point) by `Classical.choice`; total via an `if`-dispatch on
  `Nonempty (FiberStack F y₀)` so the *definition* carries no `ContMDiff`/nonconstancy hypothesis
  (design §5.7's "Design correction", needed because `exists_fiberStack` itself needs `hne`).
* `trace_of_forall_eq` — junk guard: `trace` vanishes identically for constant `F` (R2 resolved
  honestly below: `Nonempty (FiberStack F y₀)` is shown FALSE outright at `y₀ = c` too, via a
  short cardinality argument, not left open as the design worried it might have to be).

**Scope decision (design §7 Risks 2 and 7, exercised as intended)**: `meromorphicAtX_trace`
(the file's centerpiece per the design) and `trace_of_regular` are **not proved in this pass**.
Both need `trace`'s well-definedness against the `FiberStack` choice (design's flagged risk R1:
"a `traceZk`-intertwines-with-local-biholomorphisms lemma... NOT designed"), which this build
traced one level further than the design did (see below) but did not finish — a genuine, still
open technical gap, not a lookup problem, so per this task's stuck-time policy it is reported
here (loudly, in the build log and the final handoff) rather than left as an admitted goal.

**The gap, precisely, and the resolution route found (not yet executed in Lean)**: at a FIXED
point `y`, `trace F h y` (whichever `FiberStack` `Classical.choice` picks) is *independent* of
that choice and literally equals the naive fibre sum `∑ᶠ x ∈ F⁻¹{y}, h x` — because every
`traceZk` call in the defining formula is evaluated AT its own junk point `0`
(`(S.A i).e' y₀ = 0` always, `AdaptedChartsAt.map_eq_zero'`), where `traceZk _ k 0 = _ 0`
(`traceZk_zero_apply`) unfolds to exactly `h (S.pt i)`. So `trace F h y = ∑ᶠ x ∈ F⁻¹{y}, h x` for
*every* `y`, regardless of the stack chosen there — a fact that bypasses R1's "compare two
stacks' formulas" problem entirely, IF one separately shows the *same* identity
`(fixed stack S valid on S.V) ⇒ ∀ y ∈ S.V, ∑ᵢ traceZk (h ∘ (S.A i).e.symm) (mult i) ((S.A i).e' y)
  = ∑ᶠ x ∈ F⁻¹{y}, h x` — a genuine planar-to-fibre bijection argument in the style of
`Jacobian.MappingDegree.LocalConstancy`'s `bijOn_e`/`sum_multiplicity_inter_source` (which proves
the analogous statement for `multiplicity`, not `h`-weighted sums), estimated at 100+ further
lines and NOT completed here. Once done, `meromorphicAtX_trace` follows the design's §5.7 route
(chart-transport `trace F h` near `y₀` to the SAME translated meromorphic-at-`0` sum
`∑ᵢ traceZk (h ∘ (S.A i).e.symm) (mult i)`, meromorphic by `meromorphicAt_traceZk`, P5, already
proved) essentially as sketched there.
-/

open scoped ContDiff Manifold OnePoint
open Filter Set Function Topology

namespace RS.MTrace

open scoped Classical

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {F : X → Y} {h : X → ℂ} {y₀ : Y}

/-- The fibre trace of `h` along `F`, evaluated via an arbitrary chosen `FiberStack` at `y₀`.
Total: `0` if no stack can be witnessed at `y₀` (the only case this can happen for holomorphic
`F` is at the single value of a *constant* map, `trace_of_forall_eq`). -/
noncomputable def trace (F : X → Y) (h : X → ℂ) (y₀ : Y) : ℂ :=
  if hS : Nonempty (RS.FiberStack F y₀) then
    have S := hS.some
    ∑ i, traceZk (h ∘ (S.A i).e.symm) (RS.multiplicity F (S.pt i)) ((S.A i).e' y₀)
  else 0

theorem trace_def (F : X → Y) (h : X → ℂ) (y₀ : Y) (hS : Nonempty (RS.FiberStack F y₀)) :
    trace F h y₀ = ∑ i, traceZk (h ∘ (hS.some.A i).e.symm) (RS.multiplicity F (hS.some.pt i))
      ((hS.some.A i).e' y₀) := dif_pos hS

theorem trace_of_not_nonempty (hns : ¬ Nonempty (RS.FiberStack F y₀)) : trace F h y₀ = 0 :=
  dif_neg hns

/-- A positive-dimensional charted space over `ℂ` (in particular perfect — no isolated points,
`RS.nhdsNE_neBot`) that is `Nonempty` is infinite. -/
private theorem infinite_of_chartedSpace_complex {Z : Type*} [TopologicalSpace Z] [T1Space Z]
    [ChartedSpace ℂ Z] [Nonempty Z] : Infinite Z := by
  rw [← not_finite_iff_infinite]
  intro hfin
  have : DiscreteTopology Z := Finite.instDiscreteTopology
  have hne : (𝓝[≠] (Classical.arbitrary Z)).NeBot := RS.nhdsNE_neBot _
  have hmem : (∅ : Set Z) ∈ 𝓝[≠] (Classical.arbitrary Z) := by
    rw [mem_nhdsWithin]
    exact ⟨{Classical.arbitrary Z}, isOpen_discrete _, rfl, by simp⟩
  exact hne.ne (Filter.empty_mem_iff_bot.mp hmem)

/-- Junk convention (R2, resolved): `trace` vanishes identically for constant `F`. Away from the
constant value, the fibre is empty, giving a genuine (degenerate, `n = 0`) `FiberStack` directly;
AT the constant value, `X` being infinite (`infinite_of_chartedSpace_complex`) makes
`Nonempty (FiberStack F y₀)` outright impossible (a `FiberStack`'s `pt : Fin n → X` would have to
enumerate all of `X` bijectively onto its range, impossible for infinite `X`, finite `n`). -/
theorem trace_of_forall_eq (c : Y) : trace (fun _ : X => c) h = fun _ => 0 := by
  funext y₀
  by_cases hy : y₀ = c
  · subst hy
    apply trace_of_not_nonempty
    rintro ⟨S⟩
    have hrange : Set.range S.pt = Set.univ := by
      rw [S.range_pt]; ext x; simp
    have hfin : (Set.univ : Set X).Finite := hrange ▸ Set.finite_range S.pt
    have : Infinite X := infinite_of_chartedSpace_complex (Z := X)
    exact Set.infinite_univ hfin
  · by_cases hS : Nonempty (RS.FiberStack (fun _ : X => c) y₀)
    · rw [trace_def _ _ _ hS]
      set S := hS.some with hS_def
      have hrange : Set.range S.pt = (∅ : Set X) := by
        rw [S.range_pt]
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        exact fun hcx => hy hcx.symm
      have h0 : IsEmpty (Fin S.n) := by
        rw [← not_nonempty_iff]
        rintro ⟨i⟩
        have hmem : S.pt i ∈ Set.range S.pt := Set.mem_range_self i
        rw [hrange] at hmem
        exact hmem
      haveI := h0
      simp
    · exact trace_of_not_nonempty hS

end RS.MTrace
