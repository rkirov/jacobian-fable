import Jacobian.Abel.WeakToMero

/-!
# abel-theorem: the sufficiency direction (`docs/design/abel-theorem.md` §4.1 D1, §2.1)

Unit: abel-theorem. Namespace `RS.Abel`. The unit's centerpiece, and its ONE genuinely blocked
piece — see the "Status" section below and the root file for the full, precise account.

## Status: the Dolbeault-upgrade bridge (design §4.3, this design's own risk R1) is BLOCKED

`exists_mero_of_pathIntegral_mem`'s proof is complete through step 4 of the design's own §2.1
proof plan (loop cancellation via `Loops.lean` + the weak solution `f` via
`RS.AbelWeak.exists_weakSolutionOfPair`, itself now fully built — see `AbelWeak/GeneralChain.lean`).
Steps 5-7 (package `f`'s local log-derivative data into a global `Form01 X`, show it pairs to
zero against every holomorphic `1`-form via `serre-duality-tails`' `resEquiv`/`i_neg_eq_h1`, then
promote via the CR-converse already built in `WeakToMero.lean`) are **NOT completable**: as of
this build, `serre-duality-tails` (`RS.TailDuality`, Miranda VI.3's Lemma 3.4/3.6 surjectivity)
has **no directory on disk at all** (`Jacobian/TailDuality` does not exist — confirmed directly,
not merely "designed, not built"). This is a genuine EXTERNAL blocker (an entire sibling unit,
outside this builder's authorized scope of `Jacobian/Abel/` + the one `Jacobian/AbelWeak/`
rechart gap), not a coding gap: `resEquiv`/`i_neg_eq_h1` cannot even be STATED without that unit's
vocabulary (`H1Tail`, `pairT`, the Serre pairing), so there is no way to isolate the gap as a
smaller, self-contained hypothesis either. Flagged LOUDLY per this task's own stuck-blocker
protocol: **one admitted step, precisely placed, immediately below** — every other step (loop
cancellation, weak-solution existence, the CR-promotion mechanics, the genus-0 necessity
shortcut) is fully proved, no admitted steps, and ready to consume the bridge fact the moment
`serre-duality-tails` lands (its exact interface is `docs/design/abel-theorem.md` §4.3's
`exists_dbar_eq_zero_of_forall_basis_pairing_eq_zero`).

The **easy/necessity direction** (§2.2, "`∃F` with one simple pole `⟹` `genus X = 0`") is fully
built, no admitted steps: `genus_eq_zero_of_exists_simple_pole` (`WeakToMero.lean`).
-/

open scoped ContDiff Manifold

noncomputable section

namespace RS.Abel

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Forster 20.7, sufficiency direction, two-point form** (§4.1 D1, the blueprint's literal
"two-point Abel–Jacobi value" statement). Proof complete through step 4 of the design's §2.1 plan
(loop cancellation, `Loops.lean`, + weak-solution existence, `AbelWeak.exists_weakSolutionOfPair`,
NOW fully built); steps 5-7 (the Dolbeault-upgrade bridge + CR-promotion) are blocked on
`serre-duality-tails`, entirely unbuilt (see the file docstring) — flagged here as the unit's
ONE documented external blocker. -/
theorem exists_mero_of_pathIntegral_mem {P Q : X} (hPQ : Q ≠ P) (δ : Path Q P)
    (hmem : (fun k => RS.pathIntegral δ (RS.basis X k)) ∈ RS.periodSubgroup X) :
    ∃ F : RS.Mero X, F ≠ 0 ∧ F.ord P = 1 ∧ F.ord Q = -1 ∧
      ∀ z, z ≠ Q → z ≠ P → F.ord z = 0 := by
  -- Steps 1-3 (§2.1): loop cancellation — `δ'` has EXACT zero period against every `ω`.
  obtain ⟨δ', -⟩ := RS.Abel.exists_zeroPeriod_path δ hmem
  -- Step 4: the weak solution of the pair `(P, Q)` along `δ'` (fully general chart chain,
  -- `AbelWeak/GeneralChain.lean`).
  obtain ⟨f, U, hf, hUopen, hUcompact, hPU, hQU, hf1⟩ :=
    RS.AbelWeak.exists_weakSolutionOfPair hPQ δ'
  -- Steps 5-7: BLOCKED, see the file docstring.
  -- TODO(blocker): `serre-duality-tails` (`RS.TailDuality.resEquiv`/`i_neg_eq_h1`, Miranda VI.3's
  -- Lemma 3.4/3.6 surjectivity) has no directory on disk at all; the Dolbeault-upgrade bridge
  -- (design §4.3) cannot be built, and its interface cannot even be stated without that unit's
  -- own vocabulary. Once it lands, this proof continues: package `f`'s chart-local
  -- `wirtingerDbar f / f` data into `η : RS.Form01 X`, obtain `u : RS.SmoothC X` with
  -- `RS.dbar u = η` from the bridge, set `F := fun z => Complex.exp (-(u z)) * f z`, promote to
  -- genuine holomorphy off `Q` via `RS.differentiableAt_of_wirtingerDbar_eq_zero` chart-by-chart
  -- (the `∂̄F = 0` computation itself is `wirtingerDbar_exp_neg_mul_eq_zero`, ALREADY BUILT,
  -- `WeakToMero.lean`), package as `MeroGermOn.mk F hF : RS.Mero X`, and read off the order
  -- claims from `f`'s own `IsWeakSolutionAt` local models (unaffected by multiplying the
  -- nowhere-zero factor `Complex.exp (-(u ·))`).
  sorry

/-- **The necessity-composed genus-`0` corollary** (the shape `ofCurve_inj'`'s proof needs):
if the basis-period vector of SOME connecting path lies in `RS.periodSubgroup X` for `Q ≠ P`,
then `genus X = 0`. Composes `exists_mero_of_pathIntegral_mem` (blocked, see above) with the
ALREADY-BUILT necessity shortcut `genus_eq_zero_of_exists_simple_pole` (`WeakToMero.lean`). -/
theorem genus_eq_zero_of_pathIntegral_mem {P Q : X} (hPQ : Q ≠ P) (δ : Path Q P)
    (hmem : (fun k => RS.pathIntegral δ (RS.basis X k)) ∈ RS.periodSubgroup X) :
    genus X = 0 := by
  obtain ⟨F, -, hordP, hordQ, hreg⟩ := exists_mero_of_pathIntegral_mem hPQ δ hmem
  refine genus_eq_zero_of_exists_simple_pole F Q hordQ (fun x hx => ?_)
  rcases eq_or_ne x P with rfl | hxP
  · rw [hordP]; norm_num
  · rw [hreg x hx hxP]

end RS.Abel

end
