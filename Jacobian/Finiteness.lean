import Jacobian.Finiteness.Schwartz
import Jacobian.Finiteness.BddHolo
import Jacobian.Finiteness.CompactRestrict
import Jacobian.Finiteness.Chain

/-!
# finiteness-and-chi: `FiniteDimensional H¹(X, O_D)` via Schwartz/Montel (namespace `RS`/`RS.Finiteness`)

API summary (see `docs/design/finiteness-and-chi.md`). **Partial delivery**: 4 of 7 design files
are written (all gate-free per the design's §3 file plan); `TradeBounded.lean`, `H1Finite.lean`,
`Chi.lean` are NOT written (gated — see "What remains" below). No file uses the forbidden tactic.

* **`Schwartz.lean`** (namespace `RS`, pure Banach — zero project imports):
  `schwartz_finite_cospan` (the L. Schwartz perturbation lemma, cospan/span form: a compact
  perturbation of a surjective `CLM` between Banach spaces has finite-codimensional range),
  `finiteDimensional_of_cospan` (consumer wrapper), `FiniteDimensional.of_linearMap_ker_range`
  (finite-kernel + finite-codomain ⇒ finite domain — the extension helper reused everywhere
  downstream). Mirrors mathlib's own `ContinuousLinearMap.exists_preimage_norm_le` proof texture.

* **`BddHolo.lean`** (namespace `RS.Finiteness`): `BddHoloOn S` (bounded-holomorphic functions on
  `↥S` as a *closed* `Submodule` of `↥S →ᵇ ℂ` — `isClosed_bddHoloOn` via a chart-local
  uniform-limit argument, hence `CompleteSpace (BddHoloOn S)`), `restrictCLM` (norm `≤ 1`,
  presheaf law `restrictCLM_restrictCLM`), the germ bridges `toGerm`/`evalAt_toGerm`/
  `toGerm_restrict_comm` (germification into `LinSysOn 0`) and `restrictGerm`/
  `toGerm_restrictGerm`/`restrictGerm_toGerm` (de-germification via `holoRepr` on `S' ⋐ S`,
  `[T2Space X] [CompactSpace X]`).

* **`CompactRestrict.lean`**: `isCompactOperator_restrictCLM` — Montel's theorem: for
  `S' ⋐ S ⊆ source (chartAt ℂ x₀)`, `restrictCLM : BddHoloOn S → BddHoloOn S'` is a compact
  operator (built from `Jacobian/Forms/Montel.lean`'s `isCompact_closure_montelFamily`). Also
  `isCompactOperator_of_isCompactOperator_val` (Compat: a `CLM` into a *closed* submodule is
  compact once its ambient-valued composite is, via `Subtype.isCompact_iff`).

* **`Chain.lean`**: `ShrinkChain X` (Forster's `𝔚 ⋐ 𝔙 ⋐ 𝔘 ⋐ 𝔘*` same-index-set chain, D3) with
  `ShrinkChain.nonempty` (existence on `[T2Space X] [CompactSpace X]`), the four induced
  `Cech.FinCover ⊤`s (`coverStar`/`coverU`/`coverV`/`coverW`) and refinement facts
  (`good_star`, `ref_star_U`/`ref_star_V`/`ref_star_W`/`ref_U_V`/`ref_V_W`/`ref_U_W`, all `τ = id`);
  the Banach cochain layer at one level (`NC0`/`NC1`, `deltaCLM`, `NZ1` — bounded cocycles as a
  `ContinuousLinearMap.ker`, closed and complete for free — `resNC0`/`resNC1`/`resZ`, and the
  cocycle-relation workhorse `NZ1.rel_res`/`resNC1_mapsTo_NZ1`); and Forster's 14.6(b) Banach
  geometry: `tradeDefect` (the defect CLM on `Z¹(𝔘) × Z¹(𝔙) × C⁰(𝔚)`), `tradeSpace` (Forster's
  subspace `L` as its `ContinuousLinearMap.ker`, complete + normed instances registered),
  `mem_tradeSpace_iff`/`mem_tradeSpace_iff_eq`, and the two Schwartz-cospan projections
  `tradePi`/`tradeCompact`.

## What remains (gated; honest scope note for the continuation builder)

Per the task's gate: `TradeBounded.lean`/`H1Finite.lean`/`Chi.lean` need cech's `Colimit`/`Window`/
`Skyscraper` (now BUILT — the cech gate opened during this session) **and** the not-yet-built
`dolbeault-comparison` unit's `Leray.lean` exports (`exists_trade`, `toH1_surjective_of_isGood`,
`h1CoverEquiv`; no `Jacobian/DolbeaultComparison/` directory exists yet). Since `dolbeault` is
still entirely absent, these three files are not written (not merely gated by an easy check —
there is nothing to import).

`Chain.lean`'s `tradeDefect`/`tradeSpace`/`tradePi`/`tradeCompact` (Forster's 14.6(b) subspace
`L` and its two Schwartz-cospan projections) ARE now delivered — the former
`IsTopologicalAddGroup`-instance-resolution wall was diagnosed and resolved by registering
canonical `Submodule.*` instance shortcuts on `↥(NZ1 T P)`/`↥(tradeSpace T)` (full post-mortem
in the note at the end of `Chain.lean`; the §5/§6.5 Schwartz consumption shapes were verified
to type-check against them). The two `IsCompactOperator` assembly lemmas the design's §4.4
lists (`isCompactOperator_resZ_UV`, `isCompactOperator_tradeCompact`) remain deferred — no
longer instance-blocked, but their finite-`Pi`/product Montel assembly (§6.3 step 5) belongs
with the `TradeBounded.lean`-gate work.

None of `χ` ledger (`Chi.lean`), the all-`D` finiteness bookkeeping, or the
`FiniteDimensional ℂ (H1 (0 : Divisor X))` headline instance are delivered — all live downstream
of the gates above. `canonical-forms`/`riemann-roch` cannot yet consume this unit; a
continuation builder should (once dolbeault lands) write
`TradeBounded.lean`/`H1Finite.lean`/`Chi.lean` per the design's §5–§8 proof plans.
-/
