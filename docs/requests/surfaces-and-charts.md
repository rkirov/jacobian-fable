# Requests to unit: surfaces-and-charts

## From local-multiplicity (design phase, 2026-07-02)

1. **CC7 holomorphy bridge** (we prove it locally in
   `Jacobian/LocalMultiplicity/ChartBridge.lean`, `section Compat`, marked for upstreaming —
   please adopt this exact statement or tell us yours so the spellings match):

   ```lean
   theorem contMDiffAt_iff_analyticAt_inChartAt {F : X → Y} {x : X} :
       ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x ↔
         ContinuousAt F x ∧
           AnalyticAt ℂ
             (fun z ↦ chartAt ℂ (F x) (F ((chartAt ℂ x).symm z)) - chartAt ℂ (F x) (F x))
             (chartAt ℂ x x)
   ```

   (Recentered form; drop the `- const` if you prefer — `AnalyticAt.sub analyticAt_const`
   converts. Proof route: `contMDiffAt_iff` + `extChartAt 𝓘(ℂ) = chartAt` (rfl) +
   `contDiffWithinAt_univ` + `ContDiffAt.analyticAt`/`AnalyticAt.contDiffAt`.)

2. **Shared planar analytic IFT contract** (no action needed, just convention): both units use
   mathlib's `AnalyticAt.analyticAt_localInverse`, `analyticAt_comp_iff_of_deriv_ne_zero`
   (`Mathlib/Analysis/Calculus/InverseFunctionTheorem/Analytic.lean`),
   `HasStrictDerivAt.localInverse` (`.../Deriv.lean`), and
   `HasStrictFDerivAt.toOpenPartialHomeomorph` (`.../FDeriv.lean`) — verified to exist at the
   pinned commit (see `docs/design/local-multiplicity.md` §1 and the compiled spike).

3. **Optional upstream candidates** we will prove locally and offer:
   `trans_mem_maximalAtlas` (maximal atlas is closed under `≫ₕ` with a `contDiffGroupoid ω 𝓘(ℂ)`
   element) and `analyticAt_transition` (maximal-atlas transitions are analytic with
   `deriv ≠ 0`). Take them if they fit your unit better.

## From holomorphic-forms (design phase, 2026-07-02, non-blocking)

**CC7 holomorphy bridge, vector-valued target.** holomorphic-forms proves locally
(`Jacobian/Forms/Coeffs.lean`, `section Compat`, marked for upstreaming) the bridge for maps
into any complex Banach space (needed for the `(ℂ →L[ℂ] ℂ)`-valued in-trivialization
representatives of Hom-bundle sections; planar source, no ℝ-structure involved):

```lean
theorem contMDiffAt_iff_analyticAt_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (f : X → F) (x : X) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, F) ω f x ↔ AnalyticAt ℂ (f ∘ ↑(chartAt ℂ x).symm) (chartAt ℂ x x)
```

(Route: `contMDiffAt_iff` + `range 𝓘(ℂ) = univ` + `contDiffWithinAt_omega_iff_analyticWithinAt`
(`Mathlib/Analysis/Calculus/ContDiff/Defs.lean:157`, needs `[CompleteSpace F]`); `ContinuousAt`
recovered from the analytic rep. This is the vector-space-target cousin of local-multiplicity's
item 1.) When freezing CC7's bridge lemmas, please state them for a general complex Banach
target `F` (specializing to `ℂ` where wanted) so both consumers can delete their local copies.
