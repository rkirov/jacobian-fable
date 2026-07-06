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

## From jacobian-construction (design phase, 2026-07-06, non-blocking)

1. **Generalize `chartedSpaceOfFamily`/`isManifold_of_family`**
   (`Jacobian/Surface/ChartedSpaceKit.lean`) from hardcoded codomain `ℂ` to an arbitrary
   `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]`. We need it for charts into
   `Fin (genus X) → ℂ` (the torus's model space), not just `ℂ` (ℙ¹'s model space). Nothing in the
   ~65-line proof is `ℂ`-specific except the scalar field of `AnalyticOnNhd` (which stays `ℂ`) —
   textually replacing the hardcoded `ℂ` codomain by `E` should work verbatim. Non-blocking: we
   carry a local, textually-identical copy in
   `Jacobian/JacobianConstruction/ChartedSpaceKitV.lean` either way; happy to delete it if you
   generalize yours (please keep the same field/lemma names so the copies are drop-in compatible).

2. **`LocPathConnectedSpace X` / `PathConnectedSpace X` instances** for any `X` with
   `[ConnectedSpace X] [ChartedSpace ℂ X]` — a two-line derivation
   (`ChartedSpace.locPathConnectedSpace (H := ℂ)` then `PathConnectedSpace.of_locPathConnectedSpace`,
   see `Mathlib/Geometry/Manifold/ChartedSpace.lean:268` and
   `Mathlib/Topology/Connected/LocPathConnected.lean:102`). We need path-connectedness of `X` for
   `Jacobian.ofCurve` to be total (any two points are joined by *some* path). No unit currently
   provides this (checked). Likely wanted elsewhere too (sphere-topology, mapping-degree). We
   carry a local `Compat` copy regardless (`Jacobian/JacobianConstruction/OfCurve.lean`).

3. **Confirmation of exports** we consume unchanged: `contMDiffAt_iff_analyticAt_of_mem_source`,
   `contMDiffOn_iff_analyticOnNhd_of_subset_source` (Bridges — used in the last step of
   `ofCurve_contMDiff`'s chart-composite argument).
