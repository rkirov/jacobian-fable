# Requests to unit: holomorphic-forms

## From paths-and-integrals (design phase, 2026-07-02)

1. **Transition-analyticity helper** (non-blocking; we have a ~15-line `Compat` fallback in
   `Jacobian/Path/LocalPrimitive.lean` via `StructureGroupoid.compatible_of_mem_maximalAtlas`
   + `contDiffOn_omega_iff_analyticOn` if you don't want it). You derive this inside
   `analyticOnNhd_coeffIn`/`coeffIn_trans` anyway — please export it:

   ```lean
   open IsManifold in
   theorem analyticOnNhd_transition {e e' : OpenPartialHomeomorph X ℂ}
       (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω X) :
       AnalyticOnNhd ℂ (↑e' ∘ ↑e.symm) (e '' (e.source ∩ e'.source))
   ```

   (local-multiplicity independently offers an equivalent `analyticAt_transition` to
   surfaces-and-charts — any one landed copy is fine, tell us which spelling wins.)

2. **Orientation pin on `coeffIn_trans`** (blocking for our proofs, not for our statements):
   our `rechart`/uniqueness/linearity proofs are keyed to the orientation in your design doc,

   ```lean
   coeffIn e' η z = deriv (↑e ∘ ↑e'.symm) z * coeffIn e η (e (e'.symm z))
   ```

   for `z ∈ e' '' (e.source ∩ e'.source)`. If the landed form differs (swapped roles,
   `EqOn` vs pointwise, extra hypotheses), please note it here.

3. **Confirmation of exports** we consume (all already in your design doc §2 — just don't drop
   them): `coeffIn`, `coeffIn_add`, `coeffIn_smul`, `coeffIn_zero`,
   `Form1.analyticOnNhd_coeffIn` (on `e.target`, maximal-atlas `e`),
   `coeffIn_mdifferential` (EqOn `deriv (f ∘ ↑e.symm)` on `e.target`),
   `contMDiffAt_iff_analyticAt_comp` (we use it with `F := ℂ` at `chartAt`-charts in
   `pathIntegral_mdifferential`).

## From jacobian-construction (design phase, 2026-07-06, non-blocking)

1. **`genus` must stay definitionally `Module.finrank ℂ (RS.Form1 X)`, no wrapper.** We set
   `basis X := Module.finBasis ℂ (Form1 X) : Basis (Fin (Module.finrank ℂ (Form1 X))) ℂ (Form1 X)`
   (`Mathlib/LinearAlgebra/Dimension/Free.lean:286`) and need this to *definitionally* equal
   `Basis (Fin (genus X)) ℂ (Form1 X)` (no `finCongr`/cast) for the challenge's
   `Fin (genus X) → ℂ` type to line up. As long as `Genus.lean`'s `def genus X := Module.finrank ℂ
   (RS.Form1 X)` is literally that expression (per your design doc §2.1), this is `rfl` — just
   confirming you won't wrap it in anything.
2. **`FiniteDimensional ℂ (Form1 X)` instance** (§2.6 of your doc) is all we need for
   `Module.finBasis` (`[Module.Finite ℂ (Form1 X)]`); `[Module.Free ℂ (Form1 X)]` is automatic
   (`Module.Free.of_divisionRing`, every vector space over a field is free) — no action needed
   from you, just confirming the dependency shape.

## From jacobian-functoriality (2026-07-06, non-blocking — local `Compat` copies carried in
`Jacobian/JacFunctorial/Pullback.lean`)

Needed a two-manifold chart-pullback for `Form1.pullback f hf : Form1 Y →ₗ[ℂ] Form1 X` along an
arbitrary `f : X → Y` (not just `f : X → ℂ`, which is all `mdifferential`/`Coeffs.lean` needed).
Three small facts were missing and proved locally; would be nice to have canonically:

1. **Two-manifold arbitrary-chart analyticity bridge**, generalizing
   `contMDiffAt_iff_analyticAt_of_mem_source` (`f : X → ℂ`) to an arbitrary charted target `Y`:
   ```lean
   theorem analyticAt_of_mem_maximalAtlas {f : X → Y} {x : X} (hf : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x)
       {e : OpenPartialHomeomorph X ℂ} (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) (hx : x ∈ e.source)
       {e' : OpenPartialHomeomorph Y ℂ} (he' : e' ∈ maximalAtlas 𝓘(ℂ) ω Y) (hy : f x ∈ e'.source) :
       AnalyticAt ℂ (⇑e' ∘ f ∘ ⇑e.symm) (e x)
   ```
   (proved directly from mathlib's `contMDiffWithinAt_iff_of_mem_maximalAtlas`, ~10 lines).
2. **Forward-chart identity** (symmetric counterpart of your own use of
   `mfderiv_chartAt_symm_chartAt_self`, `Coeffs.lean:156`):
   ```lean
   theorem mfderiv_chartAt_self (y : Y) : mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ y) y = ContinuousLinearMap.id ℂ ℂ
   ```
   (from mathlib's `mfderiv_extChartAt_self`, ~4 lines).
3. **Two-manifold generalization of `tangentCoord_mfderiv_comp`** (`Analyticity.lean:91`), reading
   the target through its own preferred chart instead of requiring the outer map to land in `ℂ`:
   ```lean
   theorem tangentCoord_mfderiv_chart_comp {F : X → Y} {g : ℂ → X} {z : ℂ}
       (hF : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F (g z)) (hg : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g z) :
       tangentCoord (mfderiv 𝓘(ℂ) 𝓘(ℂ) F (g z) (mfderiv 𝓘(ℂ) 𝓘(ℂ) g z (1 : ℂ))) =
         deriv (⇑(chartAt ℂ (F (g z))) ∘ F ∘ g) z
   ```
   (via `mfderiv_chartAt_self` + `mfderiv_comp` + your own `tangentCoord_mfderiv_comp`, ~12 lines).

All three are proved and carried locally in `Jacobian/JacFunctorial/Pullback.lean`'s `Compat`
section — non-blocking, just flagging for possible upstream adoption since they're natural
one-level generalizations of facts you already have.
