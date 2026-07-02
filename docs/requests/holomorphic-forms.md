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
