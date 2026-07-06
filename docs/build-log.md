- [localmult] KthRoot.lean OK (49 lines, 6s)
- [forms] Jacobian/Forms/Montel.lean OK (133 lines, 6s)
- [localmult] PlanarNormalForm.lean OK (157 lines, 6s)
- [forms] Jacobian/Forms/Basic.lean OK (83 lines, 11s)
- [surfaces] Bridges.lean OK (161 lines, 7s)
- [surfaces] RealSmooth.lean OK (124 lines, 8s)
- [surfaces] ChartedSpaceKit.lean OK (65 lines, 6s)
- [localmult] ChartBridge.lean OK (212 lines, 5s)
- [localmult] Multiplicity.lean OK (244 lines, 6s)
- [surfaces] Identity.lean OK (245 lines, 7s)
- [surfaces] InverseFunction.lean OK (200 lines, 7s)
- [localmult] AdaptedCharts.lean OK (293 lines, 9s)
- [localmult] Composition.lean OK (241 lines, 7s)
- [localmult] Jacobian/LocalMultiplicity.lean (unit root) OK (33 lines, 4s; scripts/check.sh Jacobian/LocalMultiplicity passes, zero sorries — unit COMPLETE)
- [residue] TaylorCoeff.lean OK (235 lines)
- [residue] LaurentCoeff.lean OK (383 lines)
- [mapdeg] RootCounting.lean OK (123 lines, 6s)
- [mapdeg] Basics.lean OK (144 lines, 8s)
- [mapdeg] Basics.lean OK (149 lines, 8s)
- [mapdeg] Basics.lean OK (151 lines, 8s)
- [mapdeg] Basics.lean OK (153 lines, 8s)
- [mapdeg] Ramification.lean OK (146 lines, 7s)
- [mapdeg] LocalStructure.lean OK (170 lines, 7s)
- [forms] Jacobian/Forms/Coeffs.lean OK (296 lines, 12s)
- [forms] Jacobian/Forms/Analyticity.lean OK (239 lines, 8s; split-off file, uses surfaces-and-charts `Jacobian.Surface.Bridges.contMDiffAt_iff_analyticAt_comp_chartAt` bridge)
- [forms] Jacobian/Forms/OfCoeffs.lean OK (170 lines, 6s)
- [forms] Jacobian/Forms/MDifferential.lean OK (134 lines, 29s)
- [forms] Jacobian/Forms/Finiteness.lean OK (480 lines, 16s; fixed 4 small issues found on first compile: a `rw` needing `Set.mem_preimage` unfolding, missing `open scoped Classical` for the junk-extended `gext`, `restr_mem_maximalAtlas` is root-level not `StructureGroupoid.`-namespaced and takes the groupoid explicitly, `Metric.isClosed_closedBall` needs its namespace)
- [forms] Jacobian/Forms/Genus.lean OK (32 lines, 6s; root-level `genus`/`genus_eq_zero_iff_subsingleton`, exact challenge signature)
- [forms] Jacobian/Forms.lean (unit root) OK (50 lines, 5s; scripts/check.sh Jacobian/Forms passes, zero sorries — unit COMPLETE; NOT registered in Jacobian.lean per task hard rule, orchestrator to add `import Jacobian.Forms`)
- [residue] TaylorCoeff.lean recheck OK (235 lines, 5.7s) — unchanged since last entry, recompiled clean
- [residue] LaurentCoeff.lean recheck OK (383 lines, 6.5s) — unchanged since last entry, recompiled clean
- [residue] PrincipalPart.lean OK (236 lines, 6.0s) — found already complete (all §4.3 exports present), zero sorries
- [residue] Residue.lean OK (376 lines, ~7s) — resAt algebra, resAt_deriv, resAt_deriv_div (via mathlib's logDeriv API), resAt_tail_mul/resAt_analyticAt_mul/resAt_mul (Serre-pairing atoms; resAt_mul via a general disjoint-Icc-union helper lemma), zero sorries
- [mapdeg] LocalConstancy.lean OK (150 lines, ~6s) — heart part 2: `FiberStack.sum_multiplicity_inter_source` (chart bijection with the planar root set + multiplicity transport via `analyticOrderAt_charts_eq_multiplicityENat`, both as private plumbing lemmas), `FiberStack.fiberMultSum_eq_sum` (disjoint decomposition via `finsum_mem_iUnion`), `isLocallyConstant_fiberMultSum`, `fiberMultSum_const` (well-definedness). Gotcha: `set k := ...; set A := S.A i` (in THIS order — k before A) is required, else `set`'s abstraction of `k` invalidates the already-introduced `A`'s type and produces a stale shadow `A✝`.
- [mapdeg] Degree.lean OK (216 lines, ~8s) — `degree`, `fiberMultSum_eq_degree`, positivity (`one_le_degree`, `degree_pos_iff`), `multiplicity_le_degree`, regular-fiber cardinality (`ncard_fiber_of_isRegularValue`, `ncard_fiber_le_degree`), degree-1 ⇒ bijective/homeo bank (`bijective_of_degree_eq_one`, `homeomorphOfDegreeEqOne`, `coe_homeomorphOfDegreeEqOne`, `isHomeomorph_of_degree_eq_one`), and `degree_comp` (multiplicativity, kept — did not need to drop it; needs local `[CompactSpace Y]`). Zero sorries.
- [mapdeg] Covering.lean OK (89 lines, ~7s) — `exists_openPartialHomeomorph_coe_eq` (coe-exact upgrade via a private `copyOfEqOn` field-by-field rebuild of `OpenPartialHomeomorph`, NOT dot-notation-named to avoid `RS.OpenPartialHomeomorph.copyOfEqOn` namespace capture), `isCoveringMapOn_compl_branchLocus`, `isEvenlyCovered_of_isRegularValue`. Zero sorries.
- [mapdeg] Jacobian/MappingDegree.lean (unit root) OK (48 lines, ~4s; `scripts/check.sh Jacobian/MappingDegree` passes, zero sorries — unit COMPLETE; NOT registered in `Jacobian.lean` per task hard rule, orchestrator to add `import Jacobian.MappingDegree`). All 7 design files + root present: RootCounting, Basics, Ramification, LocalStructure (pre-existing, verified unchanged), LocalConstancy, Degree, Covering (new). No upstream drift found — local-multiplicity's `AdaptedCharts`/`Composition` and surfaces-and-charts' `Jacobian.Surface` APIs matched the design doc exactly, no `docs/requests/` additions needed.
- [residue] ChangeOfVariables.lean OK (160 lines, ~6s) — resAt_comp_mul_deriv (chart invariance, route (a) fully algebraic) + resAt_comp_mul_deriv_of_eventuallyEq corollary, zero sorries
- [residue] IntegralBridge.lean OK (174 lines, ~8s) — circleIntegral_eq_two_pi_I_mul_resAt (fixed-radius, via annulus deformation + Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable) + MeromorphicAt.eventually_circleIntegral_eq_two_pi_I_mul_resAt (small-radius form), zero sorries
- [residue] GermFunctionals.lean OK (86 lines, ~5s) — MeromorphicGerm, meromorphicGermsAt Submodule, laurentCoeffL/resL linear functionals, zero sorries
- [p1] Jacobian/ProjectiveLine/Inversion.lean OK (129 lines, ~6s) — `inversion` (noncomputable, `z ↦ z⁻¹`/`∞↦0`/`0↦∞`), `inversion_involutive`, `inversion_eq_infty_iff`, the `𝓝 ∞` filter work (`tendsto_coe_cocompact`, `tendsto_coe_inv_nhdsNE_zero`), `continuous_inversion`, `inversionHomeomorph`. Zero sorries.
- [p1] Jacobian/ProjectiveLine/Charts.lean OK (232 lines, ~5s) — `coeChart`/`invChart` (both hand-rolled per design §3.2, junk `coeChart ∞ = 0` and `invChart` unconditional `↑z ↦ z⁻¹`; `invChart` built directly rather than via `Homeomorph.toOpenPartialHomeomorph.trans` per fallback R2 — simpler and avoids `trans_source` simp friction), `chartFamily`/`chartIndex`, `instChartedSpace`/`instIsManifold` (via `RS.chartedSpaceOfFamily`/`RS.isManifold_of_family`), `atlas_eq`, `*_mem_maximalAtlas`, `Nontrivial (OnePoint ℂ)`, topology-instance smoke tests, plus two small extra helper lemmas (`coeChart_inversion_coe`, `invChart_inversion_coe`) added for reuse in `Holomorphy.lean`'s `contMDiff_inversion`. Zero sorries.
- [p1] Jacobian/ProjectiveLine/Holomorphy.lean OK (197 lines, ~5-9s) — `contMDiff_coe`, `ContMDiffAt.onePointCoe`/`ContMDiff.onePointCoe`, `contMDiffAt_iff_analyticAt_of_ne_infty`/`_of_eq_infty`, `contMDiffAt_of_pole` (simplified vs. design's φ-construction: uses mathlib's `tendsto_cobounded_of_meromorphicOrderAt_neg` + `meromorphicOrderAt_inv` + `AnalyticAt.of_meromorphicOrderAt_pos` directly, no zpow bookkeeping needed — R6 avoided), `meromorphicAt_coeChart_comp` (simplified vs. design's dichotomy argument: `coeChart`-composite `=` `invChart`-composite`⁻¹` GLOBALLY as a plain algebraic function identity via `inv_inv`/`inv_zero`, so no punctured-filter transport needed — R5 avoided), `contMDiff_inversion`/`inversionDiffeomorph`. R3 (∞ notation clash) hit as expected, fixed by type-ascribing `(∞ : OnePoint ℂ)` throughout. Zero sorries.
- [p1] Jacobian/ProjectiveLine/Sphere.lean OK (29 lines, ~5s) — `homeoSphere := onePointEquivSphereOfFinrankEq (by simp [Complex.finrank_real_complex])`, one-liner per design §3.4/§7 spike. Zero sorries.
- [p1] Jacobian/ProjectiveLine/GenusZero.lean OK (137 lines, ~7s) — `form1_eq_zero` (coefficient-decay + Liouville, design §4 P8, followed closely), `Subsingleton (RS.Form1 (OnePoint ℂ))`, `finrank_form1`, root-level `RS.genus_onePoint : genus (OnePoint ℂ) = 0`. Built last (after Forms unit landed complete). Zero sorries.
- [p1] Jacobian/ProjectiveLine.lean (unit root) OK (41 lines, ~5s; scripts/check.sh Jacobian/ProjectiveLine passes, zero sorries — unit COMPLETE; NOT registered in `Jacobian.lean` per task hard rule, orchestrator to add `import Jacobian.ProjectiveLine`). Scoped notation `ℙ¹ := OnePoint ℂ` in `RS.P1`. No `docs/requests/` additions needed — all consumed upstream APIs (Surface's `ChartedSpaceKit`/`Bridges`, Forms' `Coeffs`/`Genus`) matched the design doc exactly.
- [residue] MittagLeffler.lean OK (245 lines, ~6.5s) — PrincipalPartData (as a Submodule-subtype, free AddCommGroup/Module), Realizes, toFun, totalRes, ofMeromorphicOn + realizes_ofMeromorphicOn, Realizes.add/smul/sub_orderAt_nonneg, realizes_zero_iff, zero sorries
- [residue] Jacobian/ResidueCalculus.lean (unit root) OK (41 lines; scripts/check.sh Jacobian/ResidueCalculus passes, zero sorries — unit COMPLETE: TaylorCoeff 235, LaurentCoeff 383, PrincipalPart 236, Residue 376, ChangeOfVariables 160, IntegralBridge 174, GermFunctionals 86, MittagLeffler 245 lines, 1936 total)
- [mero] Jacobian/Meromorphic/Predicates.lean OK (342 lines, ~6s) — MeromorphicAtX/OnX, ordAtX, chart-transport workhorse `eventually_nhdsNE_iff_comp_chart` (+ apply/eventuallyEq/tendsto specializations), chart invariance, arithmetic, classification, CC4 compat. Zero sorries.
- [mero] Jacobian/Meromorphic/CodiscreteBridge.lean OK (160 lines, ~5s) — D2 bridge (mem_codiscreteWithin_iff_of_isOpen + specializations), codiscreteWithin_neBot, NeBot(codiscrete X) instance, congr_codiscreteWithin, analyticAt_codiscreteWithin, meromorphic identity dichotomy (clopen argument via eventually_ordAtX_eq_top/eventually_ordAtX_eq_zero), codiscrete_setOf_ne_zero. Zero sorries.
- [mero] Jacobian/Meromorphic/GermSpace.lean OK (231 lines, ~6s) — Algebra ℂ (Germ l ℂ) Compat via Algebra.ofModule, meroGermSubalgebra, MeroGermOn/ℳ X, mk/mk_eq_mk/exists_rep/ind/mk_add.../algebraMap_mk, restrictGerm + MeroGermOn.restrict as AlgHom, restrict_mk/restrict_restrict/restrict_id, algebraMap_injective. Zero sorries.
- [mero] Jacobian/Meromorphic/OrderEval.lean OK (329 lines, ~7s) — ord (liftOn descent) + calculus, evalAt (D5) + tendsto_evalAt/algebra, holoRepr + holoRepr_eventuallyEq_nhdsNE (unconditional-on-ord, via MeromorphicAt.eventually_analyticAt) + holoRepr_contMDiffAt (toMeromorphicNFAt route per design §6.5) + mk_holoRepr, continuousAt/tendsto_cobounded exports. Zero sorries.
- [paths] Jacobian/Path/Planar.lean OK (185 lines; disk primitives via mathlib HasPrimitives,
  local uniqueness, Convex.isPathConnected_diff_countable adapted from
  Set.Countable.isPathConnected_compl_of_one_lt_rank, exists_homotopy_range_subset_of_convex)
- [paths] Jacobian/Path/LocalPrimitive.lean OK (255 lines; IsPrimitiveAlongMap + mono/add_const/
  congr/congr_map/continuousOn/comp/rechart/sub_eq_sub/glue + isPrimitiveAlongMap_of_ball helper;
  uses RS.analyticAt_trans from Forms/Analyticity.lean per Forms builder's deviation note, not
  the requested analyticOnNhd_transition which was not exported)
- [paths] Jacobian/Path/Chain.lean OK (84 lines; ChartChain + exists_chartChain via
  exists_monotone_Icc_subset_open_cover_unitInterval)
- [paths] Jacobian/Path/Continuation.lean OK (341 lines; exists_isPrimitiveAlong via ChartChain
  induction + clampI upgrade to univ, pathIntegral + pathIntegral_eq, pathIntegral_refl/symm/
  trans/reparam/cast, pathIntegral_add/smul/zero_form, pathIntegralₗ)
- [paths] Jacobian/Path/Bridge.lean OK (110 lines; pathIntegral_eq_intervalIntegral single-chart
  C1 bridge via FTC-2 (intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le), and
  pathIntegral_mdifferential FTC-along-a-path for mdifferential)
- [mero] Jacobian/Meromorphic/Field.lean OK (90 lines, ~5s) — Inv (pointwise, unconditional), mk_inv, ord_inv, Mero.ord_ne_top/ord_eq_top_iff (identity dichotomy corollary), Mero.mul_inv_cancel, Field (ℳ X) instance. Zero sorries.
- [mero] Jacobian/Meromorphic/Divisor.lean OK (315 lines, ~6s) — Function.locallyFinsuppWithin.degree Compat (+ degree_zero/add/neg/mono/nonneg_of_nonneg), Divisor X abbrev, MeroGermOn.divisorOn (local finiteness via eventually_ordAtX_eq_top/eq_zero, §6.3 plan), divisor total map + algebra (mul/inv/smul/algebraMap/min_divisor_le_divisor_add), divisor_nonneg_iff (unconditional, via untop₀_nonneg), compactness finiteness (finite_support_divisor, finite_setOf_ord_neg/pos, eventually_ord_eq_zero). Zero sorries.
- [paths] Jacobian/Path/HomotopySquare.lean OK (462 lines; gridK/GridChain/exists_gridChain (2D
  Lebesgue grid via exists_monotone_Icc_subset_open_cover_unitInterval_prod_self), product hcov/
  preconnected helpers, row assembly + column stacking induction, exists_primitive_along_square
  (the centerpiece), pathIntegral_congr_homotopic, pathIntegralQ(+trans),
  pathIntegral_congr_freeHomotopic, pathIntegral_eq_of_simplyConnected,
  period_eq_zero_of_homotopic_refl)
- [mero] Jacobian/Meromorphic/Gluing.lean OK (74 lines, ~6s) — MeroGermOn.exists_glue/glue_unique (§6.6 sheaf gluing via holoRepr pointwise rigidity, no coherence lemma). Zero sorries.
- [mero] Jacobian/Meromorphic/LinSysMulEquiv.lean OK (61 lines, ~7s) — mul_mem_linSys_sub_divisor + linSysMulEquiv (L(D) ≃ₗ[ℂ] L(D - divisor φ) via LinearEquiv.ofLinear, §6.7). Zero sorries.
- [mero] Jacobian/Meromorphic.lean (unit root) OK (scripts/check.sh Jacobian/Meromorphic passes, zero sorries — unit COMPLETE, all 10 files + design doc's six hard proof plans §6.1-§6.7 including gluing and linSysMulEquiv). NOT registered in Jacobian.lean per task hard rule.
- [paths] Jacobian/Path/Periods.lean OK (75 lines; period/period_trans/symm/refl/
  congr_homotopic/conj, periodVector + trans/symm/refl)
- [paths] Jacobian/Path/Perturb.lean PARTIAL (184 lines; nonempty_open_diff_finite and
  exists_homotopic_avoiding_of_ball [single-chart-ball base case] are complete and sorry-free;
  exists_homotopic_avoiding / Loop.exists_homotopic_avoiding are BLOCKED with one `sorry` and a
  detailed TODO(blocker) note — the general ChartChain-induction (design R4: breakpoint insertion
  + homotopic_truncate_trans reparametrization bookkeeping) was time-boxed out; see module doc for
  the precise reparam strategy worked out for a future pass. Gates only abel-weak-solutions.)
- [paths] Jacobian/Path.lean (unit root) OK (69 lines; scripts/check.sh Jacobian/Path builds
  clean but FAILS the sorry-grep solely due to Perturb.lean's one documented blocker sorry —
  all 8 unit files individually build with zero errors; 7/8 are fully sorry-free. NOT registered
  in Jacobian.lean per task hard rule, orchestrator to add `import Jacobian.Path`.)
- [paths] Perturb.lean FIXED (the single blocker `sorry` in exists_homotopic_avoiding /
  Loop.exists_homotopic_avoiding is eliminated; scripts/check.sh Jacobian/Path now passes with
  zero sorries. Route: (i) `homotopic_truncateOfLE_trans` — the R4 truncation-splitting lemma
  `γ|[c,e] ≃ γ|[c,d] ⬝ γ|[d,e]` proved via `Path.Homotopy.reparam` with the explicit piecewise
  clock `ρ u = if u ≤ 1/2 then min (2u) d else max (2u-1) d` and min/max ℝ-arithmetic;
  (ii) `exists_homotopic_avoiding_aux` — downward induction on the number of remaining
  ChartChain pieces, carrying a "lead-in" path inside chart-ball k from a point already off S to
  the breakpoint γ.extend (t k): each step splits the tail with (i), picks a fresh breakpoint
  off S in the chart image of the overlap of adjacent chart-ball domains (countable-complement
  density, as in nonempty_open_diff_finite), connects with an arc pulled back through the chart,
  perturbs the one-ball head via exists_homotopic_avoiding_of_ball, recurses on the tail with
  lead-in arc.symm, and glues with Path.Homotopic.trans_assoc/trans_symm/refl_trans (new import
  Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic) + hcomp; base case feeds the whole
  remaining truncation to the ball lemma since t k = 1 there. Statements unchanged. Also updated
  the stale "partial/sorry" status paragraph in Jacobian/Path.lean's module doc, which itself
  tripped check.sh's sorry-grep.)
- [sphtop] Jacobian/SphereTopology/GlobalPrimitive.lean OK (180 lines, ~7s) — the genus-0 engine:
  `contMDiff_and_mdifferential_eq_of_isPrimitiveAlongMap_id` (rechart + `AnalyticAt.congr` +
  `contMDiffAt_iff_analyticAt_comp_chartAt` + `Filter.EventuallyEq.deriv_eq`/`HasDerivAt.deriv`
  coefficient matching), `exists_isPrimitiveAlongMap_id` (global primitive via `pathIntegral` from
  a base point; well-definedness via `pathIntegral_eq_of_simplyConnected`; the chart-local
  straight-segment argument built from mathlib's `Path.segment`/`Path.map'`/`Path.cast` combinators
  — cleaner than the design's hand-rolled-path sketch, and avoids needing the `clampI`-composition
  boost since `Path.map'.extend` lands in `Set.range` of the underlying segment unconditionally),
  `form1_eq_zero_of_simplyConnectedSpace` (Forster 10.5, via
  `MDifferentiable.exists_eq_const_of_compactSpace` + `mdifferential_const`), `Subsingleton
  (Form1 X)` instance, `genus_eq_zero_of_simplyConnectedSpace`. Built FIRST per task order (does
  not need the perturbation lemma). Zero sorries.
- [sphtop] Jacobian/SphereTopology/SimplyConnectedP1.lean OK (101 lines, ~5s) — ported the spike
  (`scratch_sphtop.lean`) verbatim for `isSimplyConnected_compl_infty`/`_compl_coeZero` +
  `PathConnectedSpace (OnePoint ℂ)`, then assembled `simplyConnectedSpace_onePoint` via
  `simply_connected_iff_loops_nullhomotopic` + `RS.Loop.exists_homotopic_avoiding` with the
  basepoint case split (`x = ∞` uses `S := {↑0}`, else `S := {∞}`) +
  `isSimplyConnected_iff_exists_homotopy_refl_forall_mem` + `Path.Homotopic.trans`, plus
  `simplyConnectedSpace_of_homeoOnePoint`/`simplyConnectedSpace_sphere`. Built LAST per task order
  (needed the perturbation lemma). Compiled clean on the first attempt with zero sorries — by the
  time this file was written, the fixer had ALREADY resolved `Perturb.lean`'s blocker sorry (see
  "Perturb.lean FIXED" above), so no `Loop.exists_homotopic_avoiding`-shaped risk materialized;
  docstring updated post-hoc to drop the now-stale caveat.
- [sphtop] Jacobian/SphereTopology/Headline.lean OK (34 lines, ~4-6s) — `genus_eq_zero_of_homeo_sphere`,
  the exact 3-line assembly per design §4 (`simplyConnectedSpace_of_homeoOnePoint` composed with
  `RS.P1.homeoSphere.symm`, then `genus_eq_zero_of_simplyConnectedSpace`). Zero sorries.
- [sphtop] Jacobian/SphereTopology.lean (unit root) OK (45 lines; `scripts/check.sh
  Jacobian/SphereTopology` passes, zero sorries — unit COMPLETE, all 4 design files present,
  360 lines total). NOT registered in `Jacobian.lean` per task hard rule, orchestrator to add
  `import Jacobian.SphereTopology`.
- [cech] Jacobian/Cech/Covers.lean OK (355 lines, ~5s) — FinCover Ω (D2), IsRefIdx/Preorder/chosenRefIdx (D3), FinCover.meet/IsDirectedOrder (pairwise meets via finProdFinEquiv), IsChartDisk/IsGood (D4), exists_chartDisk_basis/exists_chartDisk_closure_basis (§6.3), exists_good_refinement/exists_good_refinement_closure, FinCover.IsAdapted + exists_adapted_refinement (§6.2, deviation: added explicit `hS : ∀ p ∈ S, p ∈ Ω` hypothesis — see file docstring, needed since `FinCover Ω` members can't reach points outside `Ω`), FinCover.IsAdapted.not_mem_inf. Zero sorries.
- [cech] Jacobian/Cech/Cochains.lean OK (244 lines, ~6s) — LinSysOn.restrictL + restrictL_restrictL/restrictL_id/ord_restrictL, MeroGermOn.congrSet [Compat], C0/C1/C2 as `abbrev` (not `def` — avoids instance/ext diamond friction), d0/d1/d0_apply/d1_apply/d1_comp_d0, Z1/B1/B1_le_Z1/mem_Z1_iff, H1Cover (`noncomputable abbrev`, same reason) + mk/mk_surjective/mk_eq_zero_iff/subsingleton_h1Cover_iff, Z1.ord_diag. Zero sorries.
- [cech] Jacobian/Cech/H0.lean OK (143 lines, ~5s) — toC0/toC0'/toC0'_injective(via congrSet+glue_unique)/toC0'_surjective(via exists_glue)/toC0'_bijective, h0EquivLinSysOn (via LinearEquiv.ofBijective), h0EquivLinSysOn_symm_apply(_ord), linSysOn_top_eq_linSys (Opens.coe_top is rfl), h0Equiv (global H⁰≃L(D)). Zero sorries.
