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
- [cech] Jacobian/Cech/Refinement.lean OK (261 lines, ~6s) — resC0/resC1(+_apply, rfl-based), resC1_comp_d0, resC1_mem_B1, Z1.rel_res (§6.5 workhorse, flexible-hypothesis form so callers supply whichever composite proof they have — proof irrelevance does the rest), resC1_mem_Z1, resZ1/resH1 (Submodule.mapQ), resH1_mk, **resH1_indep (Forster 12.3, full proof, no sorry)** — the DirectedSystem key for Colimit.lean, plus functor laws resC0_id/resC1_id/resZ1_id/resH1_id and resC0_comp/resC1_comp/resZ1_comp/resH1_comp. Zero sorries. NOTE: resH1_injective (Forster 12.4) NOT YET attempted — deferred per design's own risk mitigation (§9.4); will attempt after Colimit.lean core assembly if time remains.
- [cech] Jacobian/Cech/Colimit.lean OK (158 lines, ~48s — needs `set_option maxHeartbeats 1000000` on the `DirectedSystem` instance, heavy `abbrev` unfolding) — resH1'/resH1'_eq_resH1, `DirectedSystem` instance (map_self/map_map from Refinement's resH1_id/resH1_comp), **H1 D as `noncomputable abbrev` Module.DirectLimit** (CC8 centerpiece; abbrev needed so Module.DirectLimit's API — of/lift/exists_of/induction_on — unify transparently, mirroring the C0/C1/C2/H1Cover abbrev pattern), toH1/toH1_resH1'/toH1_resH1, exists_rep/exists_rep_good/exists_rep_refined, H1.induction_on, subsingleton_H1_of_all_subsingleton/subsingleton_H1_of_good (do NOT need 12.4), H1.lift + H1.lift_toH1 (universal property). Zero sorries. Leray interface recorded as a docstring only (owned by dbar-solvability/dolbeault-comparison per design §7). D-functoriality (H1Incl) attempted next.
- [dbar] Jacobian/Dbar/Wirtinger.lean OK (243 lines) — wirtingerD/wirtingerDbar, clm_apply_eq_add_conj_smul (Complex.ext re/im decomposition, avoids the self-referential rw[hv] trap), CR bridge (differentiableAt_iff_wirtingerDbar_eq_zero via candidate L1•id), (0,1) chain rule (wirtingerDbar_comp_differentiableAt/wirtingerD_comp_differentiableAt, via HasFDerivAt.comp_hasDerivAt_of_eq pattern for the fderiv_comp helper), regularity (contDiffOn/continuous/hasCompactSupport_wirtingerDbar). Zero sorries.
- [dbar] Jacobian/Dbar/CauchyKernel.lean OK (452 lines) — cauchyKernel + measurability/local-integrability (polar lintegral bound), cauchyTransform + wirtingerDbar_cauchyTransform (convolution-derivative package), cauchyPompeiu (Forster 13.1 centerpiece: polar rewrite to a bounded box T'=Ioc 0 R'xIoo(-pi,pi) avoiding the indicator-Fubini-swap dance per design R1 fallback (ii), Wirtinger split of the integrand, r-leg/theta-leg FTC via intervalIntegral.integral_eq_sub_of_hasDerivAt, custom setIntegral_prod_symm helper since mathlib lacks it at the pin), wirtingerDbar_cauchyTransform_eq + exists_dbar_solution_of_hasCompactSupport (13.1 exports). GOTCHA for siblings: lake env lean does NOT enforce the project's autoImplicit=false (silently auto-binds free identifiers like an undeclared g); only lake build (= scripts/check.sh) catches it — always add explicit 'variable (g : C -> C)' and verify with lake build, not just lake env lean. Zero sorries.
- [mtrace] Jacobian/MeromorphicTrace/PlanarTrace.lean OK (384 lines, ~7-9s) — `traceZk` (D6), basic API (`traceZk_eq_finset_sum`, `traceZk_zero_apply`, `traceZk_comp_pow`; `traceZk_add` guarded by `k≠0` — deviation, design's unconditional version is false at `k=0` by a 2-line counterexample, documented inline; `traceZk_const_mul` unconditional via `smul_finsum`), `analyticAt_traceZk` (P4, local root branches + `Complex.isPrimitiveRoot_exp`/`injOn_pow_mul`, no monodromy), `meromorphicAt_traceZk` (P5, THE hardest theorem — growth-bound route via Euclidean split of the order by `k`, `Complex.differentiableOn_update_limUnder_of_bddAbove` removable singularity, zero sorries). **One documented blocker**: `laurentCoeffAt_traceZk` (P6, the Laurent-coefficient formula) is `sorry`'d with a ~30-line inline comment recording two candidate routes (design's `tsum`/power-series substitution, and a `tsum`-free finite-remainder route found during this build via `AnalyticAt.exists_taylor_remainder`) and exactly why neither was finished in the time budget (each needs a further ~100+-line growth-bound argument on top of P5's, not completed) — flagged loudly per the stuck->45min protocol; `resAt_traceZk`/`ordAt_traceZk_ge` are consequently NOT stated (would build on the sorry). P4/P5 (traceZk's existence as meromorphic at `0`, needed everywhere else including `FunctionTrace.lean`) do NOT depend on P6 and are fully proved.
- [mtrace] Jacobian/MeromorphicTrace/ToP1.lean OK (312 lines, ~6-7s) — `toP1` (D2), `toP1_eq_infty_iff`/`toP1_eq_coe_iff`, `toP1_contMDiff` (P1) — **routed through `meromorphic-and-divisors`'s `MeroGermOn.holoRepr`/`OrderEval.lean`** (built by the time of this session, contrary to the design's design-time assumption of "not yet built"; the design's own forward-looking note in §D2/§10 anticipated exactly this simplification) rather than the design's from-scratch chart-repair derivation, giving a substantially shorter, more robust proof of the same statement. `NotEventuallyConstX`/`toP1_not_const` (D3) via a private `eventuallyEq_zero_codiscrete_of_forall_ordAtX_pos` helper (order `>0` everywhere forces order `=⊤` everywhere, by the same "isolated zeros" contradiction, `eventually_ordAtX_eq_zero`). Five reusable `holoRepr`/`toP1` facts exported for `OrderMultiplicity.lean`/`ArgumentPrinciple.lean`. Zero sorries.
- [mtrace] Jacobian/MeromorphicTrace/OrderMultiplicity.lean OK (188 lines, ~5-6s) — `multiplicity_toP1_of_ordAtX_pos`/`_neg` (P2, zero/pole cases), via a shared private CC4-level `inChartAt`-germ bridge `multiplicityENat_toP1_eq_of_eventuallyEq` (reused for both, target chart `coeChart`/`invChart` resp. companion `f'`/`f'⁻¹`) plus CC3↔CC4's already-built `ordAtX_of_contMDiffAt_eq_zero`. **Deviation**: the design's third export `multiplicity_toP1_of_ordAtX_eq_zero` (`ordAtX f x=0 → multiplicity(toP1 f)x=1`) is mathematically FALSE as stated (counterexample `f(z)=1+z²` at `0`: order `0`, multiplicity `2` — `ordAtX=0` only says `f` doesn't vanish/pole, says nothing about `deriv f`/ramification) and is NOT proved; the design itself flags it as non-essential ("we do not need it ourselves"). Zero sorries.
- [mtrace] Jacobian/MeromorphicTrace/ArgumentPrinciple.lean OK (134 lines, ~6s) — **THE argument principle** `finsum_ordAtX_eq_zero` (P3) via `fiberMultSum_eq_degree` at `↑0`/`∞` on `ℙ¹` (mapping-degree's counting engine, NOT the residue theorem/Stokes per the design's explicit routing warning), `toP1_eq_coe_zero_iff_ordAtX_pos` translation helper (order-`0`-exactly excluded via `tendsto_ne_zero_of_meromorphicOrderAt_eq_zero`), `sum_ordAtX_eq_zero_of_finite` (Finset form), `finsum_ordAtX_eq_zero'` (raw `NotEventuallyConstX` wrapper). Zero sorries. This is the exact lemma `proper-map-degree` needs for `deg(divisor f)=0` (see downstream note in the unit root file).
- [mtrace] Jacobian/MeromorphicTrace/FunctionTrace.lean OK (125 lines, ~6-8s) — `trace` (D7, `Tr_F h`, correctly guarded via `if hS : Nonempty (FiberStack F y₀)` per the design's own §5.7 "design correction", no hypotheses on the def itself), `trace_of_forall_eq` (R2 junk guard, FULLY resolved including the case the design worried might stay an "open sub-case" — via a short `infinite_of_chartedSpace_complex` argument: `X` charted over `ℂ` + perfect (`RS.nhdsNE_neBot`) + nonempty (`ConnectedSpace`) ⟹ infinite, ruling out `Nonempty(FiberStack (const) y₀)` at the constant value by a cardinality contradiction). **Scope decision** (design §7 Risks 2/7, exercised as sanctioned): `meromorphicAtX_trace`/`trace_of_regular`/`trace_well_defined` NOT proved — all need `trace`'s well-definedness against the arbitrary `FiberStack` choice (design's flagged risk R1); this build traced the gap one level further than the design (documented resolution route: routing through the naive fibre sum `∑ᶠx∈F⁻¹{y},h x`, which needs a `mapping-degree`-style bijection argument, `LocalConstancy.lean`'s `bijOn_e` pattern, not completed) but did not finish it. Zero sorries in this file (the gap is reported via the module docstring, not a `sorry`).
- [mtrace] Jacobian/MeromorphicTrace.lean (unit root) OK (70 lines; `lake build Jacobian.MeromorphicTrace` passes; `scripts/check.sh Jacobian/MeromorphicTrace` reports the one PlanarTrace.lean `sorry` (P6, `laurentCoeffAt_traceZk`) as the sole failure — flagged loudly, see PlanarTrace.lean's entry above and the final handoff notes). NOT registered in `Jacobian.lean` per task hard rule. All argument-principle/order-multiplicity/`toP1` content (cluster 1) is complete with zero sorries and ready for `proper-map-degree`; `traceZk`'s existence-as-meromorphic (P4/P5) is complete and ready for `form-trace-tower`; `Tr_F h`'s definition and junk guard are ready, its meromorphy is the one open item for `form-trace-tower`, alongside `laurentCoeffAt_traceZk`.
- [pmd] Jacobian/ProperDegree/ChallengeDegree.lean OK (60 lines, ~4s) — `_root_.ContMDiff.degree`
  (challenge signature, `docs/Jacobian_challenge.lean:147`) as a `rfl`-wrapper over
  `RS.degree`/`RS.MappingDegree`, plus `degree_eq`/`degree_of_forall_eq`/`degree_comp` restated in
  wrapper form. **Deviation from the design doc**: the design's §3.1 sketch declared
  `variable {f : X → Y}` (implicit); the challenge file's own preamble declares `f` **explicit**
  (`variable (f : X → Y) (hf : ContMDiff ...)`, confirmed load-bearing by `pushforward_pullback`'s
  RHS `(ContMDiff.degree f hf) • P`, applying `f` positionally) — corrected here to match the
  target signature verbatim; `f` explicit throughout this file. `[Nonempty Y]` discharged for
  free via `ConnectedSpace.toNonempty`. Zero sorries.
- [pmd] Jacobian/ProperDegree/DivisorDegreeZero.lean OK (94 lines, ~4-5s) — `divisor_degree_eq_zero`
  (THE argument principle in `Divisor`/`ℳ X` terms), `sum_ord_eq_zero_of_finite` (Finset
  corollary), `linSys_eq_bot_of_degree_neg'` (the unconditional discharge of
  `Meromorphic/LinearSystem.lean:206`'s conditional `linSys_eq_bot_of_degree_neg`, primed to avoid
  a namespace clash). **`Jacobian/MeromorphicTrace/ArgumentPrinciple.lean` had ALREADY landed** by
  build time (contrary to the design doc's design-time assumption that it was still missing), so
  per the design's own §5 R1 adapter note this file used the short "cite instead of reprove" route
  citing `MTrace.finsum_ordAtX_eq_zero'`/`MTrace.sum_ordAtX_eq_zero_of_finite` directly, NOT the
  ~110–150 line self-contained fallback the design also provided — the design's own fallback was
  not needed/exercised. Remaining work: (a) a constancy case split translating `ℳ X`-nonconstancy
  (`φ ≠ algebraMap c` for all `c`) to mtrace's raw `NotEventuallyConstX f`, and (b) matching
  `Divisor.degree`'s `Finset`-sum shape to the finsum via
  `Function.locallyFinsuppWithin.degree_eq_sum_of_subset`, using `Mero.ord_ne_top` (connected-surface
  identity theorem: `φ ≠ 0` ⟹ `ord ≠ ⊤` everywhere, `Meromorphic/Field.lean`) to rule out the
  `⊤`-order edge case in the Finset-membership direction. GOTCHA hit twice: `rw`/`push_neg`-style
  rewriting of an `Iff`/`Eq` lemma directly under a bare `≠` (`Ne`) goal fails ("did not find
  occurrence") even when the printed goal shows the exact pattern — the workaround used throughout
  is `intro hcontra` first (turning the `Ne` into a plain hypothesis-producing goal), then `rw`
  works on the resulting bare `Eq`/`Iff` normally; noted for siblings hitting the same shape. Zero
  sorries.
- [pmd] Jacobian/ProperDegree/GenusZeroFinisher.lean OK (79 lines, ~5-6s) —
  `homeoSphere_of_exists_simple_pole` (a single simple pole ⇒ `RS.MTrace.toP1 f` has degree `1` ⇒
  `X ≃ₜ ℙ¹ ≃ₜ S²`, via `RS.homeomorphOfDegreeEqOne`/`RS.P1.homeoSphere`), assembled entirely from
  `MappingDegree`/`MeromorphicTrace.OrderMultiplicity`/`ProjectiveLine.Sphere` — zero dependency on
  `ArgumentPrinciple.lean` (nonconstancy is witnessed directly by the pole location `Q` via surface
  perfectness `RS.nhdsNE_neBot`/`self_mem_nhdsWithin`, cheaper than the general codiscrete
  argument), matching the design's own risk note that this file is independent of the mtrace-timing
  risk. Hit the same `rw`-under-`Ne` gotcha as `DivisorDegreeZero.lean` (see that entry); same
  `intro`-first workaround applied. Zero sorries. This was the safest file in the unit, as the
  design anticipated.
- [pmd] Jacobian/ProperDegree.lean (unit root) OK (48 lines; `scripts/check.sh
  Jacobian/ProperDegree` passes, zero sorries — unit COMPLETE, all 3 design files present + root,
  282 lines total, well under the design's ~370–460 line estimate, mainly because
  `ArgumentPrinciple.lean`'s early landing eliminated the need for `DivisorDegreeZero.lean`'s
  self-contained fallback route). NOT registered in `Jacobian.lean` per task hard rule, orchestrator
  to add `import Jacobian.ProperDegree`. DAG correction recorded in the root docstring (drop
  `Builds on: monodromy`, per the design doc's §2; the real edges are `mapping-degree,
  meromorphic-and-divisors, meromorphic-trace, projective-line`). Recommend the orchestrator also
  add `proper-map-degree` to `genus-zero-headline`'s `Builds on:` list (design doc §2, non-blocking
  flag — `homeoSphere_of_exists_simple_pole` is a direct dependency, not merely transitive through
  riemann-roch).
- [cech] Jacobian/Cech/Colimit.lean update — added D-functoriality: `RS.linSysOn_mono` Compat (requested, not upstreamed), `inclusion_restrictL_comm`, `inclC0`/`inclC1` (+apply, mem_Z1), `h1CoverIncl` (+_mk), `inclC1_comp_resC1`, `h1CoverIncl_resH1`, **`H1Incl` (D-monotone functoriality H1 D →ₗ H1 D')** via `Module.DirectLimit.map`, `H1Incl_toH1`, `H1Incl_id`, `H1Incl_comp`. Final size 278 lines, zero sorries, `lake build` clean (needed `set_option maxHeartbeats 1000000` on 2 heavy declarations due to abbrev-unfolding cost — expected/acceptable, noted in file). GOTCHA for future editors: `lake env lean <file>` alone is NOT a faithful check — it seems to tolerate `autoImplicit`-style unbound identifiers that `lake build` (which honours the project's `autoImplicit=false`) correctly rejects; always finish with `lake build Jacobian.Cech.<File>` before declaring a file done.
- [dbar] Jacobian/Dbar/SolveDisk.lean OK (429 lines, ~10s) — Forster 13.2 (the R2 recursion, biggest time budget item): contDiff_indicator_bump_smul/hasCompactSupport_.../eqOn_... (cutoff-extension helpers, needs `Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension` import for the `HasContDiffBump ℂ` instance — easy to miss, `ContDiffBump` application `φ z` silently fails to elaborate without it), exhaustion radii solveRho/solvePhi/solveGcut/solveF (13.1-based raw solutions on shrinking sub-balls), the Nat.rec correction sequence via a private Σ-type `SolveState` + `solveStepData` (per-step: power series of the holomorphic difference `f_{n+1}-Fn` via `DifferentiableOn.hasFPowerSeriesOnBall` + `HasFPowerSeriesOnBall.tendstoUniformlyOn'` on THREE nested auxiliary radii strictly between ρn,ρ(n+1), extracting a partial-sum degree m via `Exists.choose`/`choose_spec` — NOT `obtain`, since the goal is data-valued (Subtype) not Prop, so eliminating a Prop-valued `∃` needs the choice functions, not the `cases`/`rcases`/`obtain` tactics which hit "large elimination" errors), solveState_bound (the (iii) geometric bound, proved once as `rfl`-unfolding of the step function, no double-choice risk), final assembly via `tendstoUniformlyOn_tsum_nat` (Weierstrass M-test) + telescoping identity + `TendstoLocallyUniformlyOn.differentiableOn` (uniform-limit-of-holomorphic) to get the tail term `TN` holomorphic on each exhaustion ball `B_N`, `u := F_N + T_N` there (ContDiffOn via the holomorphic-to-real-smooth bridge, NOT by claiming `u` itself is holomorphic — that would be false since ∂̄u=g≠0). GOTCHAS for siblings: (1) `ℝ≥0`/`NNReal` notation needs `open scoped NNReal` explicitly (silently parses as `ℝ ≥ 0`, a bogus Type-level comparison, giving bizarre `LE Type`/`OfNat Type 0` instance errors otherwise); (2) `tendsto_add_atTop_iff_nat k : Tendsto (fun n => f (n+k)) atTop l ↔ Tendsto f atTop l` — note the argument order `n+k` not `k+n`, easy to mismatch against `Nat.add_comm`-equal-but-not-defeq expressions, fix via `simpa [Nat.add_comm]`; (3) after `rw [hSomeDef]` on a `set`-introduced Pi-subtraction/addition (`f - g`/`f + g`), a *lambda* form `fun w => f w - g w` used in a later goal will NOT syntactically match `wirtingerDbar_sub`/`_add`'s stated `f - g`/`f + g` pattern despite being defeq — insert a local `have heq : (fun w => f w op g w) = f op g := rfl; rw [heq]` bridge every time. Zero sorries.
- [jaccon] Jacobian/JacobianConstruction/ChartedSpaceKitV.lean OK (69 lines) — Surface's
  `chartedSpaceOfFamily`/`isManifold_of_family` textually generalized from hardcoded codomain `ℂ`
  to an arbitrary `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]` (primed names, namespace
  `RS`); request filed to surfaces-and-charts (already on file from the design phase). Zero sorries.
- [jaccon] Jacobian/JacobianConstruction/Torus.lean OK (479 lines) — the abstract layer for
  `V ⧸ L`, `L : AddSubgroup V`: `AddCommGroup`/`TopologicalSpace`/`T2Space` unconditional (the
  T2-via-closure trick, `haveI : IsClosed (L.topologicalClosure : Set V) := ...` gotcha as
  flagged by the design, spiked); raw-representative charts `chartAt'`/`rawChartAux` (simplified
  from the design's "centered" charts — no recentering needed, transitions are still translations
  by a locally-constant lattice element, exposed standalone as `analyticOnNhd_chartAt'_trans` for
  `ULift.lean` to reuse) giving `ChartedSpace`/`IsManifold 𝓘(ℂ,V) ω (V ⧸ L)` gated by
  `[DiscreteTopology L]`; `LieAddGroup` (`contMDiff_add_torus`/`contMDiff_neg_torus`, same
  affine-chart-composite technique, `[CompleteSpace V]` needed for `AnalyticAt.contDiffAt` — not
  flagged by the design, add as a hypothesis); `CompactSpace (V ⧸ L.toAddSubgroup)` gated by
  `[IsZLattice ℝ L]` (`IsZLattice.isCompact_range_of_periodic`, spiked, compiled as designed); the
  `→ₜ+` substrate `inducedHom`/`contMDiff_inducedHom` (spiked §9.2 verbatim; §9.3's `ContMDiff`
  proof is new, same affine-chart technique, `analyticAt_linearMap` via bundling the bare
  `LinearMap` into a `ContinuousLinearMap` on the fly). GOTCHA for siblings: use `abel`, not
  `ring`, for `V`-element identities (`V` is only an `AddCommGroup`, not a ring) — `ring`
  silently fails with a `ring_nf` suggestion, easy to misdiagnose. Zero sorries.
- [jaccon] Jacobian/JacobianConstruction/Periods.lean OK (46 lines) — `basis X := Module.finBasis
  ℂ (Form1 X)` (`open Module` needed at this pin, per the task's own note) and `periodSubgroup X :=
  AddSubgroup.closure (range (periodVector (basis X)))` over loops based at `Classical.arbitrary
  X` (`Nonempty X` free from `[ConnectedSpace X]`). Zero sorries.
- [jaccon] Jacobian/JacobianConstruction/ULift.lean OK (207 lines) — the `ULift` shell's transport
  toolkit, specialized to the torus per the design's own R1 fallback (not a fully generic
  `M ≃ₜ M'` toolkit — `ULift.up`/`.down` cancel by `rfl`, `PartialEquiv.coe_trans_symm`, which the
  fully-generic route would not get for free): `ChartedSpace`/`IsManifold (ULift (V ⧸ L))` by
  transporting `Torus.analyticOnNhd_chartAt'_trans` through an **exact** (not merely eventual)
  transition function-and-source identity; `LieAddGroup` via a different, cleaner route than
  re-deriving the affine-chart argument — `ULift.up`/`ULift.down` are themselves shown `ω`-smooth
  (chart composite is the identity on an open set, no lattice shift at all, since domain/codomain
  charts align exactly), so addition/negation on `ULift (V ⧸ L)` factor through `Torus`'s own
  `contMDiff_add_torus`/`contMDiff_neg_torus` by plain composition (`ContMDiff.comp`/`.prodMap`).
  GOTCHA for siblings: universe variables in `ULift.{u}` are **not** auto-shared across
  declarations in one file even with matching notation — a bare `.{u}` without a file-level
  `universe u` command gives each declaration its own fresh metavariable, causing baffling
  "failed to infer universe levels" errors deep inside otherwise-fine `have`/`show` terms; fix is
  a single `universe u` line up top. Zero sorries.
- [jaccon] Jacobian/JacobianConstruction/Basic.lean OK (125 lines) — `RS.Jac₀ X`/`Jacobian
  (X : Type u) [...] : Type u := ULift.{u} (RS.Jac₀ X)`, both `abbrev` (not `def`) so every
  `Torus`/`ULift` instance transfers by instance search alone, no manual wiring; the challenge's
  instance block under `namespace Jacobian`: `AddCommGroup`/`TopologicalSpace`/`T2Space`
  unconditional (every genus incl. `g = 0`, sanity-checked via an `example` deriving
  `Subsingleton (Jacobian X)` from `genus X = 0`, `Function.Surjective.subsingleton` +
  `ULift.ext`); `instChartedSpace`/`instIsManifold`/`instLieAddGroup`/`instCompactSpace` gated by
  `[DiscreteTopology (periodSubgroup X).topologicalClosure]` (+ `IsZLattice` for compactness).
  GOTCHA/finding for period-lattice-rank: `Torus.compactSpace_torus` is stated for `L : Submodule
  ℤ V` while the other three hooks are stated for the `AddSubgroup` directly — bridged here via a
  **new instance** `RS.discreteTopology_toIntSubmodule` (`Homeomorph.setCongr` on the equal
  carrier sets, `AddSubgroup.coe_toIntSubmodule`); this must be an `instance` (not a `theorem`),
  since `IsZLattice`'s own class signature has `[DiscreteTopology L]` as an instance-argument
  needed *while elaborating* `instCompactSpace`'s signature itself. Zero sorries.
- [jaccon] Jacobian/JacobianConstruction/OfCurve.lean OK (262 lines) — `ofCurve`/
  `ofCurve_eq_of_path` (well-definedness via `periodVector_mem_periodSubgroup`, a
  basepoint-independence lemma via `period_conj` that the design didn't spell out explicitly but
  is needed since `periodSubgroup` is generated by loops at one fixed arbitrary basepoint, not
  the basepoint `ofCurve` is called at)/`ofCurve_self`, plus **`ofCurve_contMDiff` fully proved,
  zero sorries** (the design's highest-risk item, §8.3) — gated by
  `[DiscreteTopology (periodSubgroup X).topologicalClosure]` (a finding not flagged by the design:
  the challenge's bare statement literally does not elaborate without this, since it needs
  `ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)` for its codomain — same gating as
  `Basic.lean`'s four instances). Proof: chart `e` at `x₀`, holomorphic primitives `g i` on a ball
  (`exists_hasDerivAt_ball`), straight-segment path in the chart pulled back through `e.symm` via
  mathlib's `Path.segment`/`Path.map'` (`ContinuousOn`, not full `Continuous` — avoided hand-rolling
  a `Path` structure entirely, a nice find), `IsPrimitiveAlongMap`/`isPrimitiveAlongMap_of_ball`
  giving the local formula `ofCurve P z = ULift.up (mk (v₀ + g (e z)))` (`hkey`), then the same
  locally-constant-lattice-shift chart computation as `Torus`/`ULift` to assemble `ContMDiffAt`.
  Also carries `Compat` `LocPathConnectedSpace`/`PathConnectedSpace X` instances (request already
  on file). Zero sorries.
- [jaccon] Jacobian/JacobianConstruction/Functorial.lean OK (91 lines) — the `→ₜ+` substrate
  wrapped through the `ULift` shell: `RS.uliftUpHom`/`RS.uliftDownHom` (generic `G →ₜ+ ULift G`/
  `ULift G →ₜ+ G` via `AddEquiv.ulift` + `Homeomorph.ulift`, reusable), `Jacobian.inducedHom`/
  `Jacobian.contMDiff_inducedHom` composing these with `Torus.inducedHom`/`contMDiff_inducedHom`.
  Takes the hypothesis at the **raw** `periodSubgroup` level (not its closure) and derives the
  closure-level hypothesis `Torus.inducedHom` needs via `AddSubgroup.topologicalClosure_minimal`
  (since `(periodSubgroup Y).topologicalClosure` is already closed and `T` continuous, its
  `comap` is closed too). Compiled clean on the first real attempt — the only file in the unit
  that did. Out of scope (flagged per design R4, not silently dropped): the actual
  `pushforward`/`pullback` for a real holomorphic `f` needs "pullback of holomorphic 1-forms",
  which no unit in the 30-unit blueprint owns — a genuine blueprint gap for the orchestrator.
  Zero sorries.
- [jaccon] Jacobian/JacobianConstruction.lean (unit root) OK — `scripts/check.sh
  Jacobian/JacobianConstruction` passes: builds clean, **zero sorries** across all 8 files
  (1356 lines total, above the design's ~750-line estimate mainly due to `Torus.lean`'s
  `LieAddGroup`/`inducedHom` sections and `OfCurve.lean`'s fully-proved `ofCurve_contMDiff`, both
  of which the design correctly flagged as the highest-effort items but which landed complete
  rather than needing the design's fallback/blocker routes). Ledger as built: unconditional now —
  `AddCommGroup`/`TopologicalSpace`/`T2Space (Jacobian X)` (every genus), `ofCurve`/
  `ofCurve_eq_of_path`/`ofCurve_self`; needs `[DiscreteTopology (periodSubgroup X).topologicalClosure]`
  only to typecheck (not a real extra mathematical hypothesis once period-lattice-rank lands its
  global instance) — `ofCurve_contMDiff`, `Jacobian.inducedHom`/`contMDiff_inducedHom`; gated
  `instance`s needing that same hypothesis (+ `IsZLattice` for compactness) —
  `ChartedSpace`/`IsManifold`/`LieAddGroup`/`CompactSpace (Jacobian X)`. NOT registered in
  `Jacobian.lean` per task hard rule, orchestrator to add `import Jacobian.JacobianConstruction`.
  Notes for downstream units: **abel-theorem** consumes `ofCurve`/`ofCurve_eq_of_path`/
  `ofCurve_self`/`periodSubgroup`/`AddSubgroup.subset_closure` and is the natural home for the
  real `pushforward`/`pullback` (blueprint gap, see `Functorial.lean`'s entry above);
  **period-lattice-rank** consumes the abstract layer (`Torus.instChartedSpace`/
  `isManifold_torus`/`lieAddGroup_torus`/`compactSpace_torus`) and need only register
  `DiscreteTopology (periodSubgroup X).topologicalClosure` (+ `IsZLattice ℝ
  (periodSubgroup X).topologicalClosure.toIntSubmodule`, bridged automatically to the
  `AddSubgroup`-level hypothesis via `RS.discreteTopology_toIntSubmodule`) as instances for the
  real period subgroup to light up all four gated instances plus `ofCurve_contMDiff`/
  `Jacobian.inducedHom` at once; also needs to show `closure Λ = Λ` (discrete ⇒ closed, not built
  here, flagged in the design as period-lattice-rank's own small lemma); **jacobian-functoriality**
  (if such a unit exists/is created) consumes `Functorial.lean`'s substrate directly.
- [cech] Jacobian/Cech/Window.lean OK (238 lines, ~6s) — ordGe (Submodule, order-≥-m germs), meromorphicOnX_tailGerm + tailGerm + ord_tailGerm_self (chart-transport meromorphy via `meromorphicAtX_iff_of_mem_source` + mathlib's `meromorphicOrderAt_zpow_id_sub_const`), leadCoeff (one-step leading-coefficient functional, D7), WindowAt (+mk/mk_eq_zero_iff), diffSupp/mem_diffSupp_iff, Window, windowMap (+apply/eq_zero_iff), exact_inclusion_windowMap, inclusion_injective (via mathlib's `Submodule.inclusion_injective`). Zero sorries. DEFERRED (documented in-file): `finrank_windowAt`/`finrank_window` (θ-basis induction, design §6.8) and the `FiniteDimensional` instances that depend on them — did not fit the time budget; every other export is proved and does not depend on them.
- [cech] Jacobian/Cech/Skyscraper.lean OK (171 lines, ~18s, 2 declarations need `set_option maxHeartbeats 1000000`) — C1.MemLD/C1.retype(+apply_coe/mem_Z1), **mlClass (the Mittag-Leffler atom, explicitly requested)**, mlClass_add/mlClass_smul (linearity), H1Incl_mlClass (D-functoriality vanishing), mlClass_eq_zero_of_exists (the `⇐` half of the vanishing criterion — realized-by-a-global-section classes vanish; needs no injectivity). Zero sorries. DEFERRED (documented in-file/docstring): the full six-term exactness (`windowConnect`, `exists_realization`, Lemma A, `exact_windowMap_windowConnect`, `exact_windowConnect_H1Incl`, `H1Incl_surjective`) and the `⇒` half of `mlClass_eq_zero_iff` — both need adapted-cover realization machinery and/or `toH1_injective` (12.4) beyond the time budget.
- [cech] Jacobian/Cech.lean (unit root) OK (38 lines; `scripts/check.sh Jacobian/Cech` passes, zero sorries across all 7 files — unit COMPLETE modulo the two documented gaps: Forster 12.4 `resH1_injective`/`toH1_injective`, and the window/skyscraper dimension counts + full six-term realization machinery). NOT registered in `Jacobian.lean` per task hard rule, orchestrator to add `import Jacobian.Cech`. Total 1728 lines across Covers(355)/Cochains(244)/H0(143)/Refinement(261)/Colimit(278)/Window(238)/Skyscraper(171)/root(38).
- [mtrace] Jacobian/MeromorphicTrace/PlanarTrace.lean — **P6 sorry CLOSED** (`laurentCoeffAt_traceZk`, the unit's one admitted goal; file now 705 lines, zero sorries). Route: neither of the file's two recorded candidate routes verbatim, but a sharpening of route (b) that eliminates its "second ~100-line growth bound" entirely: (1) NEW export `traceZk_zpow` — closed form `traceZk (·^e) k w = k·w^(e/k)` if `k ∣ e` else `0` (`w ≠ 0`), proved on the abstract root set via one root (`RS.exists_pow_eq`) + a primitive `k`-th root of unity enumerating the root set (`bijOn_pow_mul_root`, private; `IsPrimitiveRoot.injOn_pow_mul` + ncard pigeonhole) + `geom_sum_eq` collapse — purely algebraic, no branches/analyticity; (2) exact finite Taylor remainder `u = P + (·)^M·r` (`RS.AnalyticAt.exists_taylor_remainder`) with the cutoff `M` chosen so `n₀ + M = k·s'` is an EXACT multiple of `k` with `s' > m` — then per root `z^(n₀+M) = (z^k)^{s'} = w^{s'}` EXACTLY, so the remainder trace factors as `w^{s'}·traceZk r k w` with NO growth bound (this divisibility trick is the whole insight; route (b) as previously sketched budgeted 100+ lines for a P5-style bound here); (3) `exists_analyticAt_traceZk` (private) — analytic (not just meromorphic) repair of `traceZk` of a bounded analytic function at `0`, the trivial-bound specialization of P5's removable-singularity argument; (4) all coefficients read off via residue-calculus's presentation-independent `laurentCoeffAt_of_eventuallyEq` + linearity/shift API (`laurentCoeffAt_fun_sum/_const_mul/_zpow_monomial`), final index bookkeeping by `Finset.sum_ite_eq'` + `linarith` (products `k*m`, `k*s'` as atoms — omega can't, linarith can). Also added `resAt_traceZk` (design §4.4 residue corollary, one-liner from P6). Design §4.4's `ordAt_traceZk_ge` remains unstated: not consumed by form-trace-tower's frozen design, flagged by mtrace's own design as a mere "bank" item with a caveat that equality fails. GOTCHA: `congr 1` discharges subgoals by `assumption` — a bulleted `· exact hzM` after it dies with "No goals to be solved" if `hzM` is already in context; fold the hypothesis into the preceding `rw` instead.
- [mtrace] Jacobian/MeromorphicTrace/FunctionTrace.lean — **FunctionTrace COMPLETED** (design risk R1 resolved; file now 284 lines, zero sorries): `sum_traceZk_stack` (the `h`-weighted analogue of mapping-degree's `FiberStack.fiberMultSum_eq_sum`: for ANY stack `S` and ALL `y ∈ S.V`, the stack formula `∑ i, traceZk (h∘(S.A i).e.symm) (mult i) ((S.A i).e' y)` equals the naive fibre sum `∑ᶠ x ∈ F⁻¹{y}, h x`; engine: mapping-degree's private `bijOn_e` reproved verbatim as `bijOn_stack_e` since not exported there — orchestrator may want to de-private the original), `trace_eq_finsum` (trace = naive fibre sum wherever any stack exists — full well-definedness against the `Classical.choice`, NO holomorphy/nonconstancy hypotheses), `trace_eq_finsum'` (every point, via `exists_fiberStack`), `trace_eq_stack_sum` (read `trace` through an ARBITRARY stack on its whole `S.V` — exactly form-trace-tower's `resAtP1_trace_eq_sum` step-1 consumption shape), `trace_of_regular` (design §4.5 signature kept verbatim incl. the — now redundant — `IsRegularValue` hypothesis), and `meromorphicAtX_trace` (P7, the design centerpiece: fix one stack, planar pieces `MeromorphicAt 0` by P5 after `meromorphicAtX_iff_of_mem_source` chart transport at `(S.A i).e (S.pt i) = 0`, compose back through `(S.A i).e'` (maximal-atlas, `e' y₀ = 0`, `0 ∈ e'.target` open) via the same iff + `𝓝[≠]0`-congr, sum by `MeromorphicAt.fun_sum` under the definitional unfold of `MeromorphicAtX`, transport to `trace F h` on the open `S.V`). New import: `Jacobian.MappingDegree.Ramification` (for `IsRegularValue`). GOTCHA: `rw [← S.maps_pt_eq i]` on a goal mentioning `y₀` fails (motive not type correct — `y₀` occurs in `S : FiberStack F y₀`'s type); rewrite forward in a `have` about `F (S.pt i)` instead. `scripts/check.sh Jacobian/MeromorphicTrace` passes: **unit COMPLETE, zero sorries**; form-trace-tower fully unblocked (both its P6 gate and its `FunctionTrace` gate).
- [finiteness] Jacobian/Finiteness/Schwartz.lean OK (213 lines, ~10s) — pure Banach, zero project imports. `schwartz_finite_cospan` (the L. Schwartz perturbation lemma, cospan/span form: `u` surjective + `v` compact CLM between Banach spaces ⇒ finite-dim `S` with `∀ f, ∃ e, f - (u e - v e) ∈ S`), proved by mirroring mathlib's own `ContinuousLinearMap.exists_preimage_norm_le` proof texture verbatim (OMT first line, `finite_cover_balls_of_compact` net, geometric-series iteration with a parallel finite-dim "escape term" `s ∈ S`, telescoping, `tendsto_nhds_unique`); `finiteDimensional_of_cospan` (consumer wrapper via `Module.Finite.map` + `Submodule.topEquiv`); `FiniteDimensional.of_linearMap_ker_range` (the ker/quotient extension helper, spike-verified). Zero sorries.
- [finiteness] Jacobian/Finiteness/BddHolo.lean OK (330 lines, ~11s) — `BddHoloOn S : Submodule ℂ (↥S →ᵇ ℂ)` (BCF agreeing with a `ContMDiffOn ω` witness on `S`); `isClosed_bddHoloOn` via a from-scratch chart-local uniform-limit argument (`mem_closure_iff_seq_limit` + per-point chart transport through `Surface.Bridges` + `TendstoLocallyUniformlyOn.differentiableOn`, no reuse of Montel needed here), hence `CompleteSpace`; `restrictCLM` (norm ≤ 1, `LinearMap.mkContinuous`) + presheaf law `restrictCLM_restrictCLM`; germ bridges `toGerm`/`evalAt_toGerm`/`toGerm_restrict_comm` and `restrictGerm`/`toGerm_restrictGerm`/`restrictGerm_toGerm` (`[T2Space X][CompactSpace X]`). GOTCHA (recorded for future builders touching `Submodule`-wrapped existentials): a `def`-wrapped `LinearMap`/`Submodule` application (e.g. `toGerm S f`) is NOT reliably unfolded by either `rw` (syntactic keyed matching) or bare metavariable-from-expected-type unification during argument elaboration (`have h : (toGerm S f).foo = ... := lemma_about_mk ...` fails with "don't know how to synthesize implicit argument") — the robust fix is an explicit `rfl`-proved unfolding lemma (`toGerm_eq_mk`) rewritten in FIRST via `rw`, after which everything is syntactically `mk`-shaped. Zero sorries.
- [finiteness] Jacobian/Finiteness/CompactRestrict.lean OK (126 lines, ~8s) — `isCompactOperator_restrictCLM`: Montel compactness of `restrictCLM` for `S' ⋐ S ⊆ source (chartAt ℂ x₀)`, via `Φ : BddHoloOn S → C(K,ℂ)` (chart composite) + `isCompact_closure_montelFamily` (BUILT Montel) + `Ψ : C(K,ℂ) → (↥S'→ᵇℂ)` (`ContinuousMap.isometryEquivBoundedOfCompact` + `BoundedContinuousFunction.compContinuous`) + the generic Compat helper `isCompactOperator_of_isCompactOperator_val` (a CLM into a *closed* submodule is compact once its ambient-valued composite is, via `Subtype.isCompact_iff` + `Subtype.val '' preimage = K ∩ S`). Deviation from design's file-plan (documented in-file): the two *cocycle-level* compactness lemmas the design's §4.4 also lists (`isCompactOperator_resZ_UV`, `isCompactOperator_tradeCompact`) need `ShrinkChain`/`NZ1`/`tradeCompact` from `Chain.lean`, built *after* this file per the same file plan's stated build order — deferred to `Chain.lean`'s scope (further deferred there, see below). Zero sorries.
- [finiteness] Jacobian/Finiteness/Chain.lean OK (287 lines, ~12-14s) — `ShrinkChain X` (Forster's `𝔚⋐𝔙⋐𝔘⋐𝔘*` same-index chain, D3) + `ShrinkChain.nonempty` (iterates cech's `exists_chartDisk_closure_basis` 4× per point + finite subcover, reindexed by `Finset.equivFin` exactly as `Cech.Covers.exists_good_refinement_closure`); the four induced `FinCover ⊤`s + refinement facts (all `τ = id`); the Banach cochain layer `NC0`/`NC1` (finite `Pi`s of `BddHoloOn`), `deltaCLM` (0-to-1 coboundary), `NZ1` (bounded cocycles as `ContinuousLinearMap.ker` of an internal `d1NC` — closed+complete for free, no hand-rolled pointwise closedness); `resNC0`/`resNC1`, the cocycle-relation workhorse `NZ1.rel_res` + `resNC1_mapsTo_NZ1` (mirrors `Cech.Refinement`'s `Z1.rel_res`/`resC1_mem_Z1` almost verbatim, using the new `restrictCLM_restrictCLM` presheaf law), and `resZ` (via `ContinuousLinearMap.codRestrict`). **DEFERRED, honestly diagnosed** (`TODO(blocker)` note at file end, >45min spent): `tradeDefect`/`tradeSpace`/`tradePi`/`tradeCompact` (Forster 14.6(b)'s subspace `L` and its two Schwartz-cospan projections) hit a reproducible mathlib instance-resolution wall — `IsTopologicalAddGroup` on a `ContinuousLinearMap.ker`-valued `Submodule` (`NZ1 T T.U`) times out even at 4,000,000 `synthInstance` heartbeats (vs. the `CompleteSpace (NZ1 T P)` instance three declarations earlier, which DID respond to an 800,000-heartbeat bump) — a genuine performance/search-shape issue, not a missing lemma; two routes recorded for a continuation builder (targeted `trace.Meta.synthInstance` diagnosis, or reformulating `NZ1`'s carrier as a hand-rolled pointwise-condition `Submodule` per the design's original §2 D1 sketch). The two compactness lemmas deferred from `CompactRestrict.lean` remain deferred for the same reason (consume `tradeCompact`). Zero sorries.
- [finiteness] Jacobian/Finiteness.lean (unit root) OK (64 lines; `scripts/check.sh Jacobian/Finiteness` passes, zero sorries across all 4 written files, 1020 lines total). **PARTIAL UNIT — 4 of 7 design files written** (all gate-free ones, in the design's order). NOT registered in `Jacobian.lean` per task hard rule, orchestrator to add `import Jacobian.Finiteness`. NOT WRITTEN (not sorried): `TradeBounded.lean`, `H1Finite.lean`, `Chi.lean` — gated on the not-yet-built `dolbeault-comparison` unit's `Leray.lean` (`exists_trade`/`toH1_surjective_of_isGood`/`h1CoverEquiv`; no `Jacobian/DolbeaultComparison/` directory exists at all as of this session, though cech's `Colimit`/`Window`/`Skyscraper` DID land mid-session and are ready). Centerpieces delivered: `BddHoloOn` (BCF closed-submodule Banach spaces), `ShrinkChain` (four-level chains + existence), the Montel-compact `restrictCLM` operator, `schwartz_finite_cospan`. Notes for canonical-forms/riemann-roch: the χ ledger (`chi`, `chi_zero_add_degree_le_l`, `l_mono`, etc.) and the Riemann seed `chi 0 + deg D ≤ l D` are NOT yet available — they live in the undelivered `Chi.lean`; a continuation builder should finish `tradeSpace`/`tradePi`/`tradeCompact` (see Chain.lean's blocker note) first, then (once dolbeault lands) `TradeBounded.lean`→`H1Finite.lean`→`Chi.lean` per the design's §5–§8 proof plans, which remain unchanged and fully specified.
- [dbar] Jacobian/Dbar/Form01.lean OK (127 lines, ~7s) — `Form01 X` (design D5/D8): a plain
  structure (chartAt-indexed coefficient family for dz̄, junk-zero off chart targets, smooth on
  targets, anti-holomorphic transition law with `conj`), NOT a bundled `ContMDiffSection` (unlike
  Form1/CC1) since there is no anti-linear Hom-bundle in mathlib at the pin and the blueprint's
  `restrictScalars ℂ→ℝ` diamond warning rules one out. `ext`, `Zero/Add/Neg/Sub/SMul` instances,
  `AddCommGroup`/`Module ℂ` (via `ext` + `simp`/`ring`, no bundle machinery). Gotcha for sibling
  builders: `ω` (the `ContDiff` scope's top regularity-level token, from `open scoped ContDiff`)
  CANNOT be reused as an ordinary bound-variable name — `theorem ext {ω η : Form01 X} ...` is a
  PARSE ERROR ("unexpected token 'ω'"). Used `η, η'` for Form01-valued variables throughout
  instead (matching Forms' own `Form1` convention of `η`, not `ω`). Second gotcha: instance field
  proofs using anonymous-constructor lambdas (`fun x z hz => by rw [...]`) hit the usual
  lambda-vs-Pi-op unreduced-beta mismatch; fixed with a `dsimp only;` before the `rw` in each of
  the 8 spots (Add/Neg/Sub/SMul × 2 proof fields).
  `Form01CoeffData`/`Form01.ofCoeffs` (chart-family assembly, for `dolbeault-comparison`
  consumers) DEFERRED for time — not needed by anything inside this unit itself (only exported);
  flagged in the final report.
- [dbar] Jacobian/Dbar/Operator.lean OK (398 lines, ~7-9s) — `SmoothC X` (design D6, a private
  subtype `{f : X→ℂ // ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ f}` with hand-built `AddCommGroup`/`Module ℂ`,
  avoiding the `restrictScalars` diamond that mathlib's own bundled `ContMDiffMap` ring/module
  instances would hit for our target model `𝓘(ℝ,ℂ)`); intrinsic `dbar : SmoothC X →ₗ[ℂ] Form01 X`
  (chart-local `wirtingerDbar`); `IsDbarAt`/`IsDbarOn` (D7); `eqOn_coeffAt_of_isDbarOn` (the key
  chart-transition-transport lemma, underlies `dbar_eq_iff`,
  `contMDiffOn_omega_of_isDbarOn_zero`, `contMDiffOn_omega_sub_of_isDbarOn`); and the named
  centerpiece `exists_dbar_solution_chart_ball` (transports Forster 13.2 through a chart, using
  `Form01.compat` + the `(0,1)` chain rule to reconcile the target chart's coefficients with an
  arbitrary point's own preferred chart). THREE gotchas worth recording:
  (1) `contMDiffAt_real_iff_contDiffAt` (CC7, RealSmooth.lean) is stated via `extChartAt 𝓘(ℂ) x`,
  not `chartAt ℂ x` directly — but `(extChartAt 𝓘(ℂ) x : X→ℂ) = ⇑(chartAt ℂ x)` and
  `⇑(extChartAt 𝓘(ℂ) x).symm = ⇑(chartAt ℂ x).symm` are literally `rfl`, so `exact`/`show` against
  a `chartAt`-phrased goal works transparently; only `.target` needs a `simp` (not quite `rfl`).
  (2) Getting `ContDiffOn ℝ ∞ (f∘(chartAt x).symm) (chartAt x).target` from a GLOBAL `ContMDiff f`
  is easiest via composing `f.contMDiffOn` with mathlib's `contMDiffOn_extChartAt_symm` through
  `ContMDiffOn.comp`, then `contMDiffOn_iff_contDiffOn` — NOT via chasing "chart invariance of
  ContMDiffAt" per-point (that route needs its own separate transition-map argument, only used
  where a hypothesis is merely LOCAL `ContMDiffOn u s`, not global). (3) dependent
  `if h : p ∈ s then ... else ...` inside a `noncomputable section` still needs a `classical`
  tactic call (or an ambient `Decidable` instance) even though the SECTION is noncomputable —
  `noncomputable` alone does not supply `Decidable`. Zero sorries.
- [dbar] Jacobian/Dbar/PlanarPoU.lean OK (139 lines, ~5s) — finite smooth PoU on a planar open
  set `V` subordinate to a finite open cover (design R5): shrink the cover in the (automatically
  normal, being metrizable) subtype `↥V` via mathlib's `exists_subset_iUnion_closure_subset`,
  push shrunk pieces back to `ℂ` (`IsOpen.isOpenMap_subtype_val`, `closure_subtype`), one bump
  per piece via `IsOpen.exists_contDiff_support_eq` (exact `support`, not just containment), then
  normalize by the sum (positive on `V` since the shrunk pieces still cover `V`). Confirmed via an
  upstream investigation that mathlib's manifold `SmoothPartitionOfUnity` API is the WRONG tool
  here (needs a closed base set, bundles into `M→ℝ` smooth maps) — the from-scratch route was the
  right call. Also provides `contDiffOn_indicator_smul_of_eventually_zero` (extension-by-zero
  helper used by `PlanarCousin.lean`). Zero sorries.
- [dbar] Jacobian/Dbar/PlanarCousin.lean OK (115 lines, ~5-8s) — planar Cousin atoms (Forster
  12.6/13.4): `exists_smooth_splitting` (PoU-weighted average splits a smooth additive cocycle on
  a finite cover of an open set — `H¹ = 0` for the sheaf of smooth functions) and
  `exists_holo_splitting_ball` (corrects the smooth splitting by a `∂̄`-solution from
  `SolveDisk.exists_dbar_solution_ball` to land on a HOLOMORPHIC splitting on a ball — disk
  Cousin I). Gotcha: several steps mix `ℝ`-scalar (`ψ`) against `ℂ`-valued (`f`) arithmetic where
  neither `ring` nor `linarith` apply directly (`ring` doesn't cross the `smul` boundary,
  `linarith` needs an order which `ℂ` lacks) — `module` (for the smul identity) and
  `linear_combination` (for the plain `ℂ`-equation rearrangements) are the right tactics instead.
  Zero sorries.
- [finiteness] Chain.lean trade decls FIXED (file now 401 lines, zero sorries; `scripts/check.sh Jacobian/Finiteness` passes) — `tradeDefect`/`tradeSpace`/`tradePi`/`tradeCompact` (Forster 14.6(b)'s subspace `L ⊆ Z¹(𝔘)×Z¹(𝔙)×C⁰(𝔚)` and its two Schwartz-cospan projections) delivered in the design §4.2 shapes VERBATIM (`tradeDefect := res_UW∘pr₁ − res_VW∘pr₂ − δ_W∘pr₃` as a CLM difference, `tradeSpace := (tradeDefect T).ker`, `tradePi = pr₂∘subtypeL`, `tradeCompact = resZ_UV∘pr₁∘subtypeL`), plus consumer API: `tradeDefect_apply` (rfl), `mem_tradeSpace_iff` (defect components vanish), `mem_tradeSpace_iff_eq` (Forster's `ζ = ξ + δη` per-`𝔚`-pair rearrangement, §5-step-2 shape), `tradePi_apply`/`tradeCompact_apply` (rfl), `CompleteSpace`/`NormedAddCommGroup`/`NormedSpace ℂ` instances on `↥(tradeSpace T)`, and `ShrinkChain.W_le_V`/`V_le_U`/`U_le_Ustar`/`W_le_U` (`Opens`-level `≤` forms). **ROOT CAUSE of the recorded blocker (gotcha for future units)**: NOT actually an `IsTopologicalAddGroup` timeout — the `Sub`-of-CLMs instance (`ContinuousLinearMap.sub`, needed to write the defect as `A − B − C`) re-synthesizes `AddCommGroup ↥(NZ1 …)` as a nested subgoal and must then defeq-check its `AddCommGroup.toAddCommMonoid` against the `Submodule.addCommMonoid` already baked into the goal's CLM type; the blind search finds the group instance along a non-canonical path (BCF-`instRing`-flavored) whose defeq check is REJECTED, so the candidate fails no matter the heartbeat budget (bumping to 4M could never help — it was a rejection, not a timeout; the previously reported `IsTopologicalAddGroup ↥(NZ1 T T.U)` failure was this same storm surfacing one class higher). FIX: register canonical shortcut instances right after `NZ1` — `noncomputable instance : AddCommGroup (NZ1 T P) := (NZ1 T P).addCommGroup`, ditto `IsTopologicalAddGroup := .topologicalAddGroup`, `NormedAddCommGroup := .normedAddCommGroup`, `NormedSpace ℂ := .normedSpace` — after which the design-shape `Sub` elaborates with an ordinary `synthInstance.maxHeartbeats 1000000` bump (`800000` on the ker/normed instances). Same shortcuts registered for `↥(tradeSpace T)`. RULE OF THUMB: for any `Submodule`-of-`Pi`-of-`Submodule`-typed carrier consumed by CLM combinators, pre-register the canonical `Submodule.*` structure instances by hand; bare `Pi`-of-`BddHoloOn` levels (`NC0`/`NC1`) need nothing. DOWNSTREAM VERIFIED (scratch, this session): `RS.schwartz_finite_cospan (u := tradePi T) (v := tradeCompact T)` and `RS.finiteDimensional_of_cospan` both type-check against the new declarations (800k bump), and element-level `Sub` on `↥(NZ1 T T.V)` works — TradeBounded/H1Finite §5/§6.5 consumption shapes viable as designed; `mem_tradeSpace_iff_eq` is the §5-step-2/6/8 workhorse. STILL DEFERRED (not instance-blocked; TradeBounded-gate work): design §4.4's `isCompactOperator_resZ_UV` (finite-`Pi` Montel assembly of CompactRestrict's single-chart lemma, §6.3 step 5) and `isCompactOperator_tradeCompact` (that + `IsCompactOperator.comp_clm` through `pr₁∘subtypeL`). Docstrings updated in `Chain.lean` (blocker note replaced by a resolution post-mortem) and `Finiteness.lean` (unit root).
- [dbar] Jacobian/Dbar/DiskAcyclic.lean OK (235 lines, ~7-9s) — disk acyclicity of `𝒪_D` (design
  D9, §4.8, §7.4), depending on sibling units `Jacobian.Cech.{Cochains,Refinement}` and
  `Jacobian.Meromorphic`. DELIVERED: the `D = 0` case (`subsingleton_h1Cover_zero_of_isChartDisk`,
  "no compactness needed") — every additive holomorphic cocycle on a finite cover of a chart disk
  splits: holomorphic germ representatives (`MeroGermOn.holoRepr`) transported through the chart,
  pointwise cocycle identity assembled from cech's `Z1.rel_res` + `MeroGermOn.evalAt_restrict`,
  `PlanarCousin.exists_holo_splitting_ball` applied, pulled back to `X`, and reassembled into a
  `C0` cochain witnessing `f ∈ B1` via `MeroGermOn.mk_holoRepr`/`mk_add`/`mk_neg`/`restrict_mk`.
  Also two Compat helpers (`meromorphicOnX_of_contMDiffOn_omega`, `mk_mem_linSysOn_zero`).
  DEVIATION (honestly reported, matches the design's own R3 risk call): the general-divisor twist
  (`subsingleton_h1Cover_of_isChartDisk`, `[T2Space X][CompactSpace X]`, the finite-product
  twisting germ) is NOT included — a substantial independent construction (twisted cochain maps
  commuting with `d0`/`d1`/`restrictL`) that did not fit the remaining time budget; see the final
  report. GOTCHAS for sibling builders: (1) cech's `FinCover`/`IsChartDisk`/`C0`/`Z1`/`B1`/
  `H1Cover`/`d0`/`Z1.rel_res`/`subsingleton_h1Cover_iff` all live in `namespace RS.Cech` (NOT bare
  `RS`) — need `open Cech` (inside `namespace RS`) or full `RS.Cech.` qualification; `LinSysOn`/
  `MeroGermOn`/`Divisor`/`MeromorphicOnX` are bare `RS` (from `mero`). (2) dot-notation
  (`h.foo`) immediately after an intermediate `.contMDiffAt`/similar call can fail to resolve
  ("environment does not contain X.foo") even with an explicit `have h : ContMDiffAt ... := ...`
  type ascription, because manifold defs like `ContMDiffAt`/`ContMDiffWithinAt` are reducible and
  Lean's dot-notation dispatch sees through them to the unfolded `LiftPropWithinAt` head; fixed by
  calling the FULL declaration name as a normal function (`ContMDiffAt.meromorphicAtX h2`) rather
  than dot notation. (3) `MeroGermOn.ord_restrict`/`evalAt_restrict`'s `(hV : IsOpen V) (hU :
  IsOpen U)` argument order is "smaller set first, bigger set second" (`restrict (h : V ⊆ U)`
  narrows FROM `U` TO `V`) — easy to get backwards when `V` is a nested `⊓`-intersection and `U`
  looks "more complex" than `V`. (4) `congrArg (fun g => MeroGermOn.evalAt g p) hEq` leaves an
  unreduced `(fun g => g.evalAt p) lhs = (fun g => g.evalAt p) rhs` that plain `rw` cannot see
  through (needs `dsimp only at` first, the usual lambda-vs-application beta trap). Zero sorries
  in the delivered `D = 0` theorem.
- [canon] Jacobian/CanonicalForms/MForm.lean OK (266 lines) — `MForm X` (D1, `chartAt`-indexed
  coefficient family, `MeromorphicOn` coefficients, `deriv τ` transition rule with **no**
  conjugate — mirrors dbar's `Form01` but type `(1,0)` not `(0,1)`); `MForm.ext`,
  `Zero/Add/Neg/Sub/SMul ℂ/AddCommGroup/Module ℂ` (D2, pointwise, same proof shape as
  `Form01`'s own instances); `MFormCoeffData`/`MForm.ofCoeffs` (D3, mirrors
  `Form1CoeffData`/`Form1.ofCoeffs` but SIMPLER — no bundle/covector layer needed since `MForm`
  isn't a bundled section — built via a from-scratch `rawCoeffAt`/`rawCoeffAt_eq` master-transport
  lemma reusing `deriv_trans_comp`/`analyticAt_trans` (`Jacobian.Forms.Analyticity`) directly, no
  mfderiv/tangentCoord defeq-crossing needed at all). Zero sorries. GOTCHA for siblings: `ω` is a
  reserved `ContDiff`-scope token (the smoothness level) and cannot be reused as an ordinary
  identifier once `open scoped ContDiff` is in effect — used `θ`/`η` for `MForm`/`Form1` variables
  throughout the unit instead of the design doc's own `ω`/`ω₀` notation (a blind rename hits real
  parse errors, not just style; Form01's docstring already flags this, worth a note in
  `CONVENTIONS.md` for future builders). Also: `MeromorphicOn.const`'s `U` is an *implicit* named
  arg (`{U : Set 𝕜}`), not positional — passing it positionally silently unifies wrong metavariables
  (`NontriviallyNormedField (Set ℂ)` synthesis failures) instead of erroring cleanly; use
  `MeromorphicOn.const (U := ...) c` or ascribe the type via a `have`.
- [canon] Jacobian/CanonicalForms/OrdRes.lean OK (234 lines) — `MForm.ord`/`MForm.resAt` (D4, read
  via fixed `chartAt`), chart-invariance corollaries `ord_eq_of_mem_source`/`resAt_eq_of_mem_source`
  (via mathlib's `meromorphicOrderAt_comp_of_deriv_ne_zero` / built `resAt_comp_mul_deriv`);
  the cross-point transport helper `coeffAt_eventuallyEq_of_mem_source` (new, `compat` read as a
  neighborhood-level congruence — the engine behind both propagation lemmas below, reusable);
  `eventually_ord_eq_top`/`eventually_ord_eq_zero` (mirrors `eventually_ordAtX_eq_top`/
  `eventually_ordAtX_eq_zero`, `Predicates.lean:231/314`, with the extra chart-crossing layer
  `MForm` needs that a bare global `ordAtX f` does not); `MForm.divisor`/`.degree` (D6, local
  finiteness connectedness-free, mirrors `MeroGermOn.divisorOn`'s case split exactly). Zero
  sorries. DEFERRED (documented in `Jacobian/CanonicalForms.lean`'s root docstring, NOT sorried):
  `MForm.eq_zero_or_forall_ord_ne_top` (D5) — see the root docstring for the full writeup; briefly,
  `meromorphicOrderAt f z₀ = ⊤` is a *punctured*-neighborhood fact (`f =ᶠ[𝓝[≠]z₀] 0`) and places no
  constraint on `f z₀` itself, so "`ord = ⊤` everywhere ⟹ `θ = 0`" (`MForm.ext`-level, literal
  pointwise equality) does not follow from order data alone without a canonical/junk-free
  representative that `MForm` does not carry. This blocks `OneDimensional.lean` (D8) entirely (not
  written) and cascades to D10/D11's second half/D12 — see root docstring.
- [canon] Jacobian/CanonicalForms/Differential.lean OK (236 lines) — `deriv_comp_chart_congr` (+
  helper `differentiableAt_comp_chart_of_mem_source`), the unit's central risk item (P1),
  compiled essentially as spike-verified (`scratch_canon.lean` item 4) with a `by_cases` +
  symmetric-argument assembly, ~45 lines, matching the design's own estimate exactly; `deriv_comp`'s
  product comes out commuted from the design's stated order, needs a trailing `ring`. `ofForm1`/
  `Form1.toMForm`/`ofForm1_ord_nonneg` (D7, holomorphic embedding, `compat` = `coeffIn_trans`
  verbatim); `MForm.smul`/`SMul (ℳ X) (MForm X)`/`coeffAt_smul_mero` (via `holoRepr`, chart-crossing
  meromorphy via `meromorphicAtX_iff_of_mem_source`); `MForm.d`/`coeffAt_d` (compat =
  `deriv_comp_chart_congr` instantiated at `g := f.holoRepr`, essentially free once the general
  lemma was in hand); `MForm.d_const`; `MForm.dlog`. Zero sorries. DEFERRED (documented in-file and
  in the root docstring, NOT sorried): `MForm.smul`'s module laws (`smul_add`/`add_smul`),
  `MForm.d_add`/`d_eq_zero_iff`, `MForm.resAt_dlog` — these need
  `(f+g).holoRepr = f.holoRepr + g.holoRepr` pointwise, which genuinely FAILS at poles of the
  summands (`evalAt_add`, `OrderEval.lean:168`, only holds when *both* summands have `0 ≤ ord`) —
  the additive analogue of D5's junk-value issue. `d`/`dlog` themselves are unaffected (built from
  `holoRepr` directly, no summation).
- [canon] Jacobian/CanonicalForms/LinearSystems.lean OK (112 lines) — `MForm.OmegaSpace`/
  `mem_omegaSpace_iff`/`MForm.i` (D11, first half only — defined ORDER-WISE, mirroring `LinSys`'s
  own primary definition, rather than the design's divisor-level disjunctive carrier, specifically
  so submodule closure reduces to two new small order-arithmetic lemmas `MForm.ord_add`/
  `MForm.ord_smul` built here — junk-robust, no issue); `MLFormData`/`.Realizes`/`.totalRes`/
  `.Realizes.resAt_eq` (D13, thin wrapper around residue-calculus's `PrincipalPartData`, using
  `Finset.attach` to carry the dependent membership proof through the sum in `totalRes` — `‹_›`
  anonymous-hypothesis search does NOT find `∀ x ∈ s, ...`'s own binder inside a `def`, use a named
  `hx` argument instead). Zero sorries. DEFERRED (documented in-file and root docstring, NOT
  sorried): `Ω_iso_linSys`/`i_eq_l_add_canonicalDivisorOf` (need `canonicalDivisorOf`, D10, itself
  blocked on D8/D5) and `holomorphicMFormsEquiv`/`genus_eq_finrank_omegaSpace_zero` (D12 — its
  *backward* direction hits the SAME junk-value issue as D5 independently, design's own §7 item 2
  risk, sharper than stated there).
- [canon] Jacobian/CanonicalForms.lean (unit root) OK (82 lines; `scripts/check.sh
  Jacobian/CanonicalForms` passes, zero sorries across all 4 written files, 930 lines total).
  NOT registered in `Jacobian.lean` per task hard rule, orchestrator to add
  `import Jacobian.CanonicalForms`. Centerpieces delivered: `MForm X` (D1, chart-family structure)
  + `ord`/`resAt`/`divisor` (D4/D6, chart-invariance + connectedness-free local finiteness) +
  `MForm.d`/`dlog` (D7, the pole-case-split `compat` — the unit's flagged top risk — fully closed)
  + the `Form1 ↔ MForm` holomorphic embedding (D7/D12 forward half) + `OmegaSpace`/`i`/`MLFormData`
  (D11/D13 gate-independent halves). NOT delivered (documented above, filed as genuine findings
  rather than time-outs): the global zero-dichotomy `eq_zero_or_forall_ord_ne_top` (D5) — a
  substantive junk-value subtlety in representing meromorphic 1-forms via raw chart coefficients
  rather than germ classes, discovered during this build, not merely a missing computation — and
  everything downstream of it (`OneDimensional.lean`/D8, `canonicalDivisorOf`/D10, `Ω_iso_linSys`/
  D11-second-half, `holomorphicMFormsEquiv`/D12); `Existence.lean`/D9 (gated on
  `Jacobian/Finiteness/`'s `Chi.lean`, not on disk — per task instructions left unwritten, not
  sorried). Filed `docs/requests/meromorphic-and-divisors.md` item 6 (`Divisor.single`/
  `degree_single`, needed by the unwritten `Existence.lean`). Notes for consumers: **laurent-tails**
  gets `MForm`/`OmegaSpace`/`i`/`MLFormData` (its stated D11/D13 needs) but NOT `canonicalDivisorOf`
  — will need to either fix its own reference `ω₀`/`K` directly (any `θ₀ ≠ 0 : MForm X` obtained
  by other means) or wait for D5/D8/D10 to land; **residue-theorem** gets `MForm`/`resAt`/
  `resAt_eq_of_mem_source`/`divisor` in full (no gap); **serre-duality-cech**/**riemann-roch**
  will need D10/D11-second-half/D12 landing first — flagged as the key remaining gap for the
  Riemann–Roch chain, distinct from (and in addition to) the finiteness-and-chi gate.
- [dbar] Jacobian/Dbar.lean (unit root) OK (28 lines; `scripts/check.sh Jacobian/Dbar` passes,
  zero sorries across all 8 files — unit COMPLETE except the honestly-deferred general-divisor
  twist in DiskAcyclic.lean, see that file's entry above). Total 2190 lines across
  Wirtinger(243)/CauchyKernel(451)/SolveDisk(429)/Form01(121)/Operator(437)/PlanarPoU(135)/
  PlanarCousin(139)/DiskAcyclic(235)/root(28). NOT registered in `Jacobian.lean` per task hard
  rule, orchestrator to add `import Jacobian.Dbar`. Notes for consumers: **dolbeault-comparison**
  is the primary consumer (per the design doc) — it should reuse `Form01`/`dbar`/`IsDbarOn`/
  `exists_dbar_solution_chart_ball` directly for its `H^{0,1}` Dolbeault-vs-Čech comparison, and
  will likely want `Form01CoeffData`/`Form01.ofCoeffs` (assembling a global `(0,1)`-form from
  local chart data) which this unit did NOT deliver (deferred, see Form01.lean's entry) — a
  straightforward `conj`-decorated transcription of Forms' `Form1CoeffData`/`coeffInFun_toSection`
  pattern (`Jacobian/Forms/OfCoeffs.lean`) using `analyticAt_trans`/`deriv_trans_comp`
  (`Jacobian/Forms/Analyticity.lean`), per design §7.3. **finiteness-and-chi** may want
  `exists_dbar_solution_ball`/`exists_holo_splitting_ball` for any planar Cousin-style
  Banach-space work, though its current blocker (dolbeault's `Leray.lean`) is unrelated to this
  unit. Any consumer needing the FULL (non-chart-disk) `H¹(X, 𝒪_D) = 0` Čech-cohomological
  vanishing for GENERAL divisors `D` on general covers still needs the deferred
  `subsingleton_h1Cover_of_isChartDisk` (general-divisor twist) — not delivered.
- [mono] Jacobian/Monodromy/OpenLocus.lean OK (88 lines, ~5s) — the open pole/zero-free locus
  relativization engine: `openLocus`/`openLocusOfFinite` (closed/finite bad set ↦ `Opens X`),
  `Path.liftOpenLocus`/`.liftOpenLocus_extend`. Confirms design's central risk resolved for free:
  `ChartedSpace ℂ`/`IsManifold 𝓘(ℂ) ω` on an `Opens X` resolve by bare `inferInstance`
  (`TopologicalSpace.Opens.instChartedSpace` + its derived `IsManifold` instance), so `Path/`'s
  entire per-path API (`IsPrimitiveAlong`, `exists_isPrimitiveAlong`, `pathIntegral`, …) applies to
  the locus by direct instantiation — matches `scratch_mono.lean`'s spike, no wrapper layer needed.
  Gotcha (Lean, not math): `Path.foo` declared inside `namespace RS.Monodromy` is NOT found by dot
  notation (`γ.foo`) since `Path` is a mathlib root-namespace type and dot-notation resolves the
  literal declared namespace of the type's head symbol, not the caller's enclosing namespace
  (unlike plain identifier resolution, which does search ancestor namespaces) — call these by the
  qualified name `Path.foo γ ...` instead. Zero sorries.
- [mono] Jacobian/Monodromy/LogContinuation.lean OK (302 lines, ~9s) — the DAG-critical
  deliverable: `poleZeroLocus f` (pole/zero-free open locus of `f : ℳ X`), `dlogForm f hf : Form1
  (poleZeroLocus f)` (the `df/f` logarithmic-derivative 1-form), `exp_eq_holoRepr_of_isPrimitiveAlong`
  (any primitive of `dlogForm`, normalized at the start, is an honest continuous branch of `log f`:
  `exp (F t) = f.holoRepr (γ.extend t)`), `exists_logBranchAlong`/`logBranchAlong_unique`
  (existence with prescribed initial value / uniqueness, both citations of `Path`'s own
  existence/`sub_eq_sub` API). DEVIATION from the design doc's literal proof plan: `dlogForm` is
  built by *reusing* `Jacobian/Forms/MDifferential.lean`'s `RS.mdifferential`/`RS.Form1.smulFun`
  (both already proved generically over any surface satisfying the standing hypotheses),
  instantiated with `X := poleZeroLocus f`, rather than hand-rolling a `Form1CoeffData` with
  shrunk-ball charts + a manual chart-transition/`subtypeRestr` compat computation as the design
  sketched — `f.holoRepr` restricted to the locus is `ContMDiff` (mathlib's `contMDiffAt_subtype_iff`,
  a per-point statement — smoothness of an open-submanifold restriction needs no shrinking) and
  nonvanishing everywhere on the locus BY CONSTRUCTION (no continuity-propagation/ball-shrinking
  argument needed either), so the whole `Form1CoeffData` route (and its `dlogCoeffAt`/chart-overlap
  compat lemma) turned out to be unnecessary; `ContMDiff.inv₀` (`Mathlib.Geometry.Manifold.Algebra
  .LieGroup`, needs a `ContMDiffInv₀` instance for `ℂ` — present generically for any
  `NontriviallyNormedField`) gives the inverse's smoothness for `Form1.smulFun`. Result: shorter,
  and it sidesteps the design's flagged R2 risk (order-zero-iff-nonvanishing lemma name) by a
  different, self-contained route (`AnalyticAt.meromorphicNFAt` +
  `MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff`, `Mathlib.Analysis.Meromorphic.NormalForm`).
  GOTCHA (real Lean elaboration hazard, cost ~1hr): using `Path.liftOpenLocus (finite_support_divisor
  f).isClosed γ hγ` directly (typed in `openLocusOfFinite (finite_support_divisor f)`) alongside
  `dlogForm f hf : Form1 (poleZeroLocus f)` in the SAME theorem signature causes a `synthInstance`
  failure for `IsManifold … ↥(openLocus ⋯)` — even though each half resolves fine in isolation, and
  even marking `poleZeroLocus` `@[reducible]` does not help (confirmed by `trace.Meta.synthInstance`:
  the ChartedSpace instance candidate gets built against the WRONG (defeq but syntactically
  different) locus expression). FIX: a thin dedicated `Path.liftPoleZeroLocus`/`_extend` (not
  routed through `Path.liftOpenLocus` at all) landing directly in `poleZeroLocus f` syntactically —
  once the two occurrences of "the locus" in a signature are the SAME term, the problem disappears.
  Record this pattern for any future unit combining a `def`-wrapped `Opens X` with a
  path-lifting/subtype-construction helper of a MORE GENERAL underlying tool. Zero sorries.
- [mono] Jacobian/Monodromy.lean (unit root) OK (67 lines, ~4s; `scripts/check.sh
  Jacobian/Monodromy` passes, zero sorries — unit COMPLETE). NB: `Jacobian.lean` was NOT touched
  (out of scope per this builder's hard rules) — the root import registration is left for
  whoever assembles `Jacobian/Challenge.lean` / integrates units, or a future pass.
- [cech] Continuation pass on `Jacobian/Cech/` — closed two of the three deferred gaps in full,
  the third partially. `scripts/check.sh Jacobian/Cech` passes: builds clean, **zero sorries**
  across all 10 files + root (2528 lines, up from 1728). New files: `Injectivity.lean` (269),
  `WindowRank.lean` (347), `SixTerm.lean` (97); minimal docstring-only edits to
  `Refinement.lean`/`Colimit.lean`/`Window.lean`/`Skyscraper.lean` to retarget their "deferred"
  notes at the new files (no proof code in those four files was touched).
  1. **Forster 12.4 injectivity** (`Injectivity.lean`) — **CLOSED**. `resH1_injective` via the
     sheaf-axiom gluing plan (§6.7): `injPatch`/`injPatch_compat` (the local candidate
     `f(i,τk) − g(k)` and its overlap compatibility, proved via `Z1.rel_res` at a constructed
     meet-of-opens `Wraw`, exploiting that `Opens.⊓`'s coercion is *the same term* as `Set.∩`
     by `rfl` so Set-level and Opens-level inequality proofs interchange freely),
     `exists_injGlue` (`MeroGermOn.exists_glue` assembly per member `𝒰.U i`),
     `d0_injGlue_eq_neg` (the glued cochain is a coboundary witness for `−f`, a harmless sign
     artifact of `injPatch`'s convention — resolved by witnessing `B1` with `−ψ`). Then
     `toH1_injective`/`toH1_eq_zero_iff`/`subsingleton_H1_iff` via
     `Module.DirectLimit.exists_eq_of_of_eq` + `resH1_injective` (deliberately avoided
     `of.zero_exact`+subtraction: `AddCommGroup (H1 D)`/`AddGroup (H1 D)` fails plain
     `inferInstance` in this codebase — a genuine higher-order-instance gap in resolving
     `∀ 𝒰, AddCommGroup (H1Cover D 𝒰)` for `Module.DirectLimit`'s `addCommGroup` instance; the
     subtraction-free `exists_eq_of_of_eq` route sidesteps it entirely). **Bonus**: the `⇒` half
     of `mlClass_eq_zero_iff` (added to `Skyscraper.lean`, needs `D ≤ D'` as an explicit
     hypothesis not shown in the design's abbreviated pseudocode) — via `toH1_injective` +
     `H0.lean`'s `toC0'_surjective` gluing, exactly per design §6.9(b).
  2. **Window dimension counts** (`WindowRank.lean`) — **CLOSED**, but via a *different* proof
     route than design §6.8's planned `θ`-basis/`Basis.mk` independence-and-spanning argument:
     that argument needs `leadCoeff p m` defined on the *whole* numerator `ordGe p (-d')` for
     every index `m` simultaneously, but `leadCoeff p m`'s domain is `ordGe p m` — only the
     bottom index `m = -d'` has domain literally equal to the numerator. Route taken instead: an
     explicit one-step splitting `WindowAt p d d' ≃ₗ WindowAt p d (d'-1) × ℂ` via
     `LinearMap.quotKerEquivRange` on a "subtract off the leading term at `-d'`" map
     (`rawCorr`/`corrMap`/`bigMap`), then induction on `(d'-d).toNat` (base case: `d'=d`, cover
     is a subsingleton by an `ord_add`/`ord_neg` argument; successor: the splitting +
     `Module.finrank_prod` + `Module.finrank_self`). Needed two Compat lemmas not upstreamed
     from meromorphic-and-divisors (filed in `docs/requests/meromorphic-and-divisors.md`):
     `tendsto_zero_iff_ordAtX_pos` and `MeroGermOn.evalAt_eq_zero_iff`, both chart-transported
     from mathlib's `tendsto_zero_iff_meromorphicOrderAt_pos`; from those, `leadCoeff_eq_zero_iff`
     (leadCoeff detects the exact order) and `leadCoeff_tailGerm_self_ne_zero` (nonzero, NOT
     literally `= 1` — the induction only needs nonzero, scaled by `lam⁻¹` throughout, which
     avoided a much harder "prove it's exactly 1" germ-equality argument). `finrank_window` (the
     `Window D D'` product) via `Module.finrank_pi_fintype` + `Finset.sum_coe_sort` bridging the
     `Fintype`-sum over `↥(diffSupp D D')` to the `Finset`-sum defining `degree`, plus
     `Int.toNat_of_nonneg`/`omega` bookkeeping. `FiniteDimensional` instances for both
     `WindowAt`/`Window` included (gated on `d ≤ d'`/`D ≤ D'` per the design).
  3. **Six-term skyscraper fragment** (`SixTerm.lean`) — **PARTIAL**. Closed: `H1Incl_surjective`
     (part (g), "no `H²`, no long exact sequence, no snake lemma" per the design) — every class
     of `H1 D'` is, on a cover adapted to `diffSupp D D'` (`exists_adapted_refinement`), already
     represented by a genuine `Z1 D`-cocycle: diagonal components vanish to order `⊤`
     (`Z1.ord_diag`), off-diagonal components avoid the finite set where `D ≠ D'`
     (`FinCover.IsAdapted.not_mem_inf`) so the `D'`-bound literally *is* the `D`-bound there
     (`memLD_of_isAdapted`); retyping and `D`-including is then a wash (`C1.retype_mem_Z1'`, the
     general non-coboundary version of `Skyscraper.lean`'s `C1.retype_mem_Z1`;
     `h1CoverIncl_mk_retype`). NOT closed (recorded as interface, per the task's "independent
     items, move on" rule after this was clearly the long pole): `windowConnect`,
     `exists_realization`, Lemma A, `exact_windowMap_windowConnect`,
     `exact_windowConnect_H1Incl` (design §6.9(c)-(f)) — these need the adapted-cover
     *realization* machinery (choosing local Laurent representatives, gluing them into a
     `C0 D' 𝒰` per window vector, and the cover-independence Lemma A comparing two such
     realizations on a common refinement), which is a multi-hour undertaking in its own right
     and did not fit this pass's remaining budget.

  **Notes for finiteness-and-chi**: `finrank_window`/`finiteDimensional_window`/
  `finiteDimensional_windowAt`/`toH1_injective`/`H1Incl_surjective` are all now available with
  the exact signatures your design doc's §1 dependency list expects. **Blocking gap**: your
  `H1Finite.lean` step 2 (`FiniteDimensional ℂ (H1 D)` for general `D`, via
  `exact_windowConnect_H1Incl` identifying `ker (H1Incl h) = range (windowConnect h)`) needs
  `windowConnect`/`exact_windowConnect_H1Incl`, which are NOT built — you will need to either
  build them yourselves (the design §6.9(c)-(f) proof plan is unchanged and still believed
  correct) or find an alternate route to that one instance. Step 1
  (`FiniteDimensional ℂ (H1 D')` via `H1Incl_surjective`) and the χ-ledger's `finrank_window`
  input are fully unblocked.
  **Notes for dolbeault-comparison**: `toH1_injective` (hence Forster 12.8 modulo your own
  `toH1_surjective_of_isGood`) is now available.
  **Notes for laurent-tails**: `mlClass_eq_zero_iff` now has both directions (its `⇒` half was
  your explicitly named consumption target); `windowConnect` as a *template* is still not built
  here, so if you need the connecting map itself (not just `mlClass`), you are also blocked on
  the same §6.9(c)-(f) gap as finiteness-and-chi.
- [ftt] Jacobian/FormTrace/PairForm.lean OK (212 lines) — `resAtX F h x` (D2, the pair-form
  residue), `analyticAt_comp_chart_pair` (Compat: the two-chart `ContMDiffAt → AnalyticAt`
  bridge, one direction, derived from mathlib's `contMDiffWithinAt_iff_of_mem_maximalAtlas` —
  not previously exported for a general chart PAIR on `X`/`Y`), `resAt_pairForm_source_change` +
  `resAtX_eq_of_mem_source_left` (source-chart invariance, task item 1), `resAtX_congr`/
  `resAtX_add`/`resAtX_const_mul`. **FOUND A DESIGN BUG**: the design's `resAtX_eq_of_mem_source`
  (§4.1) claims `resAtX` is invariant under an ARBITRARY target-chart change too — FALSE, with a
  two-line counterexample recorded in the file's module docstring (`X=Y=ℂ`, `F=id`, `h=1/z`,
  target chart `id` vs `y↦2y` gives residue `1` vs `2` — changing the target chart changes WHICH
  1-form `F^*(dz)` means, a coefficient that varies over `X`, not a constant, so reusing the same
  bare `h` computes a genuinely different form's residue). Only the source-chart half is true and
  exported (`resAtX_eq_of_mem_source_left`); the design's own "one-chart-at-a-time" proof-plan
  factoring (§5 P1) was the right instinct but the "right" (target) half needed a correction
  factor, handled per-use-site in `ResidueTraceCompat.lean` rather than as a standalone public
  lemma. Zero sorries.
- [ftt] Jacobian/FormTrace/TraceZkForm.lean OK (106 lines) — `traceZkForm h k w` (D3, Jacobian-
  weighted planar trace atom), `traceZkForm_hAdapted_eq_apply` (cancellation identity, **`w ≠ 0`
  form** — deviation from the design's claimed unconditional function equality, which is false at
  `w = 0` for `k > 1` whenever `g 0 ≠ 0`, since the Jacobian factor `k·v^{k-1}` vanishes at `v=0`
  for `k>1`; the `w≠0` form is equally useful, all downstream uses being `𝓝[≠]0`-germ notions),
  `meromorphicAt_traceZkForm` (unconditional in `k`, needs only mtrace's P5),
  `laurentCoeffAt_traceZkForm`/`resAt_traceZkForm` — **now fully UNCONDITIONAL**, mtrace's P6
  having landed (see the `[mtrace]` log entries) — matches the spike (`scratch_ftt.lean`) exactly,
  only swapping in the real `RS.MTrace.laurentCoeffAt_traceZk` for the spike's abstracted
  hypothesis. Zero sorries.
- [ftt] Jacobian/FormTrace/ResidueTraceCompat.lean OK (312 lines) — `resAtP1` (D4),
  `resAtP1_eq_resAtX_id`, **`resAtP1_trace_eq_sum`** (THE central theorem, Miranda Lemma 3.2
  globalized), `trace_const_mul_pullback` (Miranda Problem VIII.3.D, unconditional),
  `trace_pullback_eq_degree_smul_of_regular` (the `Tr∘F^*=deg·id` projection formula, regular
  values only — see below). **TWO MORE FINDINGS, both resolved/documented in-file:**
  (a) `resAtP1_trace_eq_sum` needed reconstructing the design's own proof plan (§5 P-main), which
  relied on the false general `resAtX_eq_of_mem_source` from `PairForm.lean`. Fix: traced through
  *why* Miranda's classical theorem is nonetheless true — `AdaptedChartsAt`'s existence proof
  (`Jacobian/LocalMultiplicity/AdaptedCharts.lean`) always builds its target chart as `chartAt`
  shifted by an ADDITIVE CONSTANT (a translation, literally constant derivative `1`, the one case
  a target-chart change costs nothing) — a fact about the *construction*, not exposed as an
  `AdaptedChartsAt`/`FiberStack` structure field (an adversarial witness could rescale the target
  chart, genuinely breaking the theorem — verified via a second, order-2-pole counterexample
  recorded in-file). Since the theorem takes an arbitrary `S : FiberStack` as an explicit
  parameter, the calibration is recorded as an EXPLICIT hypothesis `hcal` (satisfied by any
  `exists_fiberStack` witness). Proof: `resAtX_eq_resAt_adapted` (private, the corrected
  per-fibre-point identification, ~40 lines) + `meromorphicAt_comp_sub_const` (private Compat) +
  a 4-step assembly (stack formula near `y₀` as a translation of the `traceZk` terms →
  `resAt_fun_sum` → `resAt_comp_mul_deriv` with the translation → per-term `traceZkForm`
  cancellation + `resAtX_eq_resAt_adapted`), ~120 lines total. Zero sorries.
  (b) `trace_pullback_eq_degree_smul` (design §4.3) is ALSO false unconditionally, same root
  cause as `HolomorphicVanishing.lean`'s issue below (branch-point junk in `traceZk`/`trace`) —
  concrete counterexample recorded in-file (`F := (·^2)`, `g := 1`: `trace F 1 0 = 1` but
  `degree F = 2`). Shipped restricted to `RS.IsRegularValue` (`trace_pullback_eq_degree_smul_of_regular`),
  provable and still the useful case for a future `jacobian-functoriality` unit.
- [ftt] Jacobian/FormTrace.lean (unit root) OK (68 lines) — `scripts/check.sh Jacobian/FormTrace`
  passes: builds clean, **zero sorries** across all 3 files + root (698 lines total). NOT
  registered in `Jacobian.lean` per task hard rule, orchestrator to add `import Jacobian.FormTrace`.
  **LOUD FLAG — `HolomorphicVanishing.lean` (design file 4/6) was NOT built; its centerpiece
  theorem `trace_eq_zero_of_holomorphic` is FALSE, not merely hard.** `RS.MTrace.trace` is the
  UNWEIGHTED fibre sum (`trace_eq_finsum'`, mtrace, proved unconditionally for every point).
  Counterexample: any nonconstant `F : X → ℙ¹` has a branch point (Riemann–Hurwitz forces one for
  any degree-`≥2` cover of `ℙ¹`); take `h ≡ 1` (globally holomorphic on compact `X` — automatically
  constant by the maximum-modulus principle, so `ContMDiff h` is a real, non-degenerate hypothesis
  here, not a vacuous one). Then `trace F h = degree F` at every regular value but only the
  (strictly smaller) fibre CARDINALITY at a branch value — not even continuous there, let alone
  identically `0`. This is a genuine defect in the design's route to Miranda's "integration of a
  trace"/Item 5 (the bare, unweighted function trace `D1` deliberately built instead of a new
  Jacobian-weighted form-trace object cannot be the right vehicle for a "holomorphic form traces
  to a holomorphic form" claim) — not a proof-effort shortfall, so no `sorry`/`TODO(blocker)` was
  left; the file was simply not created. `RationalOnP1.lean` (design file 5/6, the non-load-
  bearing partial-fraction bonus per the design's own §0.3) was also not attempted, for
  time-budget reasons after the above findings (lowest priority, explicitly flagged non-blocking
  by the design). **Notes for downstream**: `abel-weak-solutions` (the only DAG-wired consumer)
  gets `resAtX`, `resAtX_eq_of_mem_source_left`, `resAtP1`, `resAtP1_trace_eq_sum` (with `hcal`),
  `trace_const_mul_pullback` — but NOT `trace_eq_zero_of_holomorphic`; if its "necessity of Abel"
  argument needs a holomorphic-trace-vanishes fact, this needs a fresh design against a corrected
  object, flagged for the orchestrator. `jacobian-functoriality` (`#33`, not a current blueprint
  unit) gets `trace_const_mul_pullback`/`trace_pullback_eq_degree_smul_of_regular` (the latter
  regular-value-only, same caveat). `serre-duality-tails`: unaffected, nothing DAG-wired here
  (confirmed by the design's own §0.3 audit, independently reconfirmed).
- [dolb] Jacobian/Dbar/DiskAcyclic.lean UPDATED (474 lines, was 235) — added the general-divisor
  twist `subsingleton_h1Cover_of_isChartDisk` (D9(b) of dbar-solvability's design, honestly
  deferred by the dbar builder, built here under dolbeault-comparison's SPECIAL AUTHORIZATION
  since Leray.lean's member-splitting step needs disk acyclicity at arbitrary `D`, not just 0).
  Route: Weierstrass-factor germ `t := mk (q∘e) _` on the chart disk `V` with
  `q w := ∏ a ∈ S, (w - e a)^(D a)` (`S := D.support ∩ V`, finite via `[T2Space X][CompactSpace X]`
  + `Function.locallyFinsuppWithin.finiteSupport`), `ord t x = D x` on `V` (via
  `ordAtX_eq_of_mem_source` chart-transport + `meromorphicOrderAt_prod` +
  `meromorphicOrderAt_zpow_id_sub_const`/analytic-nonvanishing-atom order-0 case, `Finset.sum_ite_eq'`
  to collapse the sum); `t * t⁻¹ = 1` via `compl_finite_mem_codiscreteWithin` (finite complement is
  codiscreteWithin ANY set, no connectedness needed) + a punctured-neighborhood argument excluding
  `S.erase x`. Main proof: twist `f ∈ Z1 D 𝒱` by (restrictions of) `t` into `g ∈ Z1 0 𝒱` (cocycle
  identity via `Z1.rel_res` + `MeroGermOn.restrict`'s `AlgHom.map_mul`/`restrict_restrict` factoring
  out the common `t`-factor, `ring` to reassociate), apply the already-built
  `subsingleton_h1Cover_zero_of_isChartDisk` to split `g = d0 h`, then untwist by `t⁻¹` to get
  `f = d0 h'`. Zero sorries; `scripts/check.sh Jacobian/Dbar` passes (2964 jobs, unit still
  COMPLETE). Gotcha for siblings: `rw` on `Iff`-valued lemmas with under-determined implicit
  Submodule/set arguments (`mem_linSysOn_iff_of_isOpen`, `eventuallyEq_codiscreteWithin_iff_of_isOpen`)
  can fail to unify even when a direct term application (`(lemma args).2 ?_` via `refine`) succeeds
  instantly — prefer `refine (lemma args).2 ?_` over `rw [lemma args]` for iff-lemmas with a
  Set/Submodule-valued implicit that only gets pinned by the surrounding expected type. Also: bare
  `inf_le_left`/`inf_le_right` used directly inside a `show`/`have`-with-explicit-type statement can
  leave one lattice-meet operand as a stuck metavariable (elaboration doesn't see the type ascription
  in time) — name them as separate `have hij_r : A ⊓ B ≤ B := inf_le_right` first, matching the
  existing codebase's `hbc/hac/hab` convention throughout `Cech/`.
- [canon] Jacobian/CanonicalForms — ARCHITECTURAL REVISION: quotient fix OK (`scripts/check.sh
  Jacobian/CanonicalForms` passes, zero sorries, 1929 lines across 7 files). The raw
  chart-coefficient structure is renamed `MFormData` (data carrier, `MForm.lean`/`OrdRes.lean`
  unchanged in content) and `MForm X` is now the QUOTIENT by `MFormData.Eqv` (germ agreement of
  the preferred-chart coefficients on `𝓝[≠]` of every chart center — CC3 pattern, new file
  `Quotient.lean`), equivalent to codiscrete-in-every-chart agreement, chosen because every
  reading map (`ord`/`resAt`/`laurentCoeffAt`/`divisor`) is a germ-at-center functional so
  descent is a one-line congruence. This unblocked the entire previously-deferred chain, now all
  PROVED: D5 `MForm.eq_zero_or_forall_ord_ne_top` (the "`S = univ ⇒ θ = 0`" step that is FALSE
  raw is definitional on the quotient; closedness of `{ord = ⊤}` is free from
  `eventually_ord_eq_zero`); full `Module (ℳ X) (MForm X)` + `IsScalarTower`/`SMulCommClass ℂ`
  (via new `Mero.holoRepr_add/mul/smul/inv/zero/one` germ identities); `MForm.d_add` (via
  mathlib's `Filter.EventuallyEq.nhdsNE_deriv`); `MForm.resAt_dlog` (junk-robust, no `f ≠ 0`);
  D8 `MForm.exists_unique_smul_of_ne_zero` (chart-local ratios glue by `MeroGermOn.exists_glue`;
  quotient granularity removes the removable-singularity repair at zeros of `θ₀`; only needs
  `[T1][Connected]`); D10 `canonicalDivisorOf`/`MForm.divisor_smul_mero`/
  `canonicalDivisorOf_linearEquiv` (placed in `OneDimensional.lean`, not the Chi-gated
  `Existence.lean`); D11 `MForm.OmegaSpace` (on the quotient, instance-free)/`MForm.i`/
  `MForm.smul_mem_omegaSpace_iff`/`Ω_iso_linSys : OmegaSpace D ≃ₗ[ℂ] LinSys (D + K)`/
  `i_eq_l_add_canonicalDivisorOf`; D12 `form1ToOmega(_surjective)`/`holomorphicMFormsEquiv :
  Form1 X ≃ₗ[ℂ] OmegaSpace 0` (surjectivity repairs a representative chart-by-chart through
  `MeroGermOn.holoRepr` + the new cross-point bridge
  `MFormData.ord_eq_meromorphicOrderAt_of_mem_source`; NO topological instances needed)/
  `genus_eq_finrank_omegaSpace_zero`; D13 `MLFormData.Realizes` restated on classes via the
  lifted `MForm.laurentCoeffAt`. STILL DEFERRED (unchanged): D9 `Existence.lean` — gated on
  `Jacobian/Finiteness/Chi.lean`, still not on disk at completion time. NOT registered in
  `Jacobian.lean` (unchanged; orchestrator to add). Consumer notes: **serre-duality-cech** gets
  its full statement bank (`MForm.OmegaSpace`/`MForm.i`/`canonicalDivisorOf`(+`_linearEquiv`)/
  `Ω_iso_linSys`/`MLFormData.totalRes`); **laurent-tails** gets `Ω_iso_linSys`/`canonicalDivisorOf`
  it previously lacked; **residue-theorem** gets `MForm.resAt` on classes + `resAt_dlog` +
  data-level chart-invariance (`MFormData.resAt_eq_of_mem_source` — quotient consumers reach it
  via `MForm.exists_rep`); **cech-h1-genus/riemann-roch** get `genus_eq_finrank_omegaSpace_zero`
  + `i_eq_l_add_canonicalDivisorOf`. BREAKING for any not-yet-written consumer drafted against
  the old raw `MForm`: the structure is now `MFormData`; `MForm` is its quotient (`MForm.mk`,
  `mk_eq_mk`, `exists_rep`, `sound`, `ind`); coefficient access on classes is via representatives.
- [cech] SixTerm CLOSED — `Jacobian/Cech/SixTerm.lean` (1001 lines) finishes the LAST gap of the
  cech-cohomology unit: the six-term skyscraper fragment §6.9(c)-(f) is now fully proved, so
  `0 → L(D) → L(D') → Window D D' → H¹(D) → H¹(D') → 0` is complete end to end.
  `scripts/check.sh Jacobian/Cech` passes: builds clean, **zero sorries** across all 10 files
  + root (3434 lines). Construction shape (all in `SixTerm.lean`, on top of the previous pass's
  `H1Incl_surjective`/`memLD_of_isAdapted`/retype lemmas): (1) **Lemma B**
  `exists_tail_approx` — a germ of order `≥ -d'` at `q` is matched to order `≥ -d` by a finite
  Laurent tail in `ordGe q (-d')`, by induction on `(d'-d).toNat` iterating a one-step
  leading-coefficient subtraction `exists_tail_step` (`u := θ_{q,-m}·γ`, subtract
  `u.evalAt q • θ_{q,m}`; needs `tailGerm_mul_tailGerm_neg`); (2) **D7 realization predicate**
  `Realizes 𝒰 g w` — pointwise `ord ≥ -(D q)` bound on the comparison germ
  `windowDefect γ ψ := γ|_{V∩src} - ψ|_{V∩src}` against *every* chart-source representative
  `ψ` of `w q` (equivalent to the design's `(w q).out` form by `windowDefect_bound_of_mk_eq`;
  strictly easier to consume), with closure lemmas `Realizes.res/add/smul`; (3)
  `exists_realization` — realize `w` on a cover from `exists_adapted_refinement` prescribing,
  at each `q ∈ diffSupp D D'`, the neighbourhood `N_q ⊓ compOpens (S'.erase q)` (pole-free
  zone of the chosen representative `ψ q` ∩ complement of the other special points
  `S' := diffSupp ∪ supp D ∪ supp D'`); the cochain is `ψ hk.choose` restricted on members
  meeting `diffSupp`, `0` elsewhere (choice-independence of the member's `diffSupp`-point via
  the `S'.erase` separation), `MemLD` for free from `memLD_of_isAdapted` since the cochain's
  coboundary is a `Z1 D'` coboundary on an adapted cover; (4) **Lemma A**
  `mlClass_eq_of_realizes` — NO adaptedness hypothesis: restrict both realizations to
  `𝒰.meet 𝒰'` (`mlClass_res`, via `resZ1`+`toH1_resH1`), then `G - G'` is a `C0 D`-cochain
  (at `diffSupp` points the two `Realizes` bounds control the difference through `windowDefect`
  algebra; elsewhere `D = D'`), so the retyped coboundaries agree in `H1Cover D` by
  `H1Cover.mk_eq_zero_iff`; (5) `windowConnect : Window D D' →ₗ[ℂ] H1 D` — `choice` over
  `exists_realization`, well-defined + linear purely via Lemma A (`windowConnectRaw_eq`), with
  the consumer-facing `windowConnect_spec : windowConnect h w = mlClass 𝒰 g hg` for ANY
  realization; (6) `exact_windowMap_windowConnect` — `⊆`: `mlClass_eq_zero_iff` gives a global
  `φ : L(D')`, and `le_ord_sub` of its bound against the `Realizes` bound (bridged by
  `ord_sub_global_eq_defect`) shows `w = windowMap h φ`; `⊇`: `mlClass_eq_zero_of_exists`; (7)
  `exact_windowConnect_H1Incl` — `⊆`: `toH1_injective` (12.4) turns `H1Incl ξ = 0` into a
  `D'`-coboundary witness `g'` on the representing cover itself, Lemma B reads off its window
  vector `w`, and the cocycle relation (`hmemld` d0-bound) + `windowDefect_ord_congr`
  cross-member normalization show `Realizes 𝒱 g' w`, whence
  `windowConnect h w = mlClass 𝒱 g' _ = ξ`; `⊇`: `H1Incl_mlClass`. Fixes applied to the
  interrupted draft (all instances of known gotchas): unpinned Set-valued implicits at
  `Set.inter_subset_left`/a `MeroGermOn X _` type ascription (named fully-ascribed `have`s per
  the log's standing note), and a `zero_smul` rewrite stuck on the Pi-type `Window` smul
  (replaced by term-mode `exact zero_smul ℂ (w q)` — defeq through `Pi.instSMul` where the
  `rw` pattern match fails). Root docstring + `Skyscraper.lean` note updated; unit root
  `Jacobian/Cech.lean` unchanged in imports (SixTerm already registered). Cosmetic leftovers:
  2 `unusedVariables` warnings in `exists_realization` (the `h : D ≤ D'` hypothesis is kept
  for design conformity though the construction never uses it; ditto the existential's `hg`
  binder name).
  **Notes for finiteness-and-chi**: the previously blocking gap is gone —
  `windowConnect`/`exact_windowConnect_H1Incl` now exist with exactly the shapes your
  `H1Finite.lean` step 2 plan expects (`ker (H1Incl D h) = range (windowConnect h)` via
  `Function.Exact`, `Set.image_eq_range`-style consumption; combine with `finrank_window` +
  `finiteDimensional_window` from `WindowRank.lean` and `H1Incl_surjective` for step 1). The
  χ-ledger's six-term rank bookkeeping (`chi` in `docs/design/finiteness-and-chi.md` §chi) has
  every arrow: `inclusion_injective`, `exact_inclusion_windowMap` (Window.lean),
  `exact_windowMap_windowConnect`, `exact_windowConnect_H1Incl` (SixTerm.lean),
  `H1Incl_surjective`. Remember `AddCommGroup (H1 D)` does not resolve by plain
  `inferInstance` — go through `Module.DirectLimit`'s own instances or `exists_eq_of_of_eq`.
  **Notes for laurent-tails**: the connecting-map template is now real — your `T[D] → H¹(D)`
  should factor through `mlClass` exactly as `windowConnect` does: produce a realization
  (`Realizes` is the reusable predicate; `exists_realization`'s adapted-cover pattern and
  `exists_tail_approx` for tail extraction are both exported), then `windowConnect_spec` /
  `mlClass_eq_of_realizes` give well-definedness for free; `mlClass_eq_zero_iff` (both
  directions) characterizes the kernel.
- [stokes] Jacobian/PlanarStokes/Compat.lean OK (182 lines, ~7s) — found already complete from the
  interrupted prior session (Leibniz rule `wirtingerDbar_mul` + `wirtingerDbar_mul_of_
  differentiableAt`/`wirtingerDbar_mul_eq_zero_of_notMem_tsupport`, the `ContDiffOn.contDiff_of_
  hasCompactSupport` gluing lemma, `continuous_wirtingerDbar_of_contDiff_one` (R1 resolved),
  `tsupport_wirtingerDbar_subset`, the `ℂ`-rectangle ↔ iterated-real-integral bridge
  `setIntegral_reProdIm_eq_intervalIntegral`/`integral_eq_intervalIntegral_of_tsupport_subset_
  reProdIm`). Recompiled clean, zero sorries, no changes needed.
- [stokes] Jacobian/PlanarStokes/CompactSupport.lean OK (179 lines, ~10s) — found already complete
  (Atom 1 `integral_wirtingerDbar_eq_zero` via the rectangle-Stokes-lemma + boundary-vanishing
  argument, Atom 1b `integral_wirtingerDbar_mul_eq_zero_of_differentiableOn`). Recompiled clean,
  zero sorries, no changes needed.
- [stokes] Jacobian/PlanarStokes/AnnulusResidue.lean FIXED + extended (815 lines, ~15s) — found
  mid-edit (no `end RS`, missing the model-case regression theorem the file's own docstring
  promised) and with one real bug: `hv_eq_gf`'s off-`tsupport g` branch (inside Atom 2's proof)
  ended in a `show g w * f w = 0` that is NOT definitionally equal to the actual goal
  `wirtingerDbar (fun w => g w * f w) w = 0` (the same lambda-vs-unfolded-application trap this
  project's build log already flags elsewhere) — fixed by routing through Compat's own
  `wirtingerDbar_mul_eq_zero_of_notMem_tsupport` instead of re-deriving it inline. Completed the
  file: (1) Atom 1′ (`circleIntegral_sub_circleIntegral_eq_two_mul_I_mul_integral_wirtingerDbar`,
  the exp-substitution annulus identity) and Atom 2 (`integral_wirtingerDbar_mul_eq_neg_pi_mul_
  resAt`) were already present and correct, verified compiling; (2) added the promised model-case
  regression check `integral_wirtingerDbar_mul_inv_sub_eq` (`f = (·-p)⁻¹`, independent derivation
  via `RS.cauchyPompeiu` + the measure-preserving substitution `w ↦ p - w`
  (`Measure.measurePreserving_sub_left` + `measurableEmbedding_subLeft`, needs
  `import Mathlib.MeasureTheory.Measure.Haar.Unique` for the `IsNegInvariant volume` instance on
  `ℂ` — not otherwise in scope, a real gotcha for anyone doing Lebesgue-measure reflection/
  translation substitutions on `ℂ`). **Deviation from the design's frozen §5.3 signature, filed as
  the abel-weak-solutions refinement the task asked about**: `integral_wirtingerDbar_mul_inv_sub_eq`
  is stated WITHOUT the `hpU`/`hconst` hypotheses Atom 2 needs — both are provably unused in this
  proof (the design's own §8.4 already observes a simple pole needs no local-constancy at all).
  Also added, reusing the same substitution+integrability machinery already established by
  `cauchyPompeiu`'s own proof (`HasCompactSupport.convolutionExists_right`,
  `MeasurePreserving.integrable_comp_of_integrable`, `integrable_const_mul_iff`):
  `integrable_wirtingerDbar_mul_inv_sub` (the integrand is integrable) and
  `integral_wirtingerDbar_mul_inv_sub_sub_inv_sub_eq` (the two-puncture shape
  `f = (·-b)⁻¹ - (·-a)⁻¹`, `∫∫(∂̄g)·f = -π·(g b - g a)`, assembled from two instances of the
  single-puncture lemma + `MeasureTheory.integral_sub` — matches
  `docs/design/abel-weak-solutions.md` §7.3 step 3's Lemma-20.3 assembly EXACTLY, for any `C¹`
  compactly-supported `g`, no local constancy needed). Zero sorries.
- [stokes] Jacobian/PlanarStokes.lean (unit root) OK (46 lines; `scripts/check.sh
  Jacobian/PlanarStokes` passes, zero sorries across all 3 files (1176 lines) + root — unit
  COMPLETE). NOT registered in `Jacobian.lean` per task hard rule, orchestrator to add
  `import Jacobian.PlanarStokes`. Notes for **residue-theorem**: Atoms 1/1b/1′/2 all present and
  exactly as designed (`docs/design/planar-stokes.md` §5); no "change of variables for the area
  integral" atom is built (§10, unchanged — `ResidueCalculus.resAt_comp_mul_deriv` already
  suffices). Notes for **abel-weak-solutions**: both Atom 1b and Atom 2 are available as its own
  design doc expects (§2.2, correcting `planar-stokes.md`'s own downstream-map guess), PLUS the
  requested `hconst`-free refinement is done: `integral_wirtingerDbar_mul_inv_sub_eq` (single
  puncture, general `g`), `integrable_wirtingerDbar_mul_inv_sub`, and
  `integral_wirtingerDbar_mul_inv_sub_sub_inv_sub_eq` (the exact two-puncture `g b - g a` shape,
  §7.3 step 3) are all ready to consume directly — no further Stokes/measure-theory work should be
  needed for that unit's Lemma-20.3 step.
- [dolb] Jacobian/DolbeaultComparison/Leray.lean OK (677 lines; continuation of a MID-WORK file
  left by a previous builder at 345 lines — steps 1-3 of Forster 12.8's member-splitting proof
  were already in place, namespace `RS.Cech`; this pass finished steps 4-7 per
  `docs/design/dolbeault-comparison.md` §5). Added: `exists_crossGlueLinSysOn`/`patch_restrict`
  (LinSysOn-level unfolding of the step-3 glue), `exists_crossGlueFam`/`crossGlueFam_mem_Z1`
  (step 4: the glued family is a genuine `𝒰`-cocycle — PURE telescoping algebra from `patch`'s
  definition, no cocycle hypothesis on the input `f` needed at all, contrary to what the
  step-by-step design prose might suggest), `tradeH0`/`resC1_crossGlueFam_add_eq` (step 5's frozen
  conclusion `resC1 F + f = d0 h`, verified against Forster PDF 108's mirror-convention sign
  warning), then the 4 exports: `exists_trade`, `resH1_surjective_of_isGood`,
  `toH1_surjective_of_isGood` (**Leray's theorem**, discharging cech's `Colimit.lean`-recorded
  interface), `h1CoverEquiv`. `scripts/check.sh` not yet run (comparison files not built this
  pass); direct `lake env lean Jacobian/DolbeaultComparison/Leray.lean` compiles clean, **zero
  sorries**. Per design §0.1 this file ALONE (no `Form01`/PoU/∂̄) unblocks finiteness-and-chi —
  reporting now even though the comparison files (`GlueForm01`/`Splitting`/`Comparison`) are
  separate follow-up work. Gotchas hit repeatedly (new, beyond DiskAcyclic's prior notes):
  (1) type ascriptions `(𝒰.U i ⊓ 𝒰.U j : Set X)` elaborate as `↑(𝒰.U i) ⊓ ↑(𝒰.U j)`
  (Set-level inf of the coercions), NOT `↑(𝒰.U i ⊓ 𝒰.U j)` (coe of the Opens-level inf) — these
  are equal but not syntactically so; `rw [mem_linSysOn_iff_of_isOpen ...]` against an
  `Opens.isOpen`-sourced `IsOpen` proof can fail to unify for exactly this reason — use
  `refine (mem_linSysOn_iff_of_isOpen hU).2 ?_` instead (extends the DiskAcyclic-recorded
  `rw`-vs-`refine` iff-lemma gotcha to this new shape). (2) After `rw` collapses two nested
  `MeroGermOn.restrict`s via `restrict_restrict` into a single restrict, the two sides of the
  goal are only equal via PROOF IRREVELANCE of the two `≤`/`⊆` witnesses (same Prop, different
  terms) — `rw`'s automatic trailing-`rfl` closer does not always fire on this; append an
  explicit `rfl` tactic line after such a `rw` rather than assuming it auto-closes. (3) when a
  restriction-along-`le_rfl` appears in a helper lemma's conclusion (e.g. `splitting_eq_restrict`
  applied with `hWαβ := le_refl _`), convert it to the bare (unrestricted) term via
  `RS.MeroGermOn.restrict_id` explicitly (it is a propositional lemma, proved by `induction`, NOT
  `rfl`) rather than trying to state the bare form directly as the lemma's output type. (4) for
  chained additive/subtractive identities across 3+ `have`-facts, `linear_combination h1 - h2 -
  h3`-style closing (treating `MeroGermOn`'s `CommRing` structure as the ring `ring` normalizes
  over) is far more robust than manual `rw [...]; abel` chains, which break when the terms to
  rewrite are not literally contiguous subterms of the goal (interleaved differently after a
  prior rewrite) — prefer it whenever 3 or more equational facts must be combined.
  **Notes for finiteness-and-chi** (the actual compiled signatures, `D` auto-inserted first from
  the ambient `variable (D : RS.Divisor X)`, `𝒰 𝒱 : FinCover (⊤ : Opens X)` implicit throughout):
  `exists_trade (D) (h𝒰 : 𝒰.IsGood) (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ) (f : Z1 D 𝒱) :
  ∃ (F : Z1 D 𝒰) (g : C0 D 𝒱), (resZ1 D τ hτ F : C1 D 𝒱) = (f : C1 D 𝒱) + d0 D 𝒱 g`;
  `resH1_surjective_of_isGood (D) (h𝒰) (τ) (hτ) : Function.Surjective (resH1 D τ hτ)`;
  `toH1_surjective_of_isGood (D) (h𝒰 : 𝒰.IsGood) : Function.Surjective (toH1 D 𝒰)` (exactly the
  interface cech's `Colimit.lean` docstring recorded); `h1CoverEquiv (D) (h𝒰) : H1Cover D 𝒰 ≃ₗ[ℂ]
  H1 D` (`:= LinearEquiv.ofBijective (toH1 D 𝒰) ⟨toH1_injective D 𝒰, toH1_surjective_of_isGood D
  h𝒰⟩`), `h1CoverEquiv_apply`. All four hold for EVERY `D : Divisor X` (no `D = 0` restriction),
  matching cech's recorded signature exactly — no drift. Needs `[T2Space X] [CompactSpace X]`
  throughout (inherited from dbar's disk-acyclicity twist + `exists_good_refinement`).
- [dolb] Jacobian/Dbar/Form01.lean UPDATED (299 lines, was 121) — added `Form01CoeffData`/
  `Form01.ofCoeffs`/`Form01.coeffAt_ofCoeffs` (design §1.4's substrate list), confirmed NOT
  present from any prior pass, added here under dolbeault-comparison's authorization (needed by
  `GlueForm01.lean`'s `DbarGlueData.form` constructor, design §6.1) — a clean transcription of
  `Form1CoeffData`/`Form1.ofCoeffs` (`Jacobian/Forms/OfCoeffs.lean`) with `starRingEnd ℂ` (`conj`)
  inserted in the transition rule per `Form01`'s own `compat` field. SIMPLER than the `Form1`
  original: `Form01` is a raw chart-coefficient structure (not a bundled `ContMDiffSection`), so
  no covector/hom-bundle/`mfderiv`/`tangentCoord` detour is needed — `rawCoeffAt` is assembled
  directly as an `X → ℂ → ℂ` function via a chosen covering-chart index per point (`idx`,
  `Classical.choice`-based), the master transport identity `rawCoeffAt_eq` (independence of the
  chosen index, via `compat` + `RS.deriv_trans_comp`'s 3-chart chain rule), real-smoothness
  (`AnalyticAt.restrictScalars (𝕜 := ℝ)` + `.contDiffAt`, `Complex.conjCLE.contDiff` for the
  `conj` factor), and the cross-preferred-chart transition `rawCoeffAt_trans` (feeds `Form01`'s
  `compat` field directly). `scripts/check.sh Jacobian/Dbar` re-run: still passes (2964 jobs),
  **zero sorries**. Gotchas (new): (1) a `def` using `if h : P then _ else _` (`dite`) on a
  non-syntactically-`Decidable` `Prop` (e.g. `z ∈ (chartAt ℂ x).target`) needs `open scoped
  Classical` in scope BEFORE the `def` — omitting it fails with `synthInstanceFailed` on the
  `dite`, which then CASCADES into spurious "Invalid field notation"/"unknown identifier" errors
  on every later dot-notation use of that same malformed function (misleading — the root cause
  is always the missing `Classical` instance at the `def` site, chase it first). (2)
  `ContDiffAt.congr_of_eventuallyEq (h : ContDiffAt 𝕜 n f x) (hg : f₁ =ᶠ[𝓝 x] f) : ContDiffAt 𝕜 n
  f₁ x` — the `EventuallyEq` direction is `f₁ =ᶠ f` (new-name first), the OPPOSITE of the
  intuitive "old =ᶠ new" reading; passing `.symm` when it looks like it should be needed is
  usually the tell that the un-symm'd hypothesis was correct all along. **Note for any future
  `Form01`-consuming unit**: `Form01.ofCoeffs`/`Form01CoeffData` are now available at the exact
  shapes design's §1.4/§4.2/§6.1 quote; `Form01.coeffAt_ofCoeffs` gives the CENTER-point value
  only (`(Form01.ofCoeffs Data).coeffAt x (chartAt ℂ x x)`, mirroring `Form1.coeffAt_ofCoeffs`
  exactly), matching GlueForm01's consumption plan verbatim.
- [serrec] Jacobian/SerrePairing/{TailSpace,Pairing,Duality}.lean + Jacobian/SerrePairing.lean
  (unit root) OK — `scripts/check.sh Jacobian/SerrePairing` passes (2927 jobs), zero sorries
  across 4 files (472 lines total: TailSpace 101, Pairing 170, Duality 201, root docstring 88).
  Continuation of an interrupted builder: `TailSpace.lean`/`Pairing.lean` were already on disk and
  compiled clean as-is (previous builder had already adapted `Tail X` to `abbrev` and `pair` to
  route through `MForm.laurentCoeffAt` on classes rather than raw `coeffAt`, per the CanonicalForms
  quotient revision); this pass wrote `Duality.lean` (D4 `exists_tail_pair_ne_zero`, D5
  `finrank_omegaSpace_le`) and the unit root from scratch. Centerpieces: `Tail X`/`TailSpace D`
  (free `Finsupp`-of-`Finsupp`s, D1), `pair`/`pairL` bilinear (D2, via `Finsupp.lsum` over
  `MForm.laurentCoeffAt`), `exists_tail_pair_ne_zero` (the injectivity core — single-term test tail
  at the leading Laurent exponent, computed via `pair_single` + a new Compat lemma
  `MForm.laurentCoeffAt_ord_ne_zero` lifting residue-calculus's `laurentCoeffAt_order_ne_zero`
  through `MForm.exists_rep`), `finrank_omegaSpace_le` (the generic, premise-parameterized `≤`-half
  interface: any finite-dimensional `H` + surjective `toH : ↥(TailSpace D) →ₗ[ℂ] H` + a
  well-definedness hypothesis `hwd` give `finrank Ω(-D) ≤ finrank H`). Needs only
  `[T1Space X] [ConnectedSpace X]` throughout (dropped the design's extra `[T2Space][CompactSpace]`
  — `MForm.OmegaSpace`/`Module.finrank` are topology-free after the canonical-forms revision).
  NOT registered in `Jacobian.lean` (task hard rule; orchestrator to add `import
  Jacobian.SerrePairing`).

  **Deviation (adaptation, not correction) — the quotient revision**: `pair` is defined directly
  from `MForm.laurentCoeffAt` on classes (Miranda's own boxed formula) rather than via `resAt` of a
  representative product + `resAt_tail_mul`, since `MForm` no longer exposes raw `coeffAt`;
  same content, less proof debt (bilinearity in `τ` free from `Finsupp.lsum`). `mem_omegaSpace_iff`
  also dropped the design's `θ = 0 ∨ -D ≤ θ.divisor` disjunction for a single order-wise condition
  (uniform since `θ = 0` has `ord = ⊤` everywhere) — `exists_tail_pair_ne_zero`'s proof uses this
  directly, one `Divisor.neg_apply`/`neg_neg` unwind then an `omega`-closed integer inequality.

  **Genuine mathlib-instance gap found and worked around (flagged for any future `Tail X`/
  `TailSpace D` consumer, e.g. laurent-tails/serre-duality-tails if they ever build further
  `Submodule`s over this carrier)**: the design's primary plan for D5 (`Submodule.liftQ` +
  `LinearMap.quotKerEquivOfSurjective`, stacking a further quotient `↥(TailSpace D) ⧸ ker toH` on
  top of `Tail X`) elaborates so slowly it deterministically times out at `whnf`/`isDefEq` even at
  1,000,000 heartbeats. Root cause, isolated by direct scratch experiment (bisecting instance
  arguments): `↥(TailSpace D)` — a `Submodule` over the DOUBLY-NESTED `Finsupp` carrier
  `Tail X := X →₀ (ℤ →₀ ℂ)` — has no *findable* `AddCommGroup`/`Sub`/`Neg` instance at this pin;
  `AddSubgroupClass (Submodule ℂ (Tail X)) (Tail X)` itself fails `inferInstance` (confirmed this
  is NOT about the previous builder's `abbrev`-vs-`def` choice — reproduced identically with the
  custom instances stripped out), even though `Tail X` unwrapped has a perfectly good
  `AddCommGroup`/`Sub`, and the SEMIRING-level `Submodule.add_mem`/`smul_mem` (needing only
  `Semiring`/`AddCommMonoid`, not `Ring`/`AddCommGroup`) resolve fine. Fix: used the design's own
  pre-registered risk-3 fallback (§7) instead — `resDual`/`Φ` are built from a chosen section
  `Function.surjInv` of `toH` plus a congruence lemma `pair_congr_of_toH_eq`, and every place a
  "difference" of `↥(TailSpace D)` elements was needed is built as `τ + (-1 : ℂ) • σ` (`+`/`•`,
  confirmed working) instead of `τ - σ` (`Sub`, confirmed broken) — zero mathematical content lost.
  Gotcha for siblings: avoid `Submodule.sub_mem`/`neg_mem`/`AddSubgroupClass`/bare `Sub`/`Neg` on
  `↥(TailSpace D)` (or any `Submodule` over a nested-`Finsupp` carrier) directly; `add_mem`/
  `smul_mem` plus the `(-1 : ℂ) • ·` trick sidestep it completely. Also recorded: `omit [...] in`
  and `set_option ... in` must precede a declaration's docstring, not follow it (`/-- doc -/`
  between the modifier and `def`/`theorem` causes an "unexpected token" parse error) — a `let`
  bound to a structure must use `:= { field := ... }`, not `where` (the latter is `def`/`theorem`-
  only syntax, not valid after `let` in tactic mode).

  Consumer notes for serre-duality-tails (#26), the adapter surface as built: `Tail X`/`TailSpace
  D`/`pair`/`pairL`/bilinearity/`pair_single` (self-contained, provable off canonical-forms +
  residue-calculus alone, confirmed no dependence on laurent-tails/residue-theorem/cech-cohomology)
  remain available exactly as their own design's frozen §0 reconciliation records — per that
  reconciliation, #26 runs Miranda VI.3 on its own germ tail model instead of instantiating this
  unit's `finrank_omegaSpace_le`/`Tail X` directly, reusing only the proof PATTERN
  (`resAt_zpow_mul`/`laurentCoeffAt_order_ne_zero`-shaped injectivity computation, matching
  `RS.Cech.tailGerm`'s literal-monomial normalization) and citing `exists_tail_pair_ne_zero`'s shape;
  nothing here blocks or needs revision for that plan. `finrank_omegaSpace_le` itself remains a
  ready-made, zero-sorry `≤`-half interface (instantiable at `H := RS.Cech.H1 D`) if ever wanted.
- [dolb] Jacobian/DolbeaultComparison/GlueForm01.lean OK (250 lines) — design §4.2/§6.1's gluing
  atom, built in one pass (all pieces from the design's proof plan turned out correct on first
  logical draft; only mechanical Lean-API fixes were needed, see gotchas below). Exports:
  `Form01.ext_center` (Compat, via `Form01.compat` applied at the pair `(p, x)` + `Form01.ext`),
  `DbarGlueData` (fields exactly as design: `n, V, covers, center, subChart, u, smoothOn,
  holoSub`), `DbarGlueData.chart/chart_mem_maximalAtlas/chart_source` (the restricted-chart
  bookkeeping, `restr_mem_maximalAtlas`/`restr_source'` per design §1.1), `DbarGlueData.
  wirtingerDbar_u_transport` (the CENTRAL reusable lemma: `wirtingerDbar` of `u i`'s
  representative in ANY maximal-atlas chart transports to its value in the OWN data chart `i` by
  the `conj`-derivative of the transition — used for BOTH `Form01CoeffData.compat` — with
  `e := chart j` — AND `isDbarOn_form` — with `e := chartAt x` — the same computation the design
  predicted would be shared), `DbarGlueData.coeffData` (the `Form01CoeffData`; `compat` field via
  the `u j = (u j − u i) + u i` split + `holoSub`'s Cauchy–Riemann vanishing +
  `wirtingerDbar_u_transport`, exactly per design §6.1), `DbarGlueData.form := Form01.ofCoeffs
  d.coeffData`, `DbarGlueData.isDbarOn_form`, `DbarGlueData.form_unique`. A local `private`
  Compat re-derivation of `Jacobian.Dbar.Operator`'s (non-exported) `private` helper
  `contDiffOn_comp_chartAt_symm_of_contMDiffOn` was needed (kept local rather than editing
  Operator.lean, per CONVENTIONS' "add locally, request upstream" policy — no upstream request
  filed since it is a trivial 12-line repeat, not a missing capability). Zero sorries. Gotchas
  (new, on top of Leray's and Form01.ofCoeffs's): (1) mathlib's Wirtinger-adjacent lemmas
  (`wirtingerDbar_add/congr_nhds/eq_zero_of_differentiableAt`, `contDiffOn_wirtingerDbar`) live in
  a file with `variable (f g : ℂ → ℂ) (z w c : ℂ)` declared **explicit** — every one of these
  lemmas therefore has `f`/`g`/`z` as its OWN leading EXPLICIT parameters (auto-included, in
  declaration order), NOT curly-brace-inferred from the conclusion; call them as
  `wirtingerDbar_add _ _ _ hf hg` / `wirtingerDbar_congr_nhds _ _ z h` /
  `contDiffOn_wirtingerDbar _ hs hf` (function argument(s) FIRST via `_`, exactly mirroring the
  call sites already established in `Jacobian/Dbar/Operator.lean` — grep that file for the
  pattern before guessing a signature). (2) Defining a lemma inside `namespace Foo` with the SAME
  bare name as an already-`open`ed outside declaration (here: my own `DbarGlueData.
  chart_mem_maximalAtlas`/`chart_source` vs. `open`ed `IsManifold.chart_mem_maximalAtlas` /
  no-clash `chart_source`) shadows the outside one for UNQUALIFIED references inside that
  namespace — a call meant for the global lemma silently resolves to the local one instead,
  producing a confusing arity/type mismatch (arg expected `DbarGlueData` instead of `X`); always
  fully-qualify the outside name (`IsManifold.chart_mem_maximalAtlas x`) at every call site once
  such a clash exists, rather than trying to rename either side. (3) `(e.restr s).symm`,
  `⇑(e.restr s)`, and `(e.restr s).target = e '' (e.source ∩ s)` (for open `s`) are all provable
  `rfl`/one-line facts (spiked in a throwaway scratch file first) — cheaper than hunting for a
  named simp lemma. (4) `ContMDiffOn.neg` produces the POINTWISE-lambda form `fun y => -(f y)`,
  not the bundled `-f`; `rw [neg_sub]` will not fire on it directly — `funext y; simp only
  [Pi.sub_apply]; ring` (or an explicit `have heq : (fun y => -(f y)) = g := by funext y; ring`
  then `rwa [heq] at h`) bridges the gap. (5) `x ∈ (V : Opens X)` and `x ∈ (V : Set X)` are
  DEFEQ but not always syntactically interchangeable for `rw`; a `show x ∈ (V : Set X)` first
  makes the coercion visible to `rw`.
  **Notes for Splitting.lean/Comparison.lean** (next in the file plan): `DbarGlueData.form_unique`
  is the single well-definedness workhorse exactly as design promised — every future
  independence/compatibility lemma about `dolbForm`/splittings should reduce to it via
  `form_unique` applied to a candidate `(u := s.g)` against a shifted target, never by comparing
  PoU data pairwise. `Form01.ext_center` and `DbarGlueData.{form,isDbarOn_form,form_unique}` are
  the only 4 names this file exports for downstream comparison use (per design §4.2, verbatim).
- [abelweak] Jacobian/AbelWeak/PlanarLogBranch.lean OK (187 lines) — the exp-gluing engine, spiked
  in `scratch_abelweak.lean` and built out per design §6.1: `exists_logBranch_disk` (disk case,
  disk-Morera primitive `DifferentiableOn.isExactOn_ball` + zero-derivative uniqueness via
  `Convex.is_const_of_fderivWithin_eq_zero`) and `exists_exteriorLogBranch` (the exterior case
  Forster's construction needs, via the inversion `w = 1/z`; the transported function
  `H w := (1-b*w)/(1-a*w)` has genuinely no singularity on `ball 0 ρ⁻¹`, checked directly:
  `1 - a*w ≠ 0` there follows from `‖a‖<ρ, ‖w‖<ρ⁻¹ ⟹ ‖a‖·‖w‖<1`). Zero sorries, mathlib-only, no
  manifold imports (matches `Path/Planar.lean`'s hygiene).
- [abelweak] Jacobian/AbelWeak/WeakSolution.lean OK (214 lines) — `IsWeakSolutionAt`/
  `IsWeakSolutionOfPair` (D1, Forster §20.1), stated with the local-model chart taken
  existentially from `IsManifold.maximalAtlas` and a plain `f =ᶠ[𝓝 a] (...)` eventual-equality
  local model (junk-free, simpler than the design's filter-sup formula). **Gotcha recorded**: the
  design's D1 used `ContDiffAt ℝ ⊤ ψ` for the local-model cutoff; `⊤` in this project's
  `ContDiff`-scope notation means `ω` (real-**analytic**), which is false for a genuine
  `ContDiffBump` (bump functions are never real-analytic) — fixed throughout to `∞` (matching
  `Dbar/Operator.lean`'s own `SmoothC` convention, `ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞`). **SCOPE
  ADDITION** (`docs/design/abel-theorem.md` §1.4/§4.1's finding that Thm 21.4(b) needs the
  `k`-point case, not just two-point): `IsWeakSolutionOfFinset` + `isWeakSolutionOfFinset_prod`
  (Forster's Lemma 20.1, Finset-indexed product of pairwise-disjoint two-point weak solutions).
  Built two reusable chart-bridge Compat lemmas since `ℂ`'s model `𝓘(ℝ,ℂ)` has no registered
  `ContMDiffMul` instance (mathlib only gives `ContMDiffRing 𝓘(𝕜) n 𝕜`, the model over *itself*,
  not `𝓘(ℝ,ℂ)` for `ℂ` as a real algebra): `contMDiffAt_finsetProd_real` (routes finite products
  through `ContDiffAt ℝ` in `extChartAt 𝓘(ℂ) x` via `RS.contMDiffAt_real_iff_contDiffAt` +
  mathlib's generic `contDiffAt_prod`) and the two directions `contDiffAt_comp_symm_of_contMDiffAt`
  / `contMDiffAt_comp_of_contDiffAt` (composing a chart-free `ContMDiffAt` fact with an arbitrary
  *existing* `maximalAtlas` chart, not `extChartAt` — needed because `IsWeakSolutionAt`'s witness
  chart is existential, reused as-is rather than re-charted). Zero sorries.
- [abelweak] Jacobian/AbelWeak/SingleChart.lean OK (285 lines) — the single-chart weak solution
  (§6.2–6.3): `exists_weakSolutionOfPair_chart`. Planar formula
  `g z := if ‖z-c‖≤ρ then (z-eP)/(z-eQ) else exp(ψ(z-c)·L(z-c))` (`ψ : ContDiffBump (0:ℂ)`, `L`
  from `exists_exteriorLogBranch`), consistency on the transition annulus via
  `ψ.one_of_mem_closedBall`/`ψ.zero_of_le_dist` (`Set.EqOn`-rewriting only, no matching argument),
  lifted to `X` via `Set.piecewise e.source (g∘e) 1`. Topology: `U := e.symm''(ball c ψ.rOut)`
  (open, `OpenPartialHomeomorph.isOpen_image_of_subset_source`), `K := e.symm''(closedBall
  c ψ.rOut)` (compact, `IsCompact.image_of_continuousOn`), `closure U ⊆ K` (`closure_minimal`)
  gives `IsCompact (closure U)`. Zero sorries.
- [abelweak] Jacobian/AbelWeak/ChainAssembly.lean OK (166 lines) — three of the four deliverables:
  (1) **SCOPE ADDITION** `exists_weakSolutionOfFinset` (the `k`-point layer), assembled directly
  from `exists_weakSolutionOfPair_chart` (one call per pairwise-disjoint pair — the shape
  `abel-theorem`'s own Thm 21.4(a) disjoint-chart construction produces per its design's §1.4)
  plus `isWeakSolutionOfFinset_prod`; (2) `pathIntegral_eq_sum_chartChain` (§7.2, pure `Path`-API
  telescoping via `IsPrimitiveAlongMap.sub_eq_sub` + a hand-rolled induction — no Stokes, no
  mathlib "telescoping sum" lemma was found generically applicable to `ℂ`, `sum_range_tsub` is
  `OrderedSub`-only); (3) `residue_identity_two_point` + `logDeriv_rat_eq` (§7.3, the
  Lemma-20.3-specialized residue identity), citing `planar-stokes-atoms`' own hypothesis-free
  two-puncture export `RS.integral_wirtingerDbar_mul_inv_sub_sub_inv_sub_eq` directly (no new
  integration atom needed — that unit's own `abel-weak-solutions` refinement, §7.3/§11 risk R1,
  was already exactly what this needed) plus a new small computation (`logDeriv_rat_eq`)
  connecting the abstract two-puncture kernel to a weak solution's own rational-function
  log-derivative. **NOT built**: the fully general multi-chart `exists_weakSolutionOfPair` (an
  arbitrary path, assembled via a full `RS.ChartChain` product) — the design's own risk item 3
  ("internal-breakpoint cancellation bookkeeping... mechanical, ~20 lines") underestimated this:
  adjacent `ChartChain` pieces generally use *different* charts, so showing the product is smooth
  *at* a shared breakpoint needs a "rechart" lemma for `IsWeakSolutionAt` (transporting a
  simple-zero/pole local model across a holomorphic chart transition via mathlib's
  removable-singularity theorem, `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_
  continuousAt`, applied to the transition map's difference quotient). Real, correct, buildable
  content, but did not fit this pass's time budget on top of the rest of the unit. Filed as a
  documented gap (root file + this entry), not a placeholder tactic. Notes for **abel-theorem**:
  its `k`-point/Finset use (§1.4) does NOT need the general case (its own account of Thm 21.4(a)
  is exactly the disjoint-single-chart-per-pair shape `exists_weakSolutionOfFinset` covers); its
  two-point sufficiency direction (§2.1) is the one consumer that would need it — the
  multiplicativity step it would need for the induction (`IsWeakSolutionAt.mul_of_contMDiffAt`,
  `WeakSolution.lean`) is already built; only the adjacent-breakpoint rechart step is missing.
- [abelweak] Jacobian/AbelWeak.lean (unit root) OK (95 lines); `scripts/check.sh Jacobian/AbelWeak`
  passes, zero sorries across all 5 files (947 lines total) + root — unit COMPLETE per the scope
  actually shipped (see the ChainAssembly.lean entry above for the one documented gap). NOT
  registered in `Jacobian.lean` per task hard rule, orchestrator to add `import Jacobian.AbelWeak`.
  Exact export names for **abel-theorem** vs its own design's expectations: `RS.AbelWeak.
  exists_weakSolutionOfPair` (the fully general two-point deliverable its §4.1 proof plan cites)
  is NOT exported — see the gap above; `RS.AbelWeak.IsWeakSolutionOfPair`,
  `RS.AbelWeak.pathIntegral_eq_sum_chartChain` are exported exactly as its design expects; the
  "§7.3 residue identity" it expects is exported as `RS.AbelWeak.residue_identity_two_point` +
  `RS.AbelWeak.logDeriv_rat_eq` (two lemmas, not one, and not literally in `f`'s own vocabulary —
  the caller must supply its own weak solution's `g`/kernel data to invoke them, matching exactly
  what `SingleChart.exists_weakSolutionOfPair_chart`'s construction produces). The k-point layer
  abel-theorem's design expected to build itself, inline, in its own `Sufficiency.lean`
  (`f := ∏ i, f i`) is instead available pre-packaged here as `RS.AbelWeak.
  exists_weakSolutionOfFinset` + `RS.AbelWeak.IsWeakSolutionOfFinset` — abel-theorem should cite
  this directly rather than re-deriving the `Finset.prod` bookkeeping.
- [resthm] Jacobian/ResidueTheorem/RationalOnP1.lean OK (no open goals; ~330 lines) + Jacobian/
  ResidueTheorem.lean (unit root) OK; `scripts/check.sh Jacobian/ResidueTheorem` passes. Per the
  orchestrator addendum, built against the §6 trace-route primary (PoU/Stokes §3-5, the
  Area-Gluing atom, deliberately NOT built). **PARTIAL DELIVERY — read both files' docstrings in
  full before extending.** Delivered: a set of independently correct, reusable atoms toward the
  `ℙ¹` base case (task item 2) — `RS.P1.formOfCoeFn` (two-chart `MFormData` constructor from a
  finite-chart coefficient function), `RS.P1.coeffAt_coe_eq_coeffAt_coe` (ℙ¹'s finite points share
  one raw coefficient function), and the headline new technique,
  `RS.P1.resAt_neg_sq_inv_mul_comp_inv_eq_zero`: the residue at `∞` of an ENTIRE function's
  `invChart` reading vanishes via Cauchy's theorem transported through the `z ↦ z⁻¹` contour
  reindexing (`RS.P1.circleIntegral_inv_eq_neg`) — NOT a polynomial-growth/degree argument, cheaper
  than what `form-trace-tower`'s superseded non-quotient design had budgeted for the same "Liouville"
  step. **NOT delivered**: (1) the `ℙ¹` assembly itself — every other piece (finite-pole-set
  extraction from `θ.divisor`, the principal-part tail as a second `formOfCoeFn` instance, the
  order-≥0-everywhere argument via `MeromorphicAt.orderAt_sub_principalPartAt_nonneg` +
  `Finset.analyticAt_fun_sum`, the `θ.coeffAt ∞` transition-formula bridge) was worked out and
  test-compiled, but the final step needs `Differentiable ℂ R_mid` and the remainder `R_mid`,
  built from bare `MeromorphicAt`-junk-valued subtraction, is only known to have order `≥ 0` at the
  finitely many former poles — NOT necessarily continuous there (`MeromorphicAt`'s witness at a
  positive-order point puts zero constraint on the actual value, since it's multiplied by `0`).
  Fix sketched in `RationalOnP1.lean`'s docstring (weaken the Liouville-free fact to an explicit
  small radius avoiding the finite pole set) but not implemented — genuinely found late in the
  build, after the harder Liouville-free technique itself was already de-risked and working; (2)
  the general-`X` reduction (task items 1/3/4, `residue_sum_eq_zero_of_exists_nonconstant`) — NOT
  EVEN ATTEMPTED IN CODE beyond design-level reading, because `MForm.d f` (canonical-forms) does
  NOT match `resAtX`'s pullback convention (`RS.FormTrace.resAtX`, form-trace-tower) at a pole of
  `f`: `d f`'s coefficient there is `deriv(f)`-shaped (order matching `f`'s own pole, worse), while
  `F^*(dz)`'s (`F := toP1 f`) is `d(1/f)`-shaped (order matching the ramification, generically
  simple) — checked directly, a genuine cross-unit convention mismatch neither unit's design
  anticipated. Closing it needs a dedicated `MForm.ofPullback F` construction (build `F^*(dz)`
  itself as an honest `MFormData`, via `resAtX`'s own per-chart formula) NOT attempted here, before
  the `θ = h • (F-pullback)` reduction (canonical-forms D8) and the `FiberStack` sum-over-fibres
  bookkeeping (design §6.2) on top of that. **Loud flag for the orchestrator**: `serre-duality-tails`
  is the only unit whose frozen edge points here (confirmed by both units' own DAG audits) and its
  one consumption site (`RS.TailDuality.pairT_alpha`, its design §6 P3) is gated on this landing —
  it does NOT land with this delivery. No sorries anywhere; both gaps are honest absences (undecided
  theorems left unstated), not placeholder tactics, per the hard "zero sorries" rule.
- [jfun] Jacobian/JacFunctorial/Pullback.lean OK (301 lines, ~15s) — the centerpiece "easy
  direction": `Form1.pullback f hf : Form1 Y →ₗ[ℂ] Form1 X` (chain-rule pullback of a holomorphic
  1-form along any `f : X → Y`), built via `Form1.ofSectionAnalytic` (pointwise, mirroring
  `mdifferential`'s pattern, NOT `Form1CoeffData`/`ofCoeffs` — that route needs chart restriction
  and gains nothing here), plus `coeffAt_pullback`/`coeffIn_pullback` (chart formulas) and
  `Form1.pullback_id`/`Form1.pullback_comp` (Form1-level functoriality). Needed three new
  `Compat` lemmas not present upstream (recorded in the file, request-worthy for
  holomorphic-forms): `analyticAt_of_mem_maximalAtlas` (two-manifold arbitrary-chart analyticity
  bridge via mathlib's `contMDiffWithinAt_iff_of_mem_maximalAtlas`, generalizing
  `contMDiffAt_iff_analyticAt_of_mem_source` from ℂ-valued targets to any charted target),
  `mfderiv_chartAt_self` (forward-chart analogue of `mfderiv_chartAt_symm_chartAt_self`, via
  mathlib's `mfderiv_extChartAt_self`), `tangentCoord_mfderiv_chart_comp` (two-manifold
  generalization of `tangentCoord_mfderiv_comp`, reading the target through its own preferred
  chart). The "master computation" `coeffInFun_pullbackSection` handles the moving-preferred-
  chart-at-the-image-point subtlety via a `coeffIn_trans` + chain-rule-of-two-transitions
  argument (`deriv_eq_of_eventuallyEq_comp`, an `HasDerivAt.comp`+`congr_of_eventuallyEq`
  helper) — the same technique reused verbatim in `pullback_comp`'s proof. Zero sorries.
- [jfun] Jacobian/JacFunctorial/PullbackIntegral.lean OK (100 lines, ~10s) — path-integral
  naturality: `IsPrimitiveAlongMap.pullback_comp` (needs `ContinuousOn K s` added as an explicit
  hypothesis, absent from the design's sketch but needed exactly like `.comp`/`.rechart`'s own
  continuity hypotheses) and `pathIntegral_pullback` (`pathIntegral γ (Form1.pullback f hf η) =
  pathIntegral (γ.map hf.continuous) η`), via `exists_isPrimitiveAlong` + a hand-proved
  `(γ.map hf.continuous).extend = f ∘ γ.extend` function identity (`Path.map_coe` + `IccExtend`
  unfolding). Zero sorries.
- [jfun] Jacobian/JacFunctorial/Density.lean OK (113 lines, ~10s) — `Form1.eq_of_eqOn_dense`
  ("Lemma A"). **Deviation from the design**: the design's own sketch proposed routing this
  through a standalone `Form1.continuous_coeffAt : Continuous (fun x => coeffAt x η)`; this
  needs a genuine tangent-bundle fact (continuity of `mfderiv (chartAt ℂ x)` *as its base point
  varies*) that does not reduce to anything already built anywhere in this project (investigated
  `ContMDiffOn.continuousOn_tangentMapWithin`, `ContMDiffAt.mfderiv_const`/`.mfderiv_apply`/
  `inTangentCoordinates` at length — every natural instantiation degenerates to a tautological
  `mfderiv e₀ x ∘L mfderiv e₀.symm (e₀ x) = id`, not isolating the needed factor). **Avoided
  entirely**: compare `η`/`η'` against one *fixed* reference chart `e₀` and cancel a provably-
  nonzero transition factor (`coeffAt_eq_deriv_mul_coeffIn` + `deriv_transition_ne_zero`, both
  pure algebra via `coeffIn_trans`/`analyticAt_transition`, no continuity-in-the-basepoint
  needed), reducing to a comparison of `coeffIn e₀ η`/`coeffIn e₀ η'` — genuinely continuous
  PLANAR functions (`Form1.continuousOn_coeffIn`, already built) — on a dense subset of
  `e₀.target`, closed via a direct `tendsto_nhds_unique_of_eventuallyEq` filter argument
  (`ContinuousOn.eqOn_of_subset_closure` + `target_subset_closure_image_inter`, the latter
  transporting density through the chart homeomorphism). Zero sorries — this fully replaces and
  discharges what the design flagged as a to-be-confirmed `Continuous.ext_on` risk (R3), with a
  cleaner, gap-free route.
- [jfun] Jacobian/JacFunctorial/PeriodMaps.lean OK (92 lines) — the pushforward half of §8:
  `periodCoordEquiv` (`Basis.dualBasis.equivFun`, spiked in `scratch_jfun.lean`, confirmed
  compiling as designed), `pushforwardT` (via `Form1.pullback`'s `dualMap`),
  `pushforwardT_periodVector` (naturality of `pushforwardT` on period vectors, from
  `pathIntegral_pullback`), `periodSubgroup_le_comap_pushforwardT` (`hT`, exact membership via
  the basepoint-flexible `periodVector_mem_periodSubgroup` — no closure/density needed, matching
  the design's own "easy direction" assessment), and the assembly `Jacobian.pushforward` via
  `Jacobian.inducedHom`. **UNIVERSE GOTCHA for siblings (hard-won — cost hours of misdiagnosed
  build time, initially blamed on heartbeats):** `Jacobian.inducedHom`
  (`JacobianConstruction/Functorial.lean`) is declared for `X Y : Type u` in the SAME universe.
  Instantiating it at `X : Type*`/`Y : Type*` (which allocate DISTINCT universe metavariables
  u_1/u_2) does not fail cleanly with a universe error — the elaborator instead grinds through
  `ULift`/quotient `isDefEq` unfolding indefinitely (>40 min CPU observed without terminating;
  no `maxHeartbeats` value helps, `0` just runs forever). Fix: declare ONE shared `universe u`
  and put both surfaces in `Type u` for any declaration mentioning `Jacobian X` and `Jacobian Y`
  together — elaboration then takes milliseconds, no heartbeat bump needed at all. (The
  `scratch_jfun.lean` spike had silently sidestepped this by using `{X Y : Type}` — Type 0 —
  which is why the design phase never saw it.) Zero sorries.
- [jfun] Jacobian/JacFunctorial/Challenge.lean OK (49 lines) — `Jacobian.pushforward_contMDiff`
  (free one-liner from `Jacobian.contMDiff_inducedHom`; same shared-universe convention as
  `PeriodMaps.lean`, see the universe gotcha above). Zero sorries.
- [jfun] Jacobian/JacFunctorial.lean (unit root) — API docstring + LEDGER written; imports all
  five files above. **Unit INCOMPLETE, by design/necessity, not oversight**: `Form1.trace`
  (branch-point analyticity — the naive `traceZkForm` value at a branch coordinate does not equal
  the removable singularity's actual limit for multiplicity > 1, needing a genuine value-*repair*
  construction beyond a closed-form identity, per `RS.FormTrace.traceZkForm_hAdapted_eq_apply`'s
  own `w ≠ 0` guard), `Jacobian/JacFunctorial/TraceIntegral.lean` (the `FiberChain`/monodromy
  construction, the design's own highest-risk item, ~150-200 new lines, downstream of
  `Form1.trace` anyway), `Jacobian.pullback`, `pullback_contMDiff`, `pullback_id_apply`,
  `pullback_comp_apply`, `pushforward_pullback` (all need `Form1.trace`), and
  `pushforward_id_apply`/`pushforward_comp_apply` (need `Torus.inducedHom_id`/`_comp`, confirmed
  ABSENT from `Jacobian/JacobianConstruction/Torus.lean` — the design doc's claim that a request
  was filed for these is stale, `docs/requests/jacobian-construction.md` does not exist) are
  **not built**, reported loudly per the stuck→blocker protocol rather than left as silent gaps
  or filled with sorries — request NOW actually filed at `docs/requests/jacobian-construction.md`,
  and the `Compat` chart-bridge lemmas flagged at `docs/requests/holomorphic-forms.md`.
  **`scripts/check.sh Jacobian/JacFunctorial` PASSES**: builds clean (2917 jobs), zero sorries
  across all 5 files + root (774 lines) — the full pullback-of-forms + path-integral-naturality +
  pushforward-on-Jacobians chain is delivered complete. NOT registered in `Jacobian.lean` per
  task hard rule. Full detail and recommended next steps in the builder's final report.
- [ltails] Jacobian/LaurentTail/TailSpace.lean OK (150 lines, was 154 — a small net simplification)
  — continuation build. `TailAt p D` changed from a plain `def` to **`abbrev`** (matching `T D`'s
  own D2 convention exactly), and its two hand-written `instAddCommGroupTailAt`/`instModuleTailAt`
  instances **removed** (found automatically through the now-transparent quotient). Root cause:
  `Submodule.liftQ`'s output type and the previously-opaque `TailAt p D` do not unify even though
  definitionally the same quotient (confirmed via `apply`'s own unification trace: same quotient
  type shown on both sides, different-though-propositionally-equal instance terms) — needed for
  `Comparison.lean`'s `tailAtToH1`. Reverified `Truncation.lean` still builds clean after the
  change (zero sorries, no regressions to `TailAt.mk`/`windowAt_toTailAt`'s existing proofs).
- [ltails] Jacobian/LaurentTail/Comparison.lean OK (830 lines, was 224 mid-edit at session start)
  — **`tailToH1 : T D →ₗ[ℂ] Cech.H1 D` now FULLY BUILT, zero sorries** (this was the unit's
  hardest genuinely-new mathematical content, and the previous builder's own file-end note had
  reported it entirely unbuilt, citing "needs adapted-cover realization machinery beyond this
  unit's remaining time budget" — that budget wall is now cleared). Route: a from-scratch
  per-point Mittag-Leffler class `mlClassAt D p ψ : H1 D` via a 2-member cover `{V, X∖{p}}`
  (`pairCover`/`gOf`, reusing the previous builder's own machinery) on a neighbourhood `V`
  simultaneously clean for `ψ` and avoiding `D`'s other poles (`cleanNbhd`), typed at an
  auxiliary divisor `DPrimeOf D p ψ` (`D` bumped at `p` to `nOf D p ψ`, the least usable bound).
  Proved **independent of every choice** via `mlClassAtOf_agree` (any two valid `(V, D')`
  representations agree — combines a cover-shrink step via `Skyscraper.lean`'s already-built
  `mlClass_res` with a divisor-raise step via a NEW general lemma `mlClass_inclC0` — `Cech.mlClass`
  is invariant under raising a cochain's auxiliary divisor typing on a fixed cover, since only the
  underlying germs matter, not the membership proof), packaged via a new general helper
  `mlClass_congr` (`heq : g = g' → mlClass 𝒰 g hg = mlClass 𝒰 g' (heq ▸ hg)`, `by subst heq; rfl`)
  that sidesteps `rw`/`erw` repeatedly hitting "motive is not type correct" on `mlClass`'s
  dependent `hg` argument. Additivity/`ℂ`-linearity of `mlClassAt` (`mlClassAt_add`/`_smul`) each
  reduce every operand to a **single common** `(V, D')` (neighbourhood intersection, divisor sup)
  via `mlClassAtOf_agree`, then use `gOf`'s own linearity + `mlClass_add`/`mlClass_smul` there.
  Assembled into `tailAtToH1 D p : TailAt p D →ₗ[ℂ] H1 D` (`Submodule.liftQ`, kernel condition
  `mlClassAt_eq_zero_of_mem_ordGe` via `mlClass_eq_zero_of_exists` with the zero witness) then
  `tailToH1 D := DFinsupp.lsum ℕ tailAtToH1`. **Two build-environment gotchas hit and fixed**
  (full post-mortem in the file's own file-end note): (a) `fin_cases i` on `i : Fin 𝒰.n` produces
  `⟨0,⋯⟩`/`⟨1,⋯⟩`, not the `OfNat` literal, silently breaking `rw` against lemmas stated with
  `(0 : Fin 2)` — fixed by stating `gOf`'s value at a literal index as a bare `rfl` fact instead
  of rewriting; (b) **`AddCommGroup (Cech.H1 D)` is not found by plain `inferInstance` through the
  `H1` abbrev** — `Module.DirectLimit.addCommGroup` (`Mathlib.Algebra.Colimit.Module`) takes its
  index family/connecting-maps as *explicit* (re-shadowed) arguments, which defeats automatic
  discovery even with every other needed instance (`DecidableEq`/`Preorder`/`IsDirectedOrder
  (FinCover ⊤)`) in scope — confirmed by an isolated failing `inferInstance` example, fixed by
  registering it as a genuine global instance (`instAddCommGroupH1`) in this file; **flagged as a
  `docs/requests/cech-cohomology.md` item** to register it upstream in `Cech/Colimit.lean` so
  future consumers building `LinearMap`s into `H1 D` don't rediscover this (a `haveI` local-scope
  workaround was tried first and caused a multi-minute `whnf` heartbeat timeout instead of a clean
  error — the global `instance` route is the one that actually works, recorded so no one repeats
  the slow path). **Deferred, exact gates and full completion plans in the file's own file-end
  note**: `tailToH1_alpha` (`tailToH1 D (alphaL D f) = 0`, needed for `H1Tail.toH1` to descend) —
  gated on a new but fully-scoped *multi-point* generalization of this file's *two-point*
  `mlClassAt_add` (a `Finset`-indexed combination lemma, `Finset.induction_on` + an
  `(|S|+1)`-member cover generalizing `pairCover`, mirroring the pattern `Cech.SixTerm.lean`'s own
  `exists_realization` already uses internally); hence `H1Tail.toH1`/injectivity (injectivity is
  otherwise a **direct** consequence once `H1Tail.toH1` exists — `Cech.toH1_injective`/
  `mlClass_eq_zero_iff` both directions are confirmed **landed**, `Injectivity.lean:247`/
  `Skyscraper.lean:176` — the design's own flagged risk R2 is closed upstream); `H1Tail.equiv`.
  Surjectivity separately gated on `dolbeault-comparison`'s Leray theorem
  (`toH1_surjective_of_isGood`), confirmed **not yet on disk** as of this build
  (`Jacobian/DolbeaultComparison/Leray.lean` exists, 345 lines, ends at `exists_crossGlue` — the
  member-gluing step, not yet the surjectivity conclusion) — soft, non-circular dependency per
  the design's own §8 R1. `scripts/check.sh Jacobian/LaurentTail` passes (2890 jobs), zero sorries
  across the whole unit.
- [ltails] Jacobian/LaurentTail/RiemannRoch.lean OK (49 lines, empty of declarations by design) —
  **entirely deferred**: gated on `finiteness-and-chi`'s `Chi.lean` (confirmed absent —
  `Jacobian/Finiteness/` has only `Schwartz.lean`/`BddHolo.lean`/`CompactRestrict.lean`/
  `Chain.lean`; its own root docstring records `TradeBounded.lean`/`H1Finite.lean`/`Chi.lean` as
  gated on `dolbeault-comparison`, itself still absent beyond `Leray.lean`) *and* on
  `Comparison.lean`'s own deferred `H1Tail.equiv`. Every export the design's §4.4 lists (`g0`,
  `H1Tail.finiteDimensional`, `h1tail`, `h1tail_eq_h1`, `firstFormRR`, the tail-level six-term
  restatement) is a pure transport (`Module.Finite.equiv`/`LinearEquiv.finrank_eq`) once both
  gates open — no new mathematics — so per `CONVENTIONS.md` rule 3 ("no vacuous instances"), the
  file states the gates and a verbatim completion recipe rather than shipping an unusable stub.
- [ltails] Jacobian/LaurentTail.lean (unit root) OK (61 lines) — API docstring covering all four
  files' exact export/deferral status; NOT registered in `Jacobian.lean` per task hard rule.
  **Consumer notes for serre-duality-tails** (its own design doc's frozen bank, reconciled): `T D`,
  `TailAt p D`, `alphaL D`, `H1Tail D := T D ⧸ range(alphaL D)` are all available now, zero
  sorries, matching the frozen shapes exactly — serre-duality-tails' own build-wave plan already
  anticipated this (file 1 gates only on `TailSpace.lean`/`Truncation.lean`, NOT `Comparison.lean`)
  and can proceed today. `H1Tail.equiv` (needed to transport serre-duality-tails' dimension counts
  against `finiteness-and-chi`'s χ ledger) is NOT yet available — see `Comparison.lean`'s file-end
  note for the exact multi-point gate; this is the one blocking item for that unit's own
  dimension-counting endgame (its Lemma 3.4/3.6 chain), everything else in its design (the pairing
  itself, `mulInto`, the residue computations) is independent of it. `mulTail`/`mulTailEquiv`
  (design §2 D5) are deliberately not built — `serre-duality-tails` already designed its own
  `mulInto` directly on `T D`/`TailAt p D` as a superseding replacement (its design doc §0.1),
  a genuine scope relief recorded in `TailSpace.lean`'s own docstring, not a shortfall.
  `firstFormRR`/`g0` (riemann-roch's eventual consumer) remain gated on `finiteness-and-chi`.
- [dolb] Jacobian/DolbeaultComparison/Splitting.lean OK (545 lines) — design §4.3/§6.2/§6.3's PoU
  splitting of a `D = 0` Čech cocycle, built in one pass (continuation of the already-BUILT
  `Leray.lean` + `GlueForm01.lean`). Exports: `Z1.repr` (pointwise holomorphic representative,
  `holoRepr` of the cocycle component) + `Z1.repr_contMDiffOn`/`repr_cocycle`/`repr_add`/
  `repr_smul` (the cocycle identity via `evalAt` rigidity, exactly the DiskAcyclic §7.4(a) step-3
  pattern the handoff note predicted); `contMDiffOn_smul_of_tsupport_subset` (the extension-by-
  zero smul lemma, design's hand-assembled `SmoothPartitionOfUnity`-adjacent atom) and a private
  `contMDiffOn_finset_sum` (no generic `ContMDiffOn.sum` found at the pin; proved by
  `Finset.induction`); `SmoothSplitting`/`exists_smoothSplitting` (D5's frozen formula `g i := ∑
  k, p k x • Z1.repr f (k,i) x`, verified against the design's frozen sign exactly);
  `SmoothSplitting.glueData`/`dolbForm`; two new Compat helpers `IsDbarOn.add`/`IsDbarOn.congr`
  (the design's predicted "3-line helper" grew to ~15 lines each once the differentiability side
  conditions for `wirtingerDbar_add` and the chart-transport eventual-equality for `congr` were
  spelled out, but both are genuinely small, general, and reusable); the independence lemmas
  `sub_mem_range_dbar_of_splittings`/`dolbForm_add_sub_mem`/`dolbForm_smul_sub_mem`/
  `dolbForm_mem_range_of_mem_B1`/`dolbForm_res_sub_mem`, EVERY one closing via
  `DbarGlueData.form_unique` exactly as the design promised (construct a candidate splitting/glue
  data, show it solves the SAME local ∂̄-equations as the target via `IsDbarOn.add`/`.congr`, done).
  Zero sorries. Gotchas (new, beyond Leray's/GlueForm01's):
  (1) dot-notation `.evalAt`/`.ord` on a `Submodule`-coerced term fails silently as "invalid
  field" unless the term is FIRST ascribed to the ambient `MeroGermOn X U` type explicitly (e.g.
  `((f : C1 D 𝒰) p : MeroGermOn X (...))`, NOT `((f:C1 D𝒰) p).evalAt x` directly) — the
  intermediate `LinSysOn`/`Z1`-level Submodule coercion needs an EXPLICIT extra ascription before
  dot notation resolves, a step beyond the single-level coe idiom Leray.lean already used.
  (2) `linear_combination h` for a 3-term cyclic identity (`A - B + C = 0` shapes) is extremely
  sign-fragile: get the combination's SIGN wrong (`h` vs `-h`) and the tactic doesn't fail outright
  — it reports "ring failed" with a residual that is exactly DOUBLE the correct one
  (`2*(goal_lhs - goal_rhs)`), a reliable tell to flip the sign and retry, cheaper than re-deriving
  the arithmetic by hand. (3) `Finset.sum_sub_distrib`/`Finset.sum_smul` have EXPLICIT (not
  implicit) `f`/`g` arguments, so using them bare in `calc`/term mode leaves an unapplied Pi-type
  term Lean can't unify with the goal; `rw [Finset.sum_sub_distrib]`/`rw [← Finset.sum_smul]` in
  tactic mode work fine (rw unifies by pattern matching regardless of explicit/implicit-ness).
  (4) `ContinuousLinearMap.mul 𝕜 A c` (`(A→L[𝕜]A)`) + `.contMDiffOn (s := Set.univ)` +
  `ContMDiffOn.comp` is the robust route for "multiply-by-a-fixed-scalar is `ContMDiffOn`" at
  MANIFOLD level (mirrors `SmoothC`'s planar `ContinuousLinearMap.mul ℝ ℂ c` idiom one level up);
  plain `ContMDiffOn.mul`/`contMDiffOn_const.mul` needs a `ContMDiffMul` instance that does NOT
  resolve for `𝓘(ℝ,ℂ)`-model targets at this pin — avoid it for constant-scalar multiplication.
  **Notes for Comparison.lean** (next/final file): `Z1.repr`, `SmoothSplitting`,
  `exists_smoothSplitting`, `SmoothSplitting.glueData`, `dolbForm`, and all five independence
  lemmas are exactly the design's §4.3 export list, verified at these compiled shapes — no drift
  expected in `H01`/`toDolb`/`cechToH01`'s construction.
- [dolb] Jacobian/DolbeaultComparison/Comparison.lean OK (390 lines) — design §4.4/§6.4's
  Dolbeault comparison, `H01`, `toDolb`/`cechToH01` (via `H1.lift`), injectivity, surjectivity,
  `dolbeaultEquiv`, `finiteDimensional_H01`, `exists_dbar_eq_iff`. Zero sorries. The
  `toDolbAll_compat` compatibility obligation for `H1.lift` (§6.4's "pure diagram algebra on cech
  exports (~80 lines)") came in almost exactly that size: common-good-refinement via `.meet` +
  `exists_good_refinement`, then two symmetric `resH1_comp`/`toDolb_res` chains collapsed to the
  SAME `toDolb h𝒲good ∘ resH1 (combined index)` value via `resH1_indep` (Forster 12.3) — the
  frozen recipe worked exactly as designed, no surprises in the mathematical content.
  **Genuine, non-obvious mathlib/Lean gap found and worked around (flagged loudly, HIGH
  visibility for any future consumer of `RS.Cech.H1 D`'s additive structure)**: `AddCommGroup
  (RS.Cech.H1 D)` — needed for `LinearMap.ker_eq_bot`, `Sub`, `LinearEquiv`'s `CoeFun`, etc. —
  does **NOT** resolve via plain `inferInstance`/automatic instance search, even though `H1 D`
  unfolds (it is a reducible `abbrev`) to `Module.DirectLimit (fun 𝒰 => H1Cover D 𝒰) (fun _ _ h =>
  resH1' D h)` and mathlib's `Module.DirectLimit.addCommGroup (G)(f) : AddCommGroup (DirectLimit
  G f)` instance is directly APPLICABLE (confirmed: manually writing
  `Module.DirectLimit.addCommGroup (fun 𝒰 => H1Cover D 𝒰) (fun _ _ h => resH1' D h)` type-checks
  immediately). Root cause (isolated in a throwaway scratch file, deleted after use): that
  instance's hypothesis `[∀ i, AddCommGroup (G i)]` is a `∀`-quantified instance argument, and
  Lean's `synthInstance` does NOT automatically discharge these by "resolve per `i`" the way it
  does for ordinary instance arguments — it only succeeds when a BLANKET instance for the exact
  Pi-type is separately registered, or when the term is built manually (where elaboration handles
  the `∀`-argument by ordinary term elaboration, not `synthInstance`). Fix: registered ONE local,
  named instance in `Comparison.lean`, `noncomputable instance : AddCommGroup (H1 (0 : Divisor
  X))`, built exactly via the manual `Module.DirectLimit.addCommGroup` application (D = 0 only,
  matching this unit's scope) — once THIS is present, all downstream automatic instance search
  (`Sub`, `ker_eq_bot`, `CoeFun` for `LinearEquiv`, …) works normally. **Flagged for the
  orchestrator**: this is really a gap in `Jacobian/Cech/Colimit.lean` (cech-cohomology's file,
  not editable under this unit's hard rules) — cech's own `H1 D` for ARBITRARY `D` would hit the
  identical wall the moment anyone needs `Sub`/`ker_eq_bot` on it (e.g. finiteness-and-chi's
  `H1Finite.lean`, if it ever needs subtraction on `H1 D` rather than only on cover-level
  `H1Cover`/`Z1`/`C1`, which all already have working `Sub`). Two remediations, either fine: (a)
  cech adds `instance : AddCommGroup (H1 D)` (all `D`) to `Colimit.lean` upstream (best, one
  location, then this unit's local `D = 0` instance becomes redundant — safe to delete, since it
  is definitionally the same construction, no diamond); (b) leave as is — every OTHER consumer
  that also needs it registers its own `D`-specific local instance the same way, which is safe
  (same underlying term, no mathematical diamond) but duplicated effort. A request note is left
  here rather than filed separately since `docs/requests/` convention is per-unit and this unit is
  now closing out. Two smaller gotchas: (1) `set_option foo in` must be written BEFORE a
  declaration's docstring (`/-- ... -/`), not after — confirmed AGAIN here (already recorded for
  `serre-duality-tails`) after re-triggering the identical parse error twice while adding heartbeat
  bumps; (2) `Function.Surjective f` for `f : _ →ₗ[R] (M ⧸ p)`-shaped codomains needs the target
  destructured via `Submodule.mkQ_surjective`/the quotient's own `mk_surjective` FIRST (`intro y;
  obtain ⟨x, rfl⟩ := mk_surjective y`) before the element can be used as the underlying
  `Form01`/pre-quotient data the rest of the proof needs — forgetting this step (working directly
  with the quotient-class variable as if it were a representative) produces a confusing type
  mismatch far into the proof rather than at the point of the actual error.
- [dolb] Jacobian/DolbeaultComparison.lean (unit root) OK (37 lines) — API docstring covering all
  four files (`Leray`, `GlueForm01`, `Splitting`, `Comparison`). `scripts/check.sh
  Jacobian/DolbeaultComparison` passes: zero sorries, clean build, across all 5 files (1899 lines
  total: Leray 677, GlueForm01 250, Splitting 545, Comparison 390, root 37). NOT registered in
  `Jacobian.lean` per task hard rule; orchestrator to add `import Jacobian.DolbeaultComparison`.
  **dolbeault-comparison unit now FULLY BUILT** (all 4 planned files + root, matching the design's
  file plan exactly, no files dropped or descoped beyond the already-recorded `finiteDimensional_H01`
  gate).
  **Consumer notes**:
  - **finiteness-and-chi**: unblocked since `Leray.lean` landed (prior build-log entry); no new
    exports from this pass affect it (Splitting/Comparison are downstream of its needs, per design
    §0.1 — confirmed unchanged).
  - **abel-theorem** (its own design's §4.3 "Dolbeault-upgrade bridge", the hardest/highest-risk
    content in that unit): consumes exactly `RS.dolbeaultEquiv : RS.H1 (0 : Divisor X) ≃ₗ[ℂ]
    RS.H01 X`, `RS.H01.mk`, `RS.H01.mk_eq_zero_iff`, and `finiteDimensional_H01`
    (`exists_dbar_eq_iff` is available too, noted in their design as an equally-usable
    alternative). All four are BUILT at exactly the signatures abel-theorem's design doc quotes
    verbatim — **no interface mismatch found**. The one item to flag LOUDLY: abel-theorem's design
    text says "using `finiteDimensional_H01` from dolbeault-comparison" without mentioning any
    gate, but as built here `finiteDimensional_H01` carries an explicit
    `[FiniteDimensional ℂ (H1 (0 : Divisor X))]` hypothesis (see this file's own entry above —
    `Jacobian/Finiteness/H1Finite.lean` had not landed at the time of this build, so the
    unconditional discharge does not yet exist anywhere in the project). abel-theorem's own build
    will need EITHER (a) `H1Finite.lean` to have landed by then, registering
    `FiniteDimensional ℂ (H1 D)` as a genuine `instance` (not just a bare `theorem`) so ordinary
    instance search finds it automatically at their call site, or (b) if it is a `theorem` rather
    than an `instance`, an explicit `haveI := <that theorem instantiated at D = 0>` immediately
    before invoking `finiteDimensional_H01`. Recorded here so abel-theorem's builder is not
    surprised mid-proof.
  - **serre-duality-cech**: `exists_rep_good` (cech) + `h1CoverEquiv` (this unit's `Leray.lean`)
    remain available for pairing well-definedness as previously recorded; `H01`/`dolbeaultEquiv`
    available but the Miranda-tails route remains the frozen path for that unit (no drift).
  - **Nobody else** consumes `H^{0,1}` twisted variants or an `Ω`-sheaf comparison (unchanged from
    the design's §0.2/§7 non-goals).
- [resthm] HEADLINE CLOSED. `Jacobian/ResidueTheorem/` completed against the §6 trace-route
  primary (orchestrator addendum); `scripts/check.sh Jacobian/ResidueTheorem` passes, zero
  sorries across 5 files + root (1692 lines). New files: `MFormCompat.lean` (61 lines —
  `MForm.resAt_eq_zero_of_ord_nonneg`, `MForm.finite_setOf_ord_neg`,
  `MForm.finite_support_resAt`; Compat, upstream candidates for canonical-forms),
  `Calibrated.lean` (303 — `exists_adaptedChartsAt_translated`/`exists_fiberStack_translated`:
  the LocalMultiplicity/MappingDegree existence proofs re-run with the construction-inherent
  "target chart = recentered `chartAt`" conclusion exposed, discharging
  `resAtP1_trace_eq_sum`'s `hcal` calibration hypothesis verbatim), `P1Assembly.lean` (374 —
  **Gap 1 closed**: `RS.P1.sum_resAt_eq_zero (Θ : MForm (OnePoint ℂ)) : ∑ᶠ y, Θ.resAt y = 0`,
  UNCONDITIONAL; the junk-value blocker was repaired via mathlib's `toMeromorphicNFOn`
  (`exists_differentiable_of_ord_nonneg`: entire representative of the principal-part
  remainder, honest near ∞ by the pointwise two-chart `compat` identity `coeffAt_infty_eq`) —
  NOT the weakened-radius variant previously sketched), `Reduction.lean` (541 — **Gap 2
  closed**: NO `MForm.ofPullback` needed; the `d f`-vs-`resAtX` convention mismatch at poles
  IS the `dz = -(w²)⁻¹dw` target transition, handled by pushing TWO trace coefficients
  (`h.holoRepr` over finite fibres, `-(φ.holoRepr)²·h.holoRepr` over the ∞ fibre) along
  `F := toP1 φ.holoRepr`, bridged per fibre point by `resAtX_toP1_eq_of_ord_nonneg`/`_neg`
  and glued on ℙ¹ by `formOfCoeFn` + `trace_const_mul_pullback`; plus `MForm.d_ne_zero`
  (nonconstant ⟹ dφ ≠ 0, identity-theorem dichotomy) feeding D8's `θ = h • d φ`).
  **Exports**: `RS.residue_sum_eq_zero_of_exists_nonconstant (hex : ∃ f : ℳ X, ∀ c : ℂ,
  f ≠ algebraMap ℂ (ℳ X) c) (θ : MForm X) : ∑ᶠ x, θ.resAt x = 0` (THE theorem; `hex` is
  EXACTLY canonical-forms D9's frozen `exists_nonconstant_mero` shape — `Existence.lean` is
  still not on disk (Chi.lean landed, D9 export has not), so the unconditional wrapper is the
  one-liner `residue_sum_eq_zero_of_exists_nonconstant exists_nonconstant_mero θ` for whoever
  lands D9 — orchestrator: consider having canonical-forms add it, or file back here);
  **for serre-duality-tails** (`pairT_alpha`, its design §6 P3):
  `RS.MForm.sum_resAt_eq_zero_of_exists_nonconstant (hex) (f : ℳ X) (θ : MForm X) :
  ∑ᶠ x, (f • θ).resAt x = 0` — the exact `docs/requests/residue-theorem.md` finsum shape;
  also `RS.residueTheorem_of_exists_nonconstant` (Finset-flexible form). NOT registered in
  `Jacobian.lean` per task hard rule.
- [finiteness] Jacobian/Finiteness/TradeBounded.lean OK (607 lines) — the gated centerpiece of
  finiteness-and-chi, unblocked once cech's `SixTerm`/`WindowRank` and dolbeault's
  `Leray.lean` landed. Delivers: (1) §4.4's leftover finite-`Pi` Montel assembly
  `isCompactOperator_resZ_UV`/`isCompactOperator_tradeCompact` (a generic
  `isCompactOperator_pi` lemma for finite index types, via `isCompact_univ_pi` +
  `Filter.iInter_mem`, composed with `Chain.lean`'s single-chart `isCompactOperator_restrictCLM`);
  (2) the Banach↔Čech germ bridges `toGermSub`/`toGermC1`/`toGermZ1`/`boundZ1`/`boundZ1C0`
  (D5), landing in a **generic `coverOfP T P hcov` construction** rather than `T.coverU`/
  `T.coverV`/`T.coverW` directly (needed since those are indexed by an ABSTRACT `𝒰 : FinCover ⊤`
  in a naive formulation, which fails to typecheck: `NZ1 T 𝒰.U` requires `𝒰.n = T.n`
  definitionally, false for a free `𝒰` variable); (3) `trade_evalAt`/`Z1.rel_res_evalAt`
  (the "repr_cocycle" pattern: evaluate a `Z1`-cocycle relation or the trade equation
  pointwise via `MeroGermOn.evalAt`, needed Compat lemmas `MeroGermOn.evalAt_neg/_sub/_zero`
  and `LinSysOn.ord_nonneg`); (4) **`tradePi_surjective`** (Forster 14.6(a) upgraded to the
  Banach layer, §5 steps 1-6, consuming dolbeault's `exists_trade` at the good cover
  `T.coverStar`); (5) `classMap`/`classMap_tradeDiff_eq_zero`/`classMap_surjective` (§5 steps
  8-9, the two Schwartz-consumer properties, the second via a second `exists_trade`
  application at `T.coverW` plus the germ-roundtrip lemma `toGermZ1W_boundZ1`). Zero sorries.
  **The load-bearing gotcha, discovered and worked around repeatedly** (flagged for ANY future
  unit manipulating `Z1 D 𝒰`/`LinSysOn`/`MeroGermOn` values across *definitionally-but-not-
  syntactically* equal `FinCover`/`Opens` arguments): a DOUBLY-NESTED type ascription
  `((e : A) : B)` where `e`'s natural type needs TWO coercion/defeq steps to reach `B` (e.g.
  `Z1 D 𝒰 → C1 D 𝒰 → (ascribe LinSysOn at a different-but-equal domain) → (ascribe further to
  MeroGermOn)`) triggers either a hard `isDefEq` REJECTION or a multi-minute stall, even though
  EACH INDIVIDUAL step, done as a SEPARATE named `def`/`have` (forcing full elaboration to a
  concrete intermediate type before the next coercion), is instant. Fix pattern used throughout
  (`starPairMem`/`starPairGerm`, `cC1`/`cCompMem`/`cComp`, `vMem`/`vGerm`, `wPairMem`/`wPairGerm`):
  split into TWO one-step named `def`s, never write the combined ascription inline. A second,
  unrelated gotcha: `exists_trade`/`resZ1`/`resH1` calls with `τ := id` positioned BEFORE the
  `hτ : IsRefIdx 𝒰 𝒱 τ` argument (in the natural left-to-right call order) let Lean's elaborator
  prematurely unify `𝒱 := 𝒰` from `id`'s domain/codomain equality *before* `hτ` is even looked
  at, silently producing the WRONG cover; fix: name `𝒰`/`𝒱` (and often `D`) explicitly via
  `(𝒰 := ...) (𝒱 := ...)` at the call site, e.g. `exists_trade (𝒰 := T.coverStar)
  (𝒱 := T.coverW) (D := ...) (h𝒰 := ...) (hτ := ...) (τ := id) (f := ...)`.
- [finiteness] Jacobian/Finiteness/H1Finite.lean OK (82 lines) — `toH1_coverW_surjective`
  (push Leray's `T.coverStar`-level surjectivity down along `T.ref_star_W`),
  `finiteDimensional_h1Cover_W` (the Schwartz cospan assembly, one line combining
  `TradeBounded.lean`'s five exports), **`finiteDimensional_H1_zero`** (the unit's headline
  instance), **`finiteDimensional_H1`** (all-`D`, via cech's six-term fragment — `D' := D ⊔ 0`,
  `H1Incl_surjective` caps `H1 D'`, `ker(H1Incl D h) = range(windowConnect h)` via
  `LinearMap.exact_iff` caps the gap). Zero sorries. **Gotcha, confirmed and resolved** (cech's
  own build-log flagged this but left it unresolved): `AddCommGroup (H1 D)` genuinely does NOT
  resolve via `inferInstance`/`infer_instance` at ANY heartbeat budget (not a timeout — a
  real "can't find" failure, root-caused to the `∀ 𝒰, AddCommGroup (H1Cover D 𝒰)` hypothesis
  `Module.DirectLimit.addCommGroup` needs, which typeclass search can't discharge automatically
  even when the pointwise fact is separately provided as a local `haveI`). Fix: register
  `addCommGroup_H1 (D) : AddCommGroup (H1 D) := Module.DirectLimit.addCommGroup (fun 𝒰 => ...)
  (fun _ _ h => resH1' D h)` as a **global `noncomputable instance`** (a `def`/local `haveI`
  is NOT enough — the `FiniteDimensional`/`Module.Finite` abbrevs need the instance findable
  at the TYPE-elaboration stage of the theorem *statement* itself, before any tactic runs).
  Once registered globally, its `.toAddCommMonoid` IS `rfl`-defeq to the `Module.DirectLimit.
  addCommMonoid` instance already baked into `H1Incl`'s type (verified directly) — so
  `FiniteDimensional.of_linearMap_ker_range (H1Incl D h)` typechecks with NO further diamond,
  *provided* no competing local `haveI` for the same instance shadows the global one (a local
  `haveI := addCommGroup_H1 D` inside a proof that ALSO has the global instance in scope causes
  a spurious "synthesized instance is not definitionally equal" error — drop the redundant
  local `haveI` once the global instance is registered).
- [finiteness] Jacobian/Finiteness/Chi.lean OK (205 lines) — `finiteDimensional_linSys` (all-`D`
  finiteness of `L(D)`, same six-term recipe as `H1Finite.lean` applied to `windowMap` instead
  of `H1Incl`), the χ ledger `h1`/`chi`, `sixterm_ranks` (the shared rank-nullity bookkeeping,
  split into three independent private lemmas `sixterm_rank1/2/3` — bundling them into one
  `refine ⟨p, q, ?_, ?_, ?_⟩` with `p`/`q` as `set`-bound locals caused HYPOTHESES from one
  bullet's `set ... with h_def` to leak into sibling bullets' `omega` calls as spurious extra
  atoms, once via cross-bullet contamination that took several iterations to diagnose; three
  fully separate top-level lemmas sidestep it entirely), `chi_of_le`/`chi_single_add`
  (needs a `degree_single` Compat lemma, `Function.locallyFinsuppWithin.single` not upstreamed
  with a degree fact)/`chi_eq_chi_zero_add_degree`, **`chi_zero_add_degree_le_l`** and
  **`exists_ne_zero_mem_linSys`** (canonical-forms' §D9 Existence-gate names, verified against
  `docs/design/canonical-forms.md` §1.5's frozen quote — exact match), `l_mono`/
  `l_le_l_add_degree`/`h1_le_of_le`/`h1_le_h1_add_degree`. Zero sorries. Needs `[ConnectedSpace X]`
  on `finiteDimensional_linSys`/`sixterm_rank1`/`sixterm_rank2`/`chi`/`chi_of_le` and everything
  downstream (Liouville, via `L(0) = span{1}`, is the base case for `L(D')`'s finiteness) —
  `sixterm_rank3`/`h1_le_of_le`-style h1-only facts do NOT need it (H1's finiteness is
  unconditional per `H1Finite.lean`). Small gotcha: `Module.finrank_top`'s actual name is
  bare root-level `finrank_top` (not `Module.finrank_top`), despite living in a file that
  mostly uses the `Module.` prefix convention.
- [finiteness] Jacobian/Finiteness.lean (unit root) OK — `scripts/check.sh Jacobian/Finiteness`
  passes: builds clean, **zero sorries** across all 7 files + root (1964 lines total:
  Schwartz 213/BddHolo 330/CompactRestrict 126/Chain 401/TradeBounded 607/H1Finite 82/Chi 205).
  **Unit COMPLETE** — both gates (cech six-term, dolbeault `Leray.lean`) closed during this
  pass. NOT registered in `Jacobian.lean` per task hard rule (already imported there from a
  prior session, unchanged). **Notes for canonical-forms**: the Existence gate is now OPEN —
  `chi_zero_add_degree_le_l (D : RS.Divisor X) [ConnectedSpace X] : chi (0:RS.Divisor X) +
  D.degree ≤ (RS.l D : ℤ)` and `exists_ne_zero_mem_linSys [ConnectedSpace X] {D}
  (h : 0 < chi (0:RS.Divisor X) + D.degree) : ∃ f ∈ RS.LinSys D, f ≠ 0` exist at EXACTLY the
  names/shapes `docs/design/canonical-forms.md` §1.5/§D9 record (frozen quote verified against
  source at write time); `finiteDimensional_linSys`/`l_mono` also ready. **Notes for
  riemann-roch**: `chi_eq_chi_zero_add_degree (D) : chi D = chi (0:RS.Divisor X) + D.degree`
  is the frozen shape (their RR statement is this plus tail-Serre's `h1 D = l(K-D)` and
  cech-h1-genus's `h1 0 = g`); `h1`/`chi` definitions frozen as `chi D := (l D:ℤ) - (h1 D:ℤ)`.
  **Notes for laurent-tails**: `finiteDimensional_H1 D` (instance, unconditional — no
  `ConnectedSpace` needed), `h1`, `h1_le_of_le`. **Notes for tail-duality/serre-duality-cech**:
  `finiteDimensional_H1 D` discharges their pairing-nondegeneracy finiteness hypothesis
  directly as an instance (no extra argument needed at call sites).
- [abelweak] Jacobian/AbelWeak/Rechart.lean OK (190 lines) + Jacobian/AbelWeak/GeneralChain.lean OK
  (505 lines) — **the general multi-chart `exists_weakSolutionOfPair` gap CLOSED** (task: closure
  authorized inside `Jacobian/AbelWeak/` by the `abel-theorem` builder, per this unit's own
  documented gap in `ChainAssembly.lean`/root docstring). `Rechart.lean`: the "rechart" lemma
  (`exists_localModel_of_isWeakSolutionAt`, `IsWeakSolutionAt`'s local model transports across ANY
  two `maximalAtlas` charts at the same point) via mathlib's removable-singularity theorem —
  transition map `S := e ∘ e'.symm` is holomorphic (`IsManifold`'s groupoid compatibility +
  generic `contMDiffAt_iff_contDiffAt`), its `dslope` is analytic
  (`HasFPowerSeriesAt.has_fpower_series_dslope_fslope`) and NONZERO at the transition point (chain
  rule on `T ∘ S = id`, `T` the reverse transition), `sub_smul_dslope` (unconditional, no `b = a`
  case split) gives the factorisation needed to rewrite the local model. Consumer:
  `IsWeakSolutionAt.mul`, fully general order-additive multiplication (any `k1, k2 : ℤ`, possibly
  different witness charts), via `Function.update` at the single point `a` (uniformly repairs the
  `zpow`-at-zero junk-value mismatch that occurs exactly when `k1, k2 ≠ 0` and `k1 + k2 = 0` — the
  `+1`/`-1` cancellation every interior `ChartChain` breakpoint needs). `GeneralChain.lean`:
  `exists_weakSolutionOfPair {P Q} (hPQ : Q ≠ P) (δ : Path Q P) : ∃ f U, IsWeakSolutionOfPair f P Q
  ∧ IsOpen U ∧ IsCompact (closure U) ∧ P ∈ U ∧ Q ∈ U ∧ (∀ x ∉ U, f x = 1)` (exact design shape) —
  strong induction along a `RS.ChartChain δ`, gluing one fresh `SingleChart` piece per link via
  `IsWeakSolutionAt.mul` applied at up to 3 points per step (chain basepoint `M 0`, outgoing
  endpoint `M m`, new endpoint `M (m+1)` — `M 0` can coincide with either, handled by 3 exhaustive
  cases via `merge_two`/`merge_two'`/`chainFinish`/`chainFinishSame`, INCLUDING the path-revisits-
  its-own-basepoint edge case). `Q ∈ U` tracked throughout (seeded by a small chart-ball `B0 ∋ M 0`
  at the base case); `P ∈ U` via contradiction (nonzero-order weak solutions genuinely vanish at
  their own point, via new helper `IsWeakSolutionAt.apply_eq_zero_of_ne_zero`). Small reusable
  helpers also exported: `isWeakSolutionAt_zero_of_ne`, `IsWeakSolutionAt.contMDiffAt_and_ne_zero_
  of_zero`, `IsWeakSolutionAt.contMDiffAt_of_nonneg`, `IsWeakSolutionAt.congr_of_eventuallyEq`,
  `isWeakSolutionAt_one_zero`. GOTCHA for siblings: no `ContMDiffMul 𝓘(ℝ, ℂ) ∞ ℂ` instance exists
  at this pin (matches `WeakSolution.lean`'s own finding) — `ContMDiffAt.mul`/`.pow` fail to
  synthesize; route through `RS.contMDiffAt_real_iff_contDiffAt` (2-ary product, new Compat
  `contMDiffAt_mul_real`) or `contMDiffAt_finsetProd_real` (n-ary, e.g. for `(e·-ea)^n` as an
  n-fold `Finset.prod`) instead. Zero sorries; `scripts/check.sh Jacobian/AbelWeak` passes (1547
  lines total across all 6 files + root). Root docstring and `ChainAssembly.lean`'s own status
  note both updated to record the closure (no more "NOT built" framing anywhere in the unit).
- [canon] Existence.lean OK — `Jacobian/CanonicalForms/Existence.lean` (D9, the unit's
  raison d'être; gate `Jacobian/Finiteness/Chi.lean` landed): `Function.locallyFinsuppWithin.
  degree_single (P) (n) : (single P n : Divisor X).degree = n` (Compat, generalizes
  `Finiteness.degree_single`'s fixed `n = 1`; closes the §1.6 gap honestly — no separate
  `Divisor.single` constructor was ever needed, mathlib's own `single` already lands in
  `locallyFinsuppWithin univ Y`, definitionally `RS.Divisor X`); `MForm.d_ne_zero` (MOVED here
  from `residue-theorem/Reduction.lean` — that proof used only canonical-forms/meromorphic-and-
  divisors machinery, and residue-theorem is downstream of canonical-forms, so importing it back
  would cycle; `Reduction.lean` now imports it from here, call site unchanged);
  **`exists_nonconstant_mero`**/**`exists_ne_zero_mform`** at the exact frozen shapes (Forster
  16.11 pattern: `D := single P (|chi 0| + 2)` gives `chi 0 + D.degree ≥ 2`, so
  `chi_zero_add_degree_le_l` forces `l D ≥ 2 > 1 = l 0`, hence `LinSys 0 = span{1} ⊊ LinSys D`
  by `SetLike.exists_of_lt`, giving a witness outside every constant); `exists_canonicalDivisor`
  (D10 existence corollary). Zero sorries. `scripts/check.sh Jacobian/CanonicalForms` passes —
  unit COMPLETE (D1–D13 all proved, 8 files). Root docstring updated (no more "IN FLIGHT"/
  "UNWRITTEN" framing).
- [resthm] unconditional — `Jacobian/ResidueTheorem/Unconditional.lean` (new file): now that
  canonical-forms' D9 has landed, `RS.residue_sum_eq_zero (θ : MForm X) : ∑ᶠ x, θ.resAt x = 0`
  is the one-liner `residue_sum_eq_zero_of_exists_nonconstant exists_nonconstant_mero θ`; also
  unconditional `RS.MForm.sum_resAt_eq_zero (f) (θ) : ∑ᶠ x, (f • θ).resAt x = 0` (the
  tail-duality shape serre-duality-tails' `pairT_alpha` should thread instead of the conditional
  `MForm.sum_resAt_eq_zero_of_exists_nonconstant`) and `RS.residueTheorem` (Finset-flexible).
  `Reduction.lean` updated: imports `Jacobian.CanonicalForms.Existence`, its local
  `MForm.d_ne_zero` proof removed (now resolves via that import, call site unchanged). Root
  docstring updated. Zero sorries; `scripts/check.sh Jacobian/ResidueTheorem` passes.
- [abel] Jacobian/Abel/Loops.lean OK (94 lines) — `mem_periodSubgroup_iff_exists_loop`
  (`AddSubgroup.closure_induction`, case tags `zero`/`add`/`neg` not `one`/`mul`/`inv` for the
  additive version — a naming gotcha for siblings) and `exists_zeroPeriod_path` (loop
  cancellation via `RS.period_conj` + linearity of `RS.pathIntegralₗ` through `(RS.basis X).ext`,
  NOT `Basis.ext` unqualified — the real name is `Module.Basis.ext`, only reachable by dot
  notation on a `Basis` term since the file nests `namespace Basis` inside `namespace Module`).
  Zero sorries.
- [abel] Jacobian/Abel/WeakToMero.lean OK (93 lines) — `wirtingerDbar_exp_neg_mul_eq_zero` (the
  `∂̄F = 0` computation for `F := exp(-u)*f`; needed a NEW holomorphic-outer chain rule for
  `wirtingerDbar` not present in `Dbar/Wirtinger.lean`, built here via mathlib's
  `HasDerivAt.comp_hasFDerivAt` — `Complex.hasDerivAt_exp` composed with an arbitrary
  `HasFDerivAt`, giving `∂̄(exp∘v) = exp(v z)·∂̄v`) and `genus_eq_zero_of_exists_simple_pole`
  (Forster's necessity shortcut, a direct composition of two ALREADY-BUILT facts from
  `proper-map-degree`/`sphere-topology`; confirms the design's finding that `form-trace-tower`
  is not needed). Zero sorries.
- [abel] Jacobian/Abel/Sufficiency.lean — `exists_mero_of_pathIntegral_mem` built through step 4
  of the design's own proof plan (loop cancellation + weak-solution existence, both zero-sorry);
  **ONE precisely-isolated `sorry`** for steps 5-7 (the Dolbeault-upgrade bridge): confirmed at
  build time that `serre-duality-tails` (`Jacobian/TailDuality`, `resEquiv`/`i_neg_eq_h1`) has
  **no directory on disk at all** — not "designed, not built", genuinely not started — and its
  interface cannot even be stated without that unit's own vocabulary (`H1Tail`, `pairT`), so the
  gap cannot be narrowed further by this builder (out of authorized scope: `Jacobian/Abel/` + the
  one `Jacobian/AbelWeak/` rechart gap, not a whole sibling unit). Re-checked for its landing
  twice during this session (once before starting, once at the end, per task instructions) —
  still absent both times. `genus_eq_zero_of_pathIntegral_mem` composes it with the zero-sorry
  necessity shortcut. **NOT built**: the `k`-point Finset generalization
  (`exists_mero_of_periodVector_mem`) — did not fit this pass's time budget; mechanical
  (`Finset`-indexed) once the two-point case's blocker clears, per the design's own estimate.
- [abel] Jacobian/Abel/OfCurveInj.lean OK (structure; inherits `Sufficiency.lean`'s one `sorry`
  transitively, no new one) — `Jacobian.ofCurve_inj'` (gated on
  `[DiscreteTopology (RS.periodSubgroup X)]`, Forster 21.4(i) exactly, via
  `AddSubgroup.isClosed_of_discrete` + `topologicalClosure_minimal`/`le_topologicalClosure`
  antisymmetry — the design's own §9 spike, confirmed to compile as stated) and
  `Jacobian.ofCurve_inj` (kept GATED here too, since the design's literal ungated final shape
  cannot even be STATED — Lean has no way to synthesize `[DiscreteTopology (RS.periodSubgroup X)]`
  for a general `X` — until `period-lattice-rank` registers it as a global `instance`; final
  assembly's job, documented precisely in the root file, not new proof work once that instance
  exists).
- [abel] Jacobian/Abel.lean (unit root) — **PARTIAL UNIT**, one documented `sorry` (see above),
  everything else zero sorries. `scripts/check.sh Jacobian/Abel` reports exactly the one flagged
  line (`Sufficiency.lean:71`); `lake build Jacobian.Abel` (ignoring the sorry check) succeeds
  end-to-end with no errors, confirming every file genuinely compiles. NOT registered in
  `Jacobian.lean` per task hard rule. **Also closed, as separately authorized, the
  `abel-weak-solutions` unit's own documented gap**: `Jacobian/AbelWeak/{Rechart,GeneralChain}.lean`
  (695 lines together) — the general multi-chart `RS.AbelWeak.exists_weakSolutionOfPair`, zero
  sorries, `scripts/check.sh Jacobian/AbelWeak` passes; see that unit's own root docstring and the
  `[abelweak]` entry above for the full mathematical account (a removable-singularity-theorem
  "rechart" lemma + a general order-additive `IsWeakSolutionAt.mul` + a chain induction handling
  the path-revisits-its-basepoint edge case via `merge_two`/`merge_two'`/`chainFinish`/
  `chainFinishSame`). **Notes for period-lattice-rank** (#31, primary consumer) and the final
  `ofCurve_inj` assembly are recorded in full in `Jacobian/Abel.lean`'s own docstring (the
  `k`-point export it needs is NOT built; the `DiscreteTopology` instances it should register;
  the exact final-assembly discharge shape).
- [ltails] FINISHER pass on `Jacobian/LaurentTail/` — three of the unit's four previously-deferred
  items now **CLOSED**, zero sorries, `scripts/check.sh Jacobian/LaurentTail` passes (2990 jobs).
  **`tailToH1_alpha`** (`Comparison.lean`): built the multi-point Mittag-Leffler combination the
  previous builder's own file-end note scoped out — `alphaAuxD`/`alphaPatch`/`mlSumCochain`
  realize `alpha D f`'s finitely-many-marked-points data on one `(|S|+1)`-member adapted cover via
  the *global* `f` itself (`Cech.exists_adapted_refinement`), `CLAIM1` relates each point's
  `mlClassAt` to this big cover via a `pairCover → 𝒱` refinement (`mlClass_res`), a
  `Finset.induction_on` (`main`) combines them via two-argument `mlClass_add`, and the resulting
  single class vanishes directly via `mlClass_eq_zero_of_exists` with witness `f` (off-diagonal
  cover overlaps never meet the marked-point Finset, pure adaptedness — no `D`-side hypothesis
  needed there). **`H1Tail.toH1`/`H1Tail.toH1_injective`**: `H1Tail.toH1` descends via
  `Submodule.liftQ` off `tailToH1_alpha`; injectivity needed a *second*, independent multi-point
  construction (`injPatch`/`injD'`/`injψVD'`/`injG`, `inj_CLAIM1`/`inj_main`/`inj_hcoe`) for an
  *arbitrary* tail datum (no global function available a priori — representatives chosen via
  `TailAt.mk_surjective`, auxiliary divisor via `Finset.sup'` since `RS.Divisor X` has no
  `OrderBot`), landing on `Cech.mlClass_eq_zero_iff`'s `⇒` half (Forster 12.4, confirmed landed at
  `Injectivity.lean:247`) to extract a global witness `φ` with `z = alpha D φ`. Shipped a
  conditional `H1Tail.equiv_of_surjective` (honest, hypothesis-parametrized, `CONVENTIONS.md`
  rule 3) as the bridge for the moment surjectivity lands. **Two build-engineering gotchas hit and
  documented in `Comparison.lean`'s own file-end note** (both cost significant wall-clock time to
  isolate): composing an `Opens X`-level `≤` with a `Set X`-level `⊆` via bare `.trans` causes
  catastrophic `isDefEq`/`whnf` slowdown once surrounding terms are sufficiently abstract
  (confirmed: one lemma this way did not finish in 4,000,000 heartbeats / 7+ minutes; coercing to
  an explicit `Set`-level inclusion *first*, then using plain `Set.Subset.trans`, fixed it in
  under 10 seconds — grep for `).trans (` after an `Opens`-typed term if this resurfaces); a single
  tactic proof accumulating ~25 `have`/`set` steps hits a severe elaboration performance wall
  regardless of `maxHeartbeats` (confirmed: `20,000,000` heartbeats / 10+ minutes still failed) —
  fixed by factoring into separate top-level `def`/`theorem` declarations against explicit
  `variable`/`include` blocks (Lean 4 does **not** auto-include a section `variable` just because
  a declaration's *tactic proof* references it — only type-mentioned variables are auto-included;
  `include` is required for proof-only usage, confirmed by direct experiment), mirroring how
  `tailToH1_alpha`'s own helpers were already structured. **NOT closed: surjectivity of
  `tailToH1`** (item 3) — contrary to the previous builder's framing, this is **not** simply a
  citation to `dolbeault-comparison`'s now-landed Leray theorem (`Jacobian/DolbeaultComparison/
  Leray.lean`, 677 lines, confirmed complete): Leray gives a good-cover representative, but
  collapsing it to marked-point-supported Mittag-Leffler data is a genuinely separate, hard
  analytic fact (comparable to a Mittag-Leffler/Cousin-I existence theorem, classically needing
  meromorphic ∂̄-solving with prescribed principal parts) that is out of this unit's own
  `Jacobian/LaurentTail/`-only edit surface to prove — full risk writeup, the inductive-bootstrap
  route considered and ruled out, and a recommendation (a `Jacobian/Dbar/` ask) are recorded in
  `Comparison.lean`'s file-end note. **`RiemannRoch.lean`**: confirmed `Jacobian/Finiteness/
  Chi.lean` has landed (a sibling unit completed it mid-session; "Unit COMPLETE" per its own root
  docstring) — that gate is open, but the file remains empty since its *sole* remaining gate,
  `H1Tail.equiv` (blocked on the same surjectivity item), is still closed; per `CONVENTIONS.md`
  rule 3 a hypothesis-parametrized restatement here would add indirection for zero benefit since
  the true blocker is identical, so the file states this precisely rather than shipping a stub.
  Root docstring (`Jacobian/LaurentTail.lean`) and `Comparison.lean`'s own top/file-end docstrings
  updated to match. `Jacobian.lean` not touched (already importing `Jacobian.LaurentTail` from
  before this pass). Full project (`lake build Jacobian`, 3283 jobs) reverified green after the
  change.
- [jfun] Jacobian/JacFunctorial/TraceCoeff.lean OK (195 lines) — continuation build (the
  trace/pullback half; the previous builder's precisely-diagnosed blocker, now closed). The
  REPAIRED planar trace coefficient `RS.traceCoeff h k := toMeromorphicNFAt (traceZkForm h k) 0`
  (mathlib's meromorphic normal form supplies the `Function.update`-style repair for free, plus
  `eqOn_compl_singleton_toMeromorphicNFAt`: the repair agrees with `traceZkForm h k` at EVERY
  `w ≠ 0`, not just eventually). Branch-point analyticity by the design's route (a): `h` analytic
  at `0` ⟹ all negative Laurent coefficients of `traceZkForm h k` vanish
  (`laurentCoeffAt_traceZkForm` + `laurentCoeffAt_of_analyticAt`) ⟹ meromorphic order ≥ 0
  (`forall_neg_laurentCoeffAt_eq_zero_iff`, residue-calculus already had the bridge — R2's
  "to-be-confirmed" lemma existed) ⟹ analytic (`MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt`).
  Master lemma `analyticOnNhd_traceCoeff : AnalyticOnNhd ℂ (traceCoeff h k) (ball 0 (ρ^k))` from
  `AnalyticOnNhd ℂ h (ball 0 ρ)`. Plus `traceCoeff_one` (k = 1 repair is literally `h`, via
  `toMeromorphicNFAt_eq_self`) and ℂ-linearity in `h` (off `0` by `traceZk` linearity, AT `0` by
  uniqueness of limits between analytic repairs). Zero sorries.
- [jfun] Jacobian/JacFunctorial/Trace.lean OK (662 lines) — **`RS.Form1.trace (f : X → Y) (hf) :
  Form1 X →ₗ[ℂ] Form1 Y` BUILT** (zero map for constant `f` via a `Classical.dec` dite, matching
  the gist's pullback convention). Coefficient data over `ι := Y`: preferred charts RESTRICTED to
  the canonical stack neighborhoods (`traceChart y := (chartAt ℂ y).restr (stackAt hf hne y).V`,
  `restr_mem_maximalAtlas`), coefficient `traceCoeffFun = ∑ᵢ deriv ψᵢ · traceCoeff(coeffIn (S.A i).e η, kᵢ) ∘ ψᵢ`
  (ψᵢ the branch-target transition). Analyticity on the whole restricted target from
  `analyticOnNhd_traceCoeff` — no case split at branch points. Well-definedness via the CANONICAL
  stack-free coefficient `qCoeff f η e₀ x := (deriv (e₀ ∘ f ∘ (chartAt x).symm))⁻¹ · coeffAt x η`:
  `traceCoeffFun_eq_qSum` (defining coefficient = `∑ᶠ x ∈ f⁻¹{ŷ}, qCoeff` at `ŷ ≠` chart center;
  root-sum reindexed through mtrace's PUBLIC `sum_traceZk_stack` — no private `bijOn` reproof
  needed) and `qSum_trans` (chart transition, valid at ramified fibre points too since ℂ's
  junk-inverse conventions cancel on both sides); `compat` then holds on the overlap minus two
  chart centers and extends by continuity (`ContinuousOn.eqOn_of_subset_closure` + a new
  `open_subset_closure_diff`). Linearity is POINTWISE at the coefficient level (traceCoeff
  linearity) — no density needed. Key exports: `coeffAt_traceForm`,
  `coeffAt_traceForm_of_isRegularValue` (the regular-value formula), `qCoeff_eq_branch_term`,
  `deriv_chartRead_eq_of_adapted` (chart-derivative factorization through adapted charts),
  `deriv_transition_mul` (inverse-transition product). GOTCHA recorded: `multiplicity f (S.pt i)`
  occurs in the TYPE of `(S.A i)` (AdaptedChartsAt's index), so `rw [hm : multiplicity … = 1]`
  hits "motive is not type correct" — worked around throughout via `generalize`-then-rewrite,
  composite-pattern rewrites (`Nat.cast`, exponent-only), or `k = 1`-hypothesis lemmas that
  `subst` a fresh variable (`traceCoeff_eq_of_eq_one`). Zero sorries.
- [jfun] Jacobian/JacFunctorial/TraceLaws.lean OK (295 lines) — `Form1.trace_id` (dense-set
  argument on `univ`; nonconstancy of `id` from `RS.nhdsNE_neBot`), `Form1.trace_comp`
  (`Tr_{g∘f} = Tr_g ∘ Tr_f`; constant cases dispatch through the dite; main case by density on
  the cofinite set avoiding `branchLocus (g∘f) ∪ branchLocus g ∪ g '' branchLocus f`, with
  `qCoeff_comp` chain rule — unconditional thanks to `mul_inv` in ℂ — and `finsum_mem_biUnion`
  fibre regrouping), and **`Form1.trace_pullback`: `Tr_f (f^* η) = (ContMDiff.degree f hf : ℂ) • η`**
  (the projection formula; per-point `qCoeff_pullback` cancellation needs `deriv_chartRead_ne_zero`
  at unramified points, then `ncard_fiber_of_isRegularValue` + density; constant case gives `0 = 0•η`).
  Zero sorries.
- [jfun] Jacobian/JacFunctorial/TraceIntegral.lean OK (479 lines) — the trace–period relation,
  built at the PERIOD level (the design §7's own fallback, evaluated and chosen: it avoids the
  full `FiberChain`/monodromy-cycle machinery entirely). Local sections `sectionAt S i` of `f`
  over regular stacks (all-multiplicity-1: `e' y ∈ e.target`, `f ∘ section = id`, uniqueness,
  `ContinuousOn`); fibre-sum enumeration `finsum_mem_fiber_eq_sum_sectionAt` (5 lines — reuses
  `sum_traceZk_stack` + `traceZk_one` instead of reproving the fibre bijection). **Segment
  lemma** `pathIntegral_traceForm_segment`: over one trace chart the summed per-sheet DISC
  primitives (`exists_hasDerivAt_ball` on the full adapted-chart ball) form a primitive of the
  trace — its `coeffIn` is literally `∑ᵢ (coeffIn η ∘ ψᵢ) · ψᵢ'` at regular centers
  (`traceCoeff_one`), so `isPrimitiveAlongMap_of_ball` + one hand-rolled
  `IsPrimitiveAlongMap` witness give `∫ Tr_f η = ∑ᵢ ∫ (sectionᵢ ∘ p) η`. `TraceChain`
  (Lebesgue subdivision through regular values, mirroring `exists_chartChain`) + `Path.segMap`
  (affine segment reparametrization) + `pathIntegral_segMap` (segment integral via a fixed
  primitive) telescope the loop. **The monodromy-free loop closing** (the build's key
  simplification over the design): conjugate each lifted sheet by FIXED connecting paths
  `PathConnectedSpace.somePath x₀ ·`; the correction terms are fibre sums AS SETS (independent
  of the enumerating stack — the two adjacent stacks enumerate the same fibre), so they
  telescope to `0` around the loop; no cycle decomposition, no `Path.trans` chains, no
  `Path.cast` bookkeeping. Result: `pathIntegral_traceForm_eq_sum_loops` (η-independent based
  loops) and **`periodVector_traceForm_mem`** (EXACT membership in `periodSubgroup X`). Zero
  sorries.
- [jfun] Jacobian/JacFunctorial/PullbackMaps.lean OK (121 lines) — `RS.pullbackT`
  (dual of `Form1.trace` through `periodCoordEquiv`), `pullbackT_periodVector`,
  `periodSubgroup_le_comap_pullbackT` (`hT`: constant case is the zero map; nonconstant case
  conjugates the generator loop to a regular basepoint (`period_conj` + `exists_isRegularValue`),
  perturbs off the finite branch locus (`Loop.exists_homotopic_avoiding` +
  `period_congr_homotopic`), then `periodVector_traceForm_mem` — exact membership, closure only
  used at the very end), and **`Jacobian.pullback : Jacobian Y →ₜ+ Jacobian X`** via
  `Jacobian.inducedHom` (same-universe convention per the recorded gotcha). Zero sorries.
- [jfun] Jacobian/JacFunctorial/ChallengeLaws.lean OK (193 lines) — **`Jacobian.pullback_contMDiff`**
  (inheriting the `[DiscreteTopology (periodSubgroup _).topologicalClosure]` gate transparently,
  like the pushforward), representative-level computation (`Jacobian.exists_rep`,
  `Jacobian.inducedHom_apply_up_mk`), `pushforwardT_id/comp`, `pullbackT_id/comp` (from
  `Form1.pullback_id/comp`, `Form1.trace_id/comp` through `LinearMap.dualMap_id`/
  `dualMap_comp_dualMap`), `pushforwardT_pullbackT_apply` (T-level projection formula from
  `Form1.trace_pullback`), and the four challenge laws + projection formula:
  **`Jacobian.pushforward_id_apply`**, **`Jacobian.pushforward_comp_apply`**,
  **`Jacobian.pullback_id_apply`**, **`Jacobian.pullback_comp_apply`**,
  **`Jacobian.pushforward_pullback`** (`= (ContMDiff.degree f hf) • P`, ℕ-smul transported
  through `mk'`/`uliftUpHom` by `map_nsmul`). Zero sorries.
- [jfun] Jacobian/JacobianConstruction/Torus.lean EDITED (+30 lines, authorized addition per the
  filed request, now marked FULFILLED in docs/requests/jacobian-construction.md) —
  `RS.inducedHom_id`, `RS.inducedHom_comp` (functoriality of the abstract `V ⧸ L →ₜ+ V' ⧸ L'`
  substrate; `ext` + `QuotientAddGroup.induction_on` + `inducedHom_apply_mk`, as the request
  predicted). `scripts/check.sh Jacobian/JacobianConstruction` re-verified (2890 jobs, zero
  sorries, no regressions).
- [jfun] Jacobian/JacFunctorial.lean (unit root) — imports all 11 files, LEDGER REWRITTEN: the
  unit is now COMPLETE (both halves). **`scripts/check.sh Jacobian/JacFunctorial` PASSES**
  (3134 jobs, zero sorries across all files). Full challenge surface delivered:
  `Jacobian.pushforward`(+`_contMDiff`,`_id_apply`,`_comp_apply`), `Jacobian.pullback`
  (+`_contMDiff`,`_id_apply`,`_comp_apply`), `Jacobian.pushforward_pullback` — everything
  `docs/Jacobian_challenge.lean:104-153` demands, modulo the standing
  `[DiscreteTopology (periodSubgroup _).topologicalClosure]` gate on the two `contMDiff`
  statements only (inherited, no new gate). NOT registered in `Jacobian.lean` per task hard rule.
- [tdual] `Jacobian/TailDuality/` OK — the make-or-break unit. `scripts/check.sh
  Jacobian/TailDuality` passes (3049 jobs), zero sorries. Delivers Serre duality via Miranda
  VI.3's Laurent-tail calculus, worked ENTIRELY at the tail level per the orchestrator addendum
  (2026-07-08): does NOT wait on `H1Tail.toH1`'s surjectivity (Serre-circular, out of scope).
  `TailOps.lean`: `truncT`/`mulInto`/`nuL` (+ `nuL_mulInto_inv`), the `LinSys`/order bookkeeping.
  `Pairing.lean`: `readAt`/`pairAtData`/`pairAt`/`pairT` (built on `MFormData` — `MForm` exposes
  only lifted `ord`/`resAt`/`laurentCoeffAt`, no raw `coeffAt` — then descended via
  `Quotient.liftOn`), `pairT_trunc`/`pairT_mulInto`/`pairT_alpha` (the **only** residue-theorem
  citation, via `RS.residueTheorem`), `pairT_ne_zero` (Miranda Thm 3.3 injectivity),
  `resMap`/`resMap_injective`. `Counting.lean`: `instFiniteDimensional_H1Tail` (via
  `H1Tail.toH1_injective` + `Finiteness.finiteDimensional_H1`, the addendum's re-basing),
  `h1T`/`h1T_le_h1`, `nuPairDual`, **`exists_mul_functional_eq`** (Miranda **Lemma 3.4**).
  `Duality.lean`: **`mem_omegaSpace_of_vanishing_ker_trunc`** (Miranda **Lemma 3.6**),
  **`exists_pairT_eq`** (Thm 3.3's surjectivity half — the full PDF 202–203 endgame: Lemma 3.4 +
  inverting `μ_{f₁}` + Lemma 3.6 applied twice), `resMap_surjective`/`resEquiv` (`resMap` is a
  genuine linear ISOMORPHISM `Ω(-D) ≃ₗ Dual(H1Tail D)`, not just a dimension count), and the
  export bank `i_neg_eq_h1T`/`l_sub_eq_h1T`/`h1T_zero_eq_l_K`/`h1T_zero_eq_genus`/`h1T_canonical`.
  **Two build-engineering gotchas hit and documented** (recorded in `TailOps.lean`/`Counting.lean`
  comments for future builders): (1) `omega` (and `guard_target =ₐ`) can desync its atom
  detection when a fact about a divisor-pointwise value (`RS.divisor f p`, `D p`) derived via one
  lemma application is combined directly with a syntactically-different-but-defeq occurrence of
  the same term from a separate `rw` — same statement, same instances, provably equal by `rfl`,
  but NOT merged by `omega`'s atom collection; the fix is to route through a divisor-free generic
  arithmetic helper (`have key : ∀ d : ℤ, ... := fun d hd => by omega`) and connect via `apply`/
  `exact` (full `isDefEq` unification), never `omega` directly, across such a boundary — hit and
  fixed in `TailOps.lean`'s `sub_divisor_le` and `Counting.lean`'s `exists_mul_functional_eq`.
  (2) `rw`/`▸` cannot rewrite a `MForm` argument *inside* a dependent proof term like
  `pairT θ hθ` (motive not type-correct); fixed by a small proof-irrelevance helper
  `pairT_eq_of_eq (hEq : θ₁ = θ₂) (h1) (h2) : pairT θ₁ h1 = pairT θ₂ h2 := by subst hEq; rfl`
  instead. **Honest gap** (flagged, not blocking): the tail-chi ledger's additivity
  (`chiT D = chiT 0 + deg D`) is NOT delivered — `chiT` is defined but its additivity is
  genuinely independent content from Serre duality (Miranda §2.3/2.6 six-term exactness, not
  §3), NOT derivable from `i_neg_eq_h1T` alone; a proof sketch (reusing Cech's `Window`/
  `windowToT`/`windowMap` as the finite-dimensional bridge) is recorded in `Duality.lean`'s file
  docstring. Does not block riemann-roch (#28), which can combine this unit's export bank with
  `Finiteness.chi_eq_chi_zero_add_degree` (Čech-level, already built) directly. Root docstring
  (`Jacobian/TailDuality.lean`) records the exact consumer notes for riemann-roch (#28),
  cech-h1-genus (#27, re-based to `h1T_zero_eq_genus`), and `Jacobian/Abel/Sufficiency.lean`'s
  blocked step (needs `RS.H1Tail.equiv`, unavailable; only `resEquiv`/`H1Tail.equiv_of_surjective`
  exist). `Jacobian.lean` NOT touched per task hard rule (orchestrator's job).
- [rr] Jacobian/TailDuality/ChiLedger.lean OK (new file, 25 files/3050 jobs in the unit, ~6-9s for
  this file) — **THE chiT-ledger closure: the primary math item of this pass.** Closes the ONE
  honest gap `Duality.lean` flagged (chiT's additivity, independent content from Serre duality
  §3, needing Miranda §2.3/2.6's own six-term exactness). Transposes `Finiteness/Chi.lean`'s own
  `sixterm_rank1/2/3` → `chi_of_le` → `chi_eq_chi_zero_add_degree` recipe to the tail level:
  **`H1TailIncl`** (the descent of `truncT` through the `alphaL`-quotients, via `Submodule.mapQ` +
  `truncT_alpha`; surjective since `truncT` already is) and **`windowConnectT := H1Tail.mk D ∘ₗ
  windowToT D D' h`** (Cech's finite `Window D D'` embedded into the tail space via laurent-tails'
  already-built `windowToT`). Both hard exactness facts proved ENTIRELY elementarily, with NO
  reference to Cech's own `H1`/`mlClass`/cochain machinery (confirming the orchestrator's routing
  hint: `H1Tail D` being a literal `T D ⧸ range(alphaL D)` coker, not a colimit, makes this a
  DFinsupp/Submodule bookkeeping exercise): `windowToT_windowMap` identifies `windowMap`'s image
  (embedded via `windowToT`) with `alphaL D` of the same global section directly;
  `windowConnectT_eq_zero_iff`'s harder half reconstructs a global section from a killed window
  class by choosing one representative per marked point (`WindowAt.mk_surjective`) and a two-term
  `MeroGermOn.ord_add` order estimate; `H1TailIncl_eq_zero_iff`'s harder half does the same at the
  `T D`/`H1Tail` level (`TailAt.mk_surjective` per point + `truncAt_mk`/`TailAt.mk_eq_zero_iff`).
  Yields `exact_windowMap_windowConnectT`/`exact_windowConnectT_H1TailIncl` (as `Function.Exact`,
  matching Cech's own naming), `sixterm_rankT1/2/3`, **`chiT_of_le`**,
  **`chiT_single_add : chiT (D + single P 1) = chiT D + 1`**, and **`chiT_eq_chiT_zero_add_degree
  : chiT D = chiT 0 + D.degree`** — the task's two requested headline statements, both delivered.
  Zero sorries. `Jacobian/TailDuality/Duality.lean` and `Jacobian/TailDuality.lean` docstrings
  updated to record the closure (no proof content changed in `Duality.lean` itself).
  `scripts/check.sh Jacobian/TailDuality` re-verified (3050 jobs, zero sorries, no regressions).
- [rr] Jacobian/RiemannRoch/Basic.lean + Jacobian/RiemannRoch.lean (unit root) OK — riemann-roch
  (#28), a thin `omega`-level assembly unit exactly as the blueprint promised, now buildable
  directly off `TailDuality`'s OWN tail ledger (no need for the Čech-level
  `Finiteness.chi_eq_chi_zero_add_degree` fallback the orchestrator's arithmetic warning flagged
  as unsafe — that Čech-vs-tail `h¹` equality is genuinely unavailable and was correctly avoided).
  `chiT_zero : chiT 0 = 1 - g` (`RS.l_zero` + `h1T_zero_eq_genus`); **`riemannRoch {ω₀} (h₀) (D) :
  (l D : ℤ) - l(K - D) = deg D + 1 - g`**; `l_K_eq_genus`; `deg_canonical : deg K = 2g - 2`;
  **`riemann_inequality (D) : deg D + 1 - g ≤ l D`** (unconditional, no reference form). Zero
  sorries. `scripts/check.sh Jacobian/RiemannRoch` passes (3052 jobs).
- [rr] Jacobian/H1Genus/Basic.lean + Jacobian/H1Genus.lean (unit root) OK — cech-h1-genus (#27),
  a thin re-export per the orchestrator addendum's own framing (the blueprint's cup-product/
  monotonicity machinery is unnecessary on the Laurent-tail route this project took):
  **`RS.finrank_H1Tail_zero_eq_genus : finrank ℂ (H1Tail 0) = genus X`**, re-exported from
  `RS.TailDuality.h1T_zero_eq_genus`. Documents the literal Čech-`H¹` statement as open/optional
  (needs `H1Tail.equiv`'s unconditional comparison, gated on `tailToH1`'s out-of-scope
  surjectivity) — does not block anything, the challenge API never mentions Čech cohomology.
  Zero sorries. `scripts/check.sh Jacobian/H1Genus` passes (3052 jobs).
- [rr] Jacobian/GenusSphereHeadline/Basic.lean + Jacobian/GenusSphereHeadline.lean (unit root) OK
  — genus-zero-headline (#30), assembling BOTH already-built halves. Backward:
  `RS.SphereTopology.genus_eq_zero_of_homeo_sphere` (cited directly, sphere-topology). Forward
  (`RS.GenusSphereHeadline.exists_simple_pole_of_genus_eq_zero`): at `D := single P 1` (`P`
  arbitrary, `ConnectedSpace ⟹ Nonempty`), `riemann_inequality` under `genus X = 0` forces
  `l D ≥ 2 > 1 = l 0`; `SetLike.exists_of_lt` on `LinSys 0 < LinSys D` (the
  `CanonicalForms/Existence.lean` pattern, `linSys_zero_eq_span_one` for the properness) extracts
  `φ ∈ LinSys D \ LinSys 0`; `φ.ord ≥ 0` off `P` and `φ.ord P ≥ -1` from `mem_linSys_iff`;
  `φ.ord P < 0` else `φ` would be holomorphic everywhere hence in `LinSys 0 = span{1}`,
  contradiction; combined with `≥ -1`, forces `φ.ord P = -1` exactly (extracting the integer
  witness via `WithTop.ne_top_iff_exists` + `omega`). `RS.homeoSphere_of_exists_simple_pole`
  (proper-map-degree, already built) closes it. **`genus_eq_zero_iff_homeo`** exported at ROOT
  level (no namespace), at the challenge's own EXACT standing variables (no extra `[T1Space X]`/
  `[DecidableEq X]` — `T1Space` free from `T2Space`, `DecidableEq` supplied internally via
  `classical`) — matches `docs/Jacobian_challenge.lean:54-56` verbatim, a direct alias target for
  final assembly. One gotcha hit and fixed: `exact_mod_cast`/`norm_cast` can fail to bridge a bare
  `WithTop ℤ` numeral literal (e.g. `(-1 : WithTop ℤ)`, elaborated via `Neg`/`OfNat`) against an
  `Int`-side goal (produces an `Int.negSucc 0` vs `-1` numeral-normal-form mismatch) — avoided by
  keeping the running hypothesis in the EXPLICIT-cast form `((-1 : ℤ) : WithTop ℤ)` throughout
  (never materializing the bare `WithTop` literal until the final `rw`/`norm_cast` at the very
  end, where it closes cleanly) — spike-verified in a scratch file before use. Zero sorries.
  `scripts/check.sh Jacobian/GenusSphereHeadline` passes (3219 jobs).
- [abel] Sufficiency CLOSED + k-point. `Jacobian/TailDuality` landed (zero sorries) since the
  previous `[abel]` pass, clearing the "entire sibling unit doesn't exist" blocker — but its own
  root docstring flagged that the design's EXACT bridge shape (through `H1Tail.equiv`, the FULL
  unconditional Čech comparison `H1Tail 0 ≃ₗ Cech.H1 0`) still doesn't exist: `LaurentTail.
  Comparison.lean`'s `tailToH1` is only unconditionally INJECTIVE, its surjectivity being a
  genuine out-of-scope Cousin-I/Mittag-Leffler existence theorem. Restated the bridge exactly as
  that unit's consumer note suggested: **new file `Jacobian/Abel/DolbeaultBridge.lean`**,
  `formDualEquiv : Form1 X ≃ₗ[ℂ] Dual (H1Tail 0)` (`holomorphicMFormsEquiv` + `resEquiv 0` + a
  `neg_zero` cast, unconditional) and `exists_dbar_eq_zero_of_forall_basis_pairing_eq_zero`
  (PROVEN, zero sorries) gated ONLY on `Function.Surjective (LaurentTail.tailToH1 (0 : Divisor X))`
  — a genuine, independently-meaningful, non-vacuous hypothesis (`LaurentTail.H1Tail.
  equiv_of_surjective`'s own gate), matching the project's established idiom
  (`Jacobian.ofCurve_inj'`'s `[DiscreteTopology (RS.periodSubgroup X)]`). Proof: `e := H1Tail.
  equiv_of_surjective.symm (dolbeaultEquiv.symm (H01.mk η))`; `e = 0` from `Module.
  forall_dual_apply_eq_zero_iff ℂ` (valid for ANY vector space over a field via `Module.Free.
  of_divisionRing`/`Projective.of_free`, no finite-dimensionality needed) + `(RS.basis X).ext`
  (a linear map vanishing on a basis is the zero map) applied to the composite functional
  `LinearMap.applyₗ e ∘ₗ formDualEquiv`; then chase `LinearEquiv.apply_symm_apply`/`map_zero`
  forward twice to get `H01.mk η = 0`, closed by `H01.mk_eq_zero_iff`. Needed
  `set_option maxHeartbeats 4000000`/`synthInstance.maxHeartbeats 400000` (the `H1 D`
  `Module.DirectLimit` instance search, same gotcha `Comparison.lean` itself already flags) and
  care to avoid `ω` as a bound variable name (clashes with the `ContDiff` scoped notation for
  smoothness order `∞`/analytic, used in `IsManifold 𝓘(ℂ) ω X`).

  **Investigated in full but NOT closed** (genuinely separate, non-external, new-content gap —
  NOT a restatement of the just-cleared blocker): design §4.1 step 5, packaging a weak solution
  `f`'s chart-local `d''f/f` data into one global `η : Form01 X` with a PROVEN vanishing pairing
  against a basis of `Form1 X`. Traced the exact reason it resists a short proof: the "pairs to
  zero" hypothesis has to be established via a genuine Stokes/residue argument tying `f`'s own
  `GeneralChain`-internal chain construction (telescoped via `pathIntegral_eq_sum_chartChain`) to
  the area-integral pairing — `exists_weakSolutionOfPair`'s EXPORTED interface (the bundled
  `IsWeakSolutionOfPair` Prop + `U`-support facts) does not expose enough of the chain's internal
  structure to run this argument as a black box, and re-deriving it independently (e.g. via an
  ad hoc `DbarGlueData`/rotated-`Complex.log`-branch finite cover of `X`, using compactness) is a
  substantial undertaking in its own right, comparable in scope to a further sibling unit, not a
  short remainder — confirmed by working through the construction in detail (recorded in-session,
  not reproduced here) before deciding not to attempt it under time pressure. Step 7 (the CR
  promotion once `u` is in hand) WAS traced to a concrete, tractable recipe — `Jacobian/Dbar/
  Operator.lean`'s `contMDiffOn_omega_of_isDbarOn_zero` (promotes `IsDbarOn F 0` + real-smoothness
  on an open set to genuine `ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω`, already handling the chart-transition
  plumbing) applied on `{Q}ᶜ`, using `wirtingerDbar_exp_neg_mul_eq_zero` (ALREADY BUILT,
  `WeakToMero.lean`) off `{P, Q}` plus a short direct product-rule computation
  `wirtingerDbar f P = 0` (from `f`'s own `IsWeakSolutionAt f P 1` local model, no rechart needed)
  to extend across `P`; order bookkeeping via `ordAtX_eq_of_mem_source`'s chart-invariance (reads
  the order in the SAME chart the weak-solution model uses, no rechart) +
  `meromorphicOrderAt_mul`/`meromorphicOrderAt_zpow_id_sub_const`, and at `Q` specifically via
  mathlib's `Complex.differentiableOn_compl_singleton_and_continuousAt_iff` removable-singularity
  theorem (the same tool `AbelWeak/Rechart.lean` already uses) to extend the local `ψ`-cofactor's
  holomorphy across the puncture — but this was not wired up given step 5 was already the
  time-blocking piece, and doing so without step 5 in hand would be unverifiable.

  **Resolution**: isolated the ENTIRE remaining content (steps 5 AND 7 combined — deliberately not
  further split, since step 7's tractability is contingent on step 5's output shape) as one
  explicit, precisely-scoped hypothesis per arity, following this project's own "gated theorem,
  not vacuous, not `sorry`" convention (`CONVENTIONS.md` rule cited by `LaurentTail.Comparison.
  lean`'s own `equiv_of_surjective`): **`RS.Abel.WeakSolutionUpgrade X`** (two-point,
  `Sufficiency.lean`) and **`RS.Abel.WeakSolutionUpgradeFinset X ι`** (`k`-point, same file) —
  both state exactly "given a weak solution (resp. `Finset`-indexed family of weak solutions)
  along path(s) with EXACT zero period against every `ω ∈ Form1 X`, the honest meromorphic
  function exists", i.e. literally design steps 5-7's combined conclusion, with a docstring
  recording the full discharge roadmap above (apply the packaging construction to build `η` +
  its pairing-vanishing, feed it to the NOW-PROVEN `exists_dbar_eq_zero_of_forall_basis_pairing_
  eq_zero`, then run the sketched step-7 recipe). `exists_mero_of_pathIntegral_mem`/`genus_eq_
  zero_of_pathIntegral_mem` (two-point) and the NEWLY BUILT `exists_mero_of_periodVector_mem`
  (`k`-point, previously not built at all) all take the relevant hypothesis and are otherwise
  fully proved, zero sorries — steps 1-4 for both arities (loop cancellation, including a
  from-scratch `k`-point generalization cancelling the TOTAL period against one fixed index via
  `Function.update`/`Finset.add_sum_erase`; a weak solution per pair; Forster's Lemma 20.1
  multiplicativity via the ALREADY-BUILT `isWeakSolutionOfFinset_prod`) are genuinely proved, not
  gated. `OfCurveInj.lean`'s `ofCurve_inj'`/`ofCurve_inj` take `WeakSolutionUpgrade X` as an
  additional explicit hypothesis (propagated, not newly introduced). One Lean gotcha hit while
  building the `k`-point loop-cancellation: `WeakSolutionUpgradeFinset`'s `ι` MUST be an explicit
  parameter of the def (`WeakSolutionUpgradeFinset X ι`, not hidden inside an inner
  `∀ {ι : Type*}`) — otherwise its `Type*` gets auto-bound to its OWN fresh universe parameter at
  `def`-elaboration time, unrelated to the consuming theorem's own `{ι : Type*}`, causing a
  universe-mismatch application error with no informative fix short of this restructuring.
  `Jacobian/Abel.lean` (unit root) docstring updated, gap paragraph dropped. **`scripts/check.sh
  Jacobian/Abel` passes, ZERO sorries** (3270 jobs) — the two-point `sorry` from the previous pass
  is gone; nothing new introduced. Files touched: `Jacobian/Abel/DolbeaultBridge.lean` (new),
  `Jacobian/Abel/Sufficiency.lean`, `Jacobian/Abel/OfCurveInj.lean`, `Jacobian/Abel.lean`
  (imports + docstring), `docs/build-log.md` (this entry). `Jacobian.lean` (root orchestrator) NOT
  touched, per task hard rule; `Jacobian/Abel` is still not registered there (orchestrator's job).
- [plr] `Jacobian/PeriodLattice/` OK — period-lattice-rank (#31), the final deep analytic unit,
  built to the design's exact §6 file plan (`Membership.lean`, `GenericPoints.lean`, `Segment.lean`
  (new, not in the original 5-file plan — the in-chart segment-path + its `pathIntegral` formula,
  factored out once since both `Discreteness.lean` Stage C and `Nondegeneracy.lean` step 2 need the
  identical construction), `FormIdentity.lean`, `Nondegeneracy.lean`, `Discreteness.lean`,
  `FullRank.lean`) + root `Jacobian/PeriodLattice.lean`. **`scripts/check.sh
  Jacobian/PeriodLattice` passes, ZERO sorries** (3279 jobs).
  * **Discreteness (Forster 21.3–21.4(a)(b)) — the unit's centerpiece, GATED**: `GenericPoints.lean`
    proves `exists_genericPoints`/`det_genericMatrix_ne_zero` (§21.3, a strict-descending-finrank
    induction over `genericKernel`, using T2 avoidance `nonempty_open_diff_finite` and a linear
    map/matrix argument via `Fintype.linearIndependent_iff`/`Matrix.exists_vecMul_eq_zero_iff`).
    `Discreteness.lean`'s `exists_isolating_nhds_periodSubgroup` builds Stage A (pairwise disjoint
    chart-ball images via `Set.Finite.t2_separation`, shrinking radii by two nested
    `Metric.isOpen_iff` extractions), Stage B (the local Jacobi map `𝔉 : ℂ^g → ℂ^g`, its
    `HasStrictFDerivAt` built by hand via `HasDerivAt.comp_hasStrictFDerivAt` +
    `hasStrictFDerivAt_apply` + `HasStrictFDerivAt.sum` + `hasStrictFDerivAt_pi`, identified with
    the matrix CLM `(Matrix.mulVecLin A).toContinuousLinearMap` via `ContinuousLinearMap.ext`, det
    transported via `LinearMap.det_toLin'` + `Matrix.toLin'_apply'`, then
    `ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero` +
    `HasStrictFDerivAt.map_nhds_eq_of_equiv` give the isolating neighborhood), and Stage C (given
    a nonzero period `t = 𝔉 w` in that neighborhood, the moved-coordinate index set
    `S := {j | x j ≠ a j}` is nonempty; **`RS.Abel.exists_mero_of_periodVector_mem`, instantiated
    at `ι := ↥S`, GATED on `RS.Abel.WeakSolutionUpgradeFinset X ↥S`**, produces `F : RS.Mero X`
    with prescribed simple zeros/poles; `F • MForm.ofForm1 (basis X k)`'s residues at each `a j`
    are computed via `resAt_analyticAt_mul` + `Mero.ord_eq_meromorphicOrderAt_holoRepr`, and
    `RS.residueTheorem` (now UNCONDITIONAL, per residue-theorem's own landed unit — no separate
    gate needed there, a finding that simplifies the design's original two-gate expectation to
    one) forces `A.mulVec c = 0` for `c ≠ 0`, contradicting `det_genericMatrix_ne_zero`).
    Universe gotcha inherited from `Jacobian/Abel`: `WeakSolutionUpgradeFinset X ι` needs `ι`
    explicit, so the gate is threaded as `RS.DiscretenessHyp X := ∀ S : Finset (Fin (genus X)),
    RS.Abel.WeakSolutionUpgradeFinset X (↥S : Type)`, and every discreteness-adjacent theorem
    (`discreteTopology_periodSubgroup`, `periodSubgroup_topologicalClosure_eq`,
    `discreteTopology_periodSubgroup_topologicalClosure`, `FullRank.lean`'s
    `isZLattice_periodSubgroup_topologicalClosure`/`finrank_int_periodSubgroup`) takes it
    explicitly — exactly Abel's own hypothesis-parameterized idiom, per the task's instruction.
    One extra Lean gotcha: `IsZLattice ℝ L`'s class carries `[DiscreteTopology L]` as a genuine
    instance argument of the *type itself*, so a theorem concluding `IsZLattice ℝ (…).
    toIntSubmodule` cannot discharge that via an internal `haveI` (too late — the type is
    elaborated before the tactic block runs); the fix is a `haveI := discreteTopology_… hupgrade;
    IsZLattice …` **inside the theorem's own type**, a documented but easy-to-miss Lean 4 idiom
    for instance-dependent conclusions.
  * **Nondegeneracy (Forster 21.4(c)) — UNGATED, the design's own routing call vindicated**: the
    maximum-principle route (`Nondegeneracy.lean`'s `form1_eq_zero_of_re_period_eq_zero`) needed no
    Hodge/de Rham/dissection/2-form integral, exactly as designed: a real primitive `F` (built from
    `PathConnectedSpace.somePath`, reusing jaccon's `OfCurve.lean` `Compat` instance) attains a max
    on compact `X`; `AnalyticAt.eventually_constant_or_nhds_le_map_nhds` (mathlib's local open
    mapping theorem) forces the local holomorphic primitive `g` locally constant there (the
    non-constant branch contradicts the max via an explicit `g(e p) + δ/2` witness outside the
    local-max half-plane); `FormIdentity.lean`'s clopen identity-theorem propagation
    (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` on a chart ball) finishes.
    `FullRank.lean`'s `span_real_periodSubgroup` (also ungated) is the linear-algebra shell:
    `Submodule.exists_dual_map_eq_bot_of_lt_top` (vector spaces over a field are projective by
    `inferInstance`) gives a nonzero real functional vanishing on `Λ`; complexifying it against the
    `{Pi.single i 1, Pi.single i I}` "basis" (via `Finset.univ_sum_single` + `Pi.single_add`/
    `_smul`) produces a nonzero form with vanishing real periods, contradicting nondegeneracy.
  * **Segment.lean** (shared helper, ungated): `RS.segmentPath` (the in-chart straight-line path,
    continuity via `ContinuousOn.comp_continuous` + `Convex.lineMap_mem`) and
    `RS.pathIntegral_segmentPath` (its integral is the primitive's value-difference, via
    `isPrimitiveAlongMap_of_ball` + `IsPrimitiveAlong.pathIntegral_eq`).
  * **Final-assembly discharge shape** (recorded in the root docstring): once a sibling pass proves
    `hproof : RS.DiscretenessHyp X` unconditionally, `instance : DiscreteTopology (RS.periodSubgroup
    X).topologicalClosure := RS.discreteTopology_periodSubgroup_topologicalClosure hproof` and
    `instance : IsZLattice ℝ (RS.periodSubgroup X).topologicalClosure.toIntSubmodule :=
    RS.isZLattice_periodSubgroup_topologicalClosure hproof` are the only two lines final assembly
    needs; `jacobian-construction`'s `Jacobian.instChartedSpace`/`instIsManifold`/`instLieAddGroup`/
    `instCompactSpace` (`docs/Jacobian_challenge.lean:78-89`) then fire by instance search alone.
  Files: `Jacobian/PeriodLattice/{Membership,GenericPoints,Segment,FormIdentity,Nondegeneracy,
  Discreteness,FullRank}.lean` (all new) + `Jacobian/PeriodLattice.lean` (new, unit root/API
  docstring). `Jacobian.lean` (root orchestrator) NOT touched, per task hard rule.

## abel-theorem: the weak-solution-upgrade DISCHARGE (the Serre-functional pass)

**Task**: discharge the two hypotheses isolated by the previous Abel pass —
`RS.Abel.WeakSolutionUpgrade X` / `WeakSolutionUpgradeFinset X ι` (design §4.1 steps 5-7) and
the `DolbeaultBridge` gate `Function.Surjective (RS.LaurentTail.tailToH1 (0 : RS.Divisor X))` —
by building the blueprint's routing-decision-#2 "honest integration atom" (the Dolbeault-side
Serre functional).

**Outcome**: the atom is BUILT and steps 5-7 are FULLY DISCHARGED, collapsing the unit's whole
gate structure to the ONE pre-existing `serre-duality-tails` fact. Six new files, all under
`Jacobian/Abel/`, zero sorries, no new axioms:

* `AreaPairing.lean` — `SurfPoU X` (finite smooth PoU subordinate to preferred-chart sources,
  from `RS.exists_smoothPartitionOfUnity` + compactness); the indicator-extension smoothness /
  compact-support / integrability gadgets; the chart-inverse `ContDiffOn` bridges; the
  spike-recorded holomorphic-Jacobian fact `det_fderiv_eq_normSq_deriv`; the biholomorphic
  `(1,1)`-density change-of-variables atom `integral_eq_integral_transition` (mathlib
  `integral_image_eq_integral_abs_det_fderiv_smul` + `normSq∘deriv`); and the **Serre area
  pairing** `RS.Abel.pairing PU σ θ := ∑ i, ∫ ψᵢ σᵢ θᵢ dA`, integrable and bilinear. The pairing
  is parametrized by a fixed `PU : SurfPoU X` — no independence-of-PoU statement is ever needed,
  since every downstream conclusion is a `Prop` that fixes one `PU` at the start.
* `SerreFunctional.lean` — (a) **`pairing_dbar_eq_zero`** (`∬ ∂̄u ∧ θ = 0`, UNCONDITIONAL): the
  compact-surface Stokes argument run through planar Atom 1 per PoU chart
  (`ψᵢ ∂̄u θᵢ = ∂̄(ψᵢ u θᵢ) − ∂̄ψᵢ·u·θᵢ`), with the leftover sum killed by inserting `∑ⱼ ψⱼ = 1`,
  transporting each `(i,j)` piece to chart `j` by the change-of-variables atom (the
  `conj (deriv τ)·deriv τ = normSq (deriv τ)` cancellation against the `(0,1)` chain rule and
  `coeffIn_trans`), and summing `∑ᵢ ∂̄ψᵢ = ∂̄1 = 0`. (b) `conjForm` (the conjugate `(0,1)`-form,
  whose `Form01.compat` law is the conjugated `coeffIn_trans`) and **`pairingDual_injective`**
  (UNCONDITIONAL, Hodge-free: `∬ θ̄ ∧ θ = ∑ ∫ ψᵢ|θᵢ|² ≥ 0`, zero only for `θ = 0`, via
  `volume`'s open-positivity). (c) `finrank_H01_eq_genus` and the INTEGRAL-pairing bridge
  **`exists_dbar_of_forall_pairing_eq_zero`** (σ ⊥ all of `Form1 X` ⟹ ∂̄-exact), both gated on
  the single `serre-duality-tails` fact: surjectivity forces `finrank (H01 X) = genus X`
  (via `dolbeaultEquiv` + `H1Tail.equiv_of_surjective` + `h1T_zero_eq_genus`), so the positivity
  injection is onto `Dual (H01 X)` by dimension count and
  `Module.forall_dual_apply_eq_zero_iff` closes. Also
  **`tailToH1_zero_surjective_iff_finrank_le`**: the remaining gate is EQUIVALENT to the pure
  dimension statement `finrank ℂ (Cech.H1 0) ≤ genus X` (the `≥` direction being the
  unconditional tail injection).
* `ChartSupported.lean` — `ChartSupportedData.form`: a planar coefficient compactly supported in
  one maximal-atlas chart spreads to a global `Form01 X` (direct construction, `compat` via
  `deriv_trans_comp`); the localization **`pairing_form`**: `pairing PU D.form θ =
  ∫ h · coeffIn e θ dA` (one planar integral in the supporting chart — per-PoU-index
  change of variables, `deriv_trans_mul_deriv_trans_symm` unit cancellation, `∑ψᵢ = 1`).
* `LogPiece.lean` (pure planar) — `LogPieceData`: one `SingleChart.lean`-recipe piece
  (`(z-β)/(z-α)` inside `ball c ρ`, `exp(χ·L)` across the bump annulus, `1` outside, `L` the
  exterior log branch); its `∂̄log` coefficient `dlog = ∂̄(χL)`, globally smooth, supported in
  the closed bump annulus, with `∂̄g = dlog·g` off `{α, β}`; punctured-limit factorizations
  `g·(z-β)⁻¹ → (β-α)⁻¹`, `g·(z-α) → α-β`; and **`integral_dlog_mul`** — Forster 20.3/20.5 in
  planar form, `∫ dlog·θ dA = π (Gp β − Gp α)`: the annulus-Stokes atom reduces the area
  integral to `−∮ L·θ` on the inner circle, integration by parts along the circle
  (`circleIntegral.integral_eq_zero_of_hasDerivWithinAt`) trades `L·θ` for the two-pole kernel
  `((z-β)⁻¹−(z-α)⁻¹)·Gp`, and `DiffContOnCl.circleIntegral_sub_inv_smul` evaluates it.
* `LinkData.lean` — **`exists_link`**: one `ChartChain` link (two points in a common chart
  ball) yields the piece function on `X` plus its packaged `Form01` with five facts:
  real-smoothness off the pole, non-vanishing off the divisor, the `∂̄log`-matching at every
  preferred-chart center, the punctured factor limit `f·(z-z₀)^(−linkOrd) → C ≠ 0` at EVERY
  point (handled uniformly — zero, pole, regular, off-chart, and degenerate `A = B` cases; slope
  limits via `hasDerivAt_iff_tendsto_slope`), and the pairing identity
  `∬ η ∧ θ = π (Gp(eB) − Gp(eA))`. Also the planar **promotion lemma**
  `meromorphicAt_of_tendsto_factor` (punctured holomorphy + factor limit ⟹ `MeromorphicAt` AND
  `meromorphicOrderAt = m`, via the removable-singularity theorem +
  `tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero` — this replaces ALL `Rechart`-style order
  bookkeeping), and the `∂̄` finite product rule.
* `UpgradeDischarge.lean` — **`exists_mero_of_sum_pathIntegral_eq_zero`** (the engine): chains
  via `RS.exists_chartChain`, one `exists_link` per link, `η := ∑ η_l`;
  `pairing PU η θ = π ∑ᵢ ∫_{δᵢ} θ = 0` (the per-link residue identities telescope through
  `pathIntegral_eq_sum_chartChain` USING THE SAME chart primitives, from mathlib's
  `DifferentiableOn.isExactOn_ball`); the bridge gives `u` with `∂̄u = η`;
  `F₀ := exp(−u)·∏ f_l` is `∂̄`-closed off the divisor points
  (`wirtingerDbar_exp_neg_mul_eq_zero` + the product rule + the per-link `∂̄log`-matchings),
  hence holomorphic there (`contMDiffOn_omega_of_isDbarOn_zero`), and the factor limits multiply
  into the promotion lemma at EVERY point, giving meromorphy and
  `ord_z F = ∑_l linkOrd l z` in one stroke; the link orders telescope
  (`Finset.sum_range_sub`) to the endpoint divisor. Consumers:
  **`weakSolutionUpgrade_of_surjective : (surjectivity) → WeakSolutionUpgrade X`** and
  **`weakSolutionUpgradeFinset_of_surjective`** — note the `WeakSolutionUpgrade` shapes'
  weak-solution ARGUMENTS are not needed at all (their conclusions never mention `f`), so the
  discharge builds its own chain pieces along the given zero-period paths.
* `OfCurveInj.lean` (edited) — new `Jacobian.ofCurve_inj_of_surjective'`/`ofCurve_inj_of_surjective`:
  the challenge statement now gated ONLY on `[DiscreteTopology (RS.periodSubgroup X)]`
  (`period-lattice-rank`'s job) and the single `serre-duality-tails` fact.

**What remains (ONE fact, strictly smaller than the previous gate set)**:
`Function.Surjective (RS.LaurentTail.tailToH1 (0 : RS.Divisor X))`, equivalently (proved,
`tailToH1_zero_surjective_iff_finrank_le`) `Module.finrank ℂ (RS.Cech.H1 (0 : RS.Divisor X)) ≤
genus X`. Classically this is the surjectivity half of Serre duality for `𝒪_X`; the recorded
Hodge-free route is Forster §17.9's dimension counting (Čech level: the residue pairing
`H⁰(Ω_{nP}) × H¹(𝒪_{−nP}) → ℂ` via PoU-splitting + the now-built `∬` machinery, the
multiplication epimorphisms `H¹(𝒪_{−nP}) → H¹(𝒪)` through the six-term/skyscraper ledger, and
the count `dim Λ + dim Im(ι) > dim H¹(𝒪_{−nP})*` for `n ≫ 0`) — a further sibling-unit-sized
build on the Čech colimit, not attempted here. NOTE the reduction is strict: previously
`WeakSolutionUpgrade`(+Finset) was an INDEPENDENT second gap; now every `Jacobian/Abel` result
is reduced to this single fact.

**Lean gotchas hit**: `ω`/`𝒫` are not usable as identifiers under `open scoped ContDiff` (hence
"θ not ω" everywhere); raw `P.ρ < ‖z-c‖` props must be coerced to `z ∈ {w | …}` memberships
before `Set.indicator_of_mem` rewrites (the unifier otherwise decomposes the membership as a
`Real.lt`-application and the rewrite pattern misses the `setOf`-indicator); `rcases eq_or_ne x B
with rfl` substitutes `B := x`, so subsequent references must use `x`; `ContDiffOn.smul`/`.mul`
chains need the scalar factor bound by `have` first (metavariable-stuck `IsScalarTower`
otherwise); `ContDiffBump`-field inequalities are best proved by `show`-normalizing the structure
literal's projections (a `rw` into the literal makes the motive ill-typed); and
`Set.piecewise`/`Function.comp` chart-center evaluations close by `simp [Function.comp,
left_inv]`, not `rfl`.

**Verification**: `scripts/check.sh Jacobian/Abel` — Build completed successfully (3276 jobs),
zero sorries. Files touched: `Jacobian/Abel/AreaPairing.lean`, `SerreFunctional.lean`,
`ChartSupported.lean`, `LogPiece.lean`, `LinkData.lean`, `UpgradeDischarge.lean` (all new),
`Jacobian/Abel/Sufficiency.lean` (docstring update), `Jacobian/Abel/OfCurveInj.lean` (new
wrappers), `Jacobian/Abel.lean` (imports + docstring), `docs/build-log.md` (this entry).
`Jacobian.lean` NOT touched.

- [abel] UPGRADE DISCHARGED

## cechcount: the FINAL GATE — `dim H¹(𝒪_X) ≤ genus X`, and every remaining discharge

**New unit `Jacobian/CechCount/`** (root `Jacobian/CechCount.lean` — NOT yet registered in
`Jacobian.lean`, per this pass's edit-surface rule; registration is a one-line
`import Jacobian.CechCount`). Forster §17.8–17.9's dimension count executed directly on the
Čech colimit (Hodge-free, residue-functional-free, duality-free):

* `Mul.lean` — **multiplication on Čech `H¹`**: `RS.Cech.MulBound f D E`
  (`∀ x, D x − E x ≤ ord_x f` in `WithTop ℤ`; holds for `f = 0`), the tower
  `mulOn` (germ level, `LinearMap.mulLeft` + `MeroGermOn.restrict`) → `mulC0`/`mulC1`
  (commuting with `d0`/`d1`/`resC1`) → `mulZ1`/`mulH1Cover` (`Submodule.mapQ`) →
  **`RS.Cech.mulH1 f hf : H1 D →ₗ[ℂ] H1 E`** (`Module.DirectLimit.map`, mirroring `H1Incl`
  verbatim), plus laws `mulH1_add`/`mulH1_smul`/`mulH1_mulH1`/`mulH1_one` (= `H1Incl`)/
  `mulH1_H1Incl`/`mulH1_congr`. All descents are triple `Subtype.ext`+`funext` to the germ
  algebra; `mulH1_H1Incl` closes by `congr 1` alone (inclusion is coe-identity).
* `Surjective.lean` — **Forster 17.8 (primal)**: `mulH1_surjective` for `f ≠ 0`, factoring
  through `D₁ := E + divisor f`: `H1Incl_surjective` (six-term part (g)) ∘ exact-bound
  multiplication (inverse `f⁻¹` via `Mero.mul_inv_cancel` + `divisor_inv` +
  `WithTop.coe_untop₀_of_ne_top`).
* `Count.lean` — the ledger + growth contradiction. Step 1 (constancy): for `n > 2g−2`,
  `l(nP) = n+1−g` (`riemannRoch` + `deg_canonical` + `linSys_eq_bot_of_degree_neg'` +
  `degree_single`), so `chi_eq_chi_zero_add_degree` + `l_zero` give
  `h¹(nP) = h¹(0) − g` — constant. Step 2 (Forster 17.9, primal): if `h¹(0) > g`, set
  `c := h¹(0) − g ≥ 1`, `n₀ := 2g`, `m := g + h¹(0) + 1`; pick `ξ ≠ 0` in `H¹(n₀P)`
  (`Module.nontrivial_of_finrank_pos`); `Φ : L(mP) →ₗ H¹((n₀+m)P)`, `f ↦ (f·)ξ` has
  `dim L(mP) = h¹(0)+2 > c = dim H¹((n₀+m)P)`, hence a nonzero `f := q − r` with
  `(f·)ξ = 0`; but `mulH1_surjective` between equal dimensions `c` forces injectivity
  (rank–nullity: `finrank_range_add_finrank_ker` + `finrank_top` +
  `Submodule.finrank_eq_zero`), so `ξ = 0` — contradiction. **`RS.cechCount :
  Module.finrank ℂ (RS.Cech.H1 (0 : RS.Divisor X)) ≤ genus X`** (alias
  `RS.finrank_H1_zero_le_genus`).
* `Final.lean` — the ungated finals: **`RS.tailToH1_zero_surjective`** (via the built
  `RS.Abel.tailToH1_zero_surjective_iff_finrank_le`), `RS.finrank_H1_zero_eq_genus`
  (`dim H¹(X,𝒪_X) = genus X`, the deferred cech-h1-genus identity),
  **`RS.Abel.weakSolutionUpgrade_final : WeakSolutionUpgrade X`**,
  `RS.Abel.weakSolutionUpgradeFinset_final`, **`RS.discretenessHyp_final :
  RS.DiscretenessHyp X`**, the global instances `DiscreteTopology (RS.periodSubgroup X)`,
  `DiscreteTopology (RS.periodSubgroup X).topologicalClosure`, `IsZLattice ℝ
  (RS.periodSubgroup X).topologicalClosure.toIntSubmodule` (the exact recorded
  `PeriodLattice` discharge shapes — both fire by `inferInstance`, spot-checked),
  `RS.finrank_int_periodSubgroup_final` (`ℤ`-rank `2g`), and
  **`Jacobian.ofCurve_inj_final (P : X) (h : 0 < genus X) :
  Function.Injective (Jacobian.ofCurve P)`** — the challenge's `ofCurve_inj`,
  hypothesis-free.

**Lean gotchas hit**: `rw [mem_linSysOn_iff_of_isOpen U.2]` fails on the `U.carrier`-vs-`↑U`
pattern mismatch — pass `U.isOpen` instead; `omega` cannot bridge `locallyFinsuppWithin.le_def`'s
coe atoms against pointwise hypotheses (close with `sub_nonpos.mp`/`sub_le_iff_le_add'` term
lemmas); every `H1`-level declaration needs `set_option maxHeartbeats 1000000` (DirectLimit
`isDefEq` unfolding, as in `Colimit.lean`); a `set_option … in` must precede the docstring, not
sit between it and the declaration; `tailToH1` needs `[DecidableEq X]` even to *state* — the
`Final.lean` consumers take it via a single `classical` per proof (one consistent local
instance).

**Verification**: `scripts/check.sh Jacobian/CechCount` — Build completed successfully
(3292 jobs), zero sorries. `#print axioms` on all seven finals: `[propext, Classical.choice,
Quot.sound]` only. Files: `Jacobian/CechCount/{Mul,Surjective,Count,Final}.lean`,
`Jacobian/CechCount.lean` (all new), `docs/build-log.md` (this entry). `Jacobian.lean` NOT
touched (registration pending, one line).

- [cechcount] FINAL GATE CLOSED

## final-assembly: `Jacobian/Challenge.lean` — the challenge API, complete

- [final] `Jacobian/Challenge.lean` NEW (built on top of the registered `Jacobian` root import).
  Contains ONLY the gist names that did not yet exist: the root-level functorial API
  `Jacobian.pushforward`, `Jacobian.pushforward_contMDiff`, `Jacobian.pushforward_id_apply`,
  `Jacobian.pushforward_comp_apply`, `Jacobian.pullback`, `Jacobian.pullback_contMDiff`,
  `Jacobian.pullback_id_apply`, `Jacobian.pullback_comp_apply`, `Jacobian.pushforward_pullback`
  — one-line wrappers of the built `RS.Jacobian.*` (JacFunctorial). The contMDiff wrappers are
  stated UNGATED: the discreteness gates are global instances since `Jacobian/CechCount/Final.lean`.
  Everything else already lives at its gist name: `genus` (Forms/Genus), `genus_eq_zero_iff_homeo`
  (GenusSphereHeadline), `Jacobian` + the 7 instances (JacobianConstruction/Basic, gates global),
  `Jacobian.ofCurve`/`ofCurve_self`/`ofCurve_contMDiff` (JacobianConstruction/OfCurve),
  `ContMDiff.degree` (ProperDegree/ChallengeDegree). A final self-auditing `GistCheck` section
  witnesses all 24 gist items as `example`s in the gist's own shapes.
- [final] **Universe deviation (the only one, sanctioned by the JacFunctorial LEDGER)**: the
  functorial declarations state `{X Y Z : Type u}` in ONE shared universe instead of the gist's
  independent `Type*`s. Re-verified during assembly: the gist-verbatim distinct-universe wrapper
  does not fail cleanly but dies in the documented `ULift`/quotient defeq grind
  (`(deterministic) timeout at whnf`, 54s to heartbeat limit).
- [final] **Name deviation**: the gist-signature `ofCurve_inj` is `Jacobian.ofCurve_inj_final`
  (CechCount/Final) — the literal name `Jacobian.ofCurve_inj` was claimed by abel-theorem's gated
  variant (extra explicit `RS.Abel.WeakSolutionUpgrade X` argument) and cannot be redeclared.
  `Jacobian.ofCurve_contMDiff` carries one extra instance-implicit `[DiscreteTopology …]`
  argument, globally discharged — gist-shaped uses elaborate verbatim.
- [final] **Acceptance test** `scratch_gist_check.lean` (project root): `import Jacobian` +
  `import Jacobian.Challenge`, all 24 gist items stated verbatim as `example`s and proved by the
  providing names — `lake env lean scratch_gist_check.lean` clean (7.6s). `#print axioms` on
  `genus`, `Jacobian`, `Jacobian.ofCurve_inj_final`, `genus_eq_zero_iff_homeo`,
  `Jacobian.pushforward_pullback`, `ContMDiff.degree`: all
  `[propext, Classical.choice, Quot.sound]` only.
- [final] `scripts/check.sh Jacobian/Challenge` — Build completed successfully (3319 jobs), zero
  sorries. `Jacobian.lean` NOT touched (orchestrator to register `import Jacobian.Challenge`).

## forward-port: v4.30.0-rc2/mathlib 5483982 → v4.32.0-rc1/mathlib 360da6fa (979 commits)

Pure drift-fixing pass, no statement changes. Root failures were 16 errors in 6 files; fixing
them cascaded through the rest of the (46k-line) build in five more rounds as downstream files
hit the same handful of mathlib-API-shape changes. Three recurring root causes account for
almost everything:

1. **The new `to_fun` attribute** (`Mathlib.Tactic.ToFun`, since ~2026-05): point-free combinator
   lemmas (`HasDerivAt.sub`, `AnalyticAt.zpow`, `MeromorphicAt.zpow`, `AnalyticAt.comp'`,
   `HasFDerivAt.comp_hasDerivAt_of_eq`, …) now literally produce `f - g` / `f ^ n` /
   `g ∘ f` (`Pi`/`Function.comp` point-free form) instead of the eta-expanded `fun x => f x - g x`
   form our proofs were written against — and critically, `simp`/`simpa` no longer bridges the
   two forms the way it used to (see point 3). Fix: use the `to_fun`-generated eta-expanded
   sibling where one exists (`HasDerivAt.fun_sub`, `AnalyticAt.fun_zpow`,
   `MeromorphicAt.fun_zpow`, `AnalyticAt.fun_comp`, `AnalyticAt.fun_comp_of_eq`,
   `MeromorphicAt.fun_mul`, `HasDerivAt.fun_div`) — mathlib's own migration path for exactly this
   shape mismatch.
2. **Renamed/dropped lemmas** (plain `@[deprecated]` aliases, one-line fixes): `Pi.zero_def`/
   `Pi.one_def` needed explicitly in a couple of `simpa` calls that used to close automatically;
   `ContinuousLinearMap.{add,sub,neg,smul}_apply` → unqualified `{add,sub,neg,smul}_apply`;
   `ContinuousLinearMap.ring_lmap_equiv_self` → `(ContinuousLinearMap.toSpanSingletonLIE _ _).symm`
   (direction flipped in the rename); `ofReal_norm_eq_enorm` → `ofReal_norm`; `Set.mem_diff` →
   `Set.mem_sdiff`; `Set.diff_eq_empty`/`Set.sdiff_eq_empty`, `Icc_diff_{Ioo,Ico}_same` →
   `Icc_sdiff_{Ioo,Ico}_same`; `Set.diff_subset` → `Set.sdiff_subset`; `DFunLike`'s field
   `coe_injective'` → `coe_injective` (and its type is now stated as `Function.Injective coe`).
3. **`simpa`/`simp only []` no longer closes goals it used to.** Two recurring shapes: (a) a bare
   `simp only []` or `dsimp only` that used to do *some* normalization now does none (the
   preceding `simp`/rewriting already leaves the goal in simp-normal form) — deleting the
   vacuous call is the fix; (b) `simpa [foo] using bar` where `bar`'s type and the goal are
   **definitionally equal** (mostly `rfl`-true unfoldings of a `def`/`LinearMap`/`Submodule`
   wrapper, or associativity of `Function.comp`) but not *simp*-equal — `simpa`'s closing step
   apparently now checks equality at a stricter transparency than plain `exact`/`rw` does, so it
   fails where it used to succeed. Fix: replace `simpa … using bar` with a plain `exact bar` (or
   `rw [foo]; exact bar`/`simp only [...] at bar; exact bar` when a genuine, non-defeq rewrite is
   still needed first).

A fourth, unrelated issue surfaced in `Jacobian/Cech/Cochains.lean` and `Jacobian/Cech/
WindowRank.lean`: `synthInstance` on this toolchain no longer reliably re-derives a **dependent**
Pi-instance goal (`∀ i, AddCommGroup ↥(Submodule …)`, arising from `Module`/`AddCommGroup` on a
`∀ i, LinSysOn …`-shaped cochain/window type) on demand at every downstream `Submodule.addCommGroup`/
`Submodule.instModule`/`HasQuotient` use site — even though the *non-dependent* instance for a
single fixed factor resolves fine. Fix: register the resolved instance once, directly, as a named
global `instance` (bypassing the fragile re-derivation), rather than changing any type. Separately,
two declarations (`finiteDimensional_windowAt`, `finiteDimensional_window`) were `instance`s
whose one non-instance-implicit hypothesis (`h : d ≤ d'` / `h : D ≤ D'`) Lean now (correctly)
refuses to accept as an `instance` at all (`"has 1 argument that cannot be inferred using
typeclass synthesis"` is now a hard error, not a lint warning) — both were already invoked only by
explicit application at every call site, so `instance` → `theorem` is a no-op change in behavior.

Files touched (30), each a one-liner-to-small tactic/API fix, statements unchanged:

- [fport] `Jacobian/ResidueCalculus/PrincipalPart.lean`: deleted 3 now-vacuous `simp only []`
  calls in the Laurent-coefficient `Finset.sum_nbij'` proof (`simp made no progress`; the
  preceding `simp only [Finset.mem_range/Icc]` already leaves the goal in normal form).
- [fport] `Jacobian/Meromorphic/Predicates.lean`: `ordAtX_zero`/`ordAtX_one` — added
  `Pi.zero_def`/`Pi.one_def` to the `simpa` set so `(0 : X → ℂ)`/`(1 : X → ℂ)` match
  `ordAtX_const`'s `fun _ => c` shape (mathlib change: these no longer fire without the
  lemma named explicitly).
- [fport] `Jacobian/Path/Planar.lean`: `HasDerivAt.sub` → `HasDerivAt.fun_sub` (×2, in
  `eventuallyEq_of_hasDerivAt_eq`); `convert hy.units_smul ![-1, 1]` now leaves two
  instance-diamond side goals (`CommRing.toCommSemiring.toSemiring = Real.semiring`,
  `addCommGroup.toAddCommMonoid = instAddCommMonoid`) — closed with
  `<;> [skip; rfl; rfl]` (both are `rfl`-true, `convert`'s own closing pass no longer does it).
- [fport] `Jacobian/Dbar/Wirtinger.lean`: `simpa [wirtingerDbar] using this` (×2, in
  `contDiffOn_wirtingerDbar`/`continuous_wirtingerDbar`) → `exact this` (the def-unfold
  is `rfl`-true, `simpa`'s closing check no longer sees it through the partial
  application); dropped 4 now-unused-and-deprecated `ContinuousLinearMap.{add,sub,neg,smul}_apply`
  simp args (mathlib change: → unqualified `{add,sub,neg,smul}_apply`).
- [fport] `Jacobian/AbelWeak/SingleChart.lean`: `simpa [Function.comp] using hcomp` → `exact
  hcomp` (same defeq-not-simp-eq pattern, for a `ContDiffAt … (↑ψ ∘ fun w ↦ w - c)` vs
  `fun w ↦ ↑ψ (w - c)` goal).
- [fport] `Jacobian/Forms/Analyticity.lean`: `ContinuousLinearMap.ring_lmap_equiv_self ℂ ℂ` →
  `(ContinuousLinearMap.toSpanSingletonLIE ℂ ℂ).symm` (mathlib change: the old name is now a
  deprecated alias for `toSpanSingletonLIE` itself, i.e. the *forward* direction — our use needed
  the reverse, exactly as the deprecation message says); `AnalyticAt.comp'` →
  `AnalyticAt.fun_comp` (×3, mathlib change: `AnalyticAt.comp'` deprecated in favor of the
  `to_fun`-generated `fun_comp`).
- [fport] `Jacobian/Meromorphic/OrderEval.lean`: `evalAt_smul` — `simpa [smul_eq_mul] using
  (e1.const_smul c)` → `simp only [smul_eq_mul] at h2; exact h2` (goal needs the literal
  Pi-form `c • f`, matching a sibling `tendsto_evalAt` call; `Filter.Tendsto.const_smul` has no
  `to_fun` sibling to reach for, so bridge in two steps instead of one `simpa`).
- [fport] `Jacobian/MeromorphicTrace/PlanarTrace.lean`: `.zpow` → `.fun_zpow` (×3, `AnalyticAt`
  once, `MeromorphicAt` twice); `.comp'` → `.fun_comp` (×1).
- [fport] `Jacobian/PlanarStokes/Compat.lean`: dropped 2 now-unused deprecated
  `ContinuousLinearMap.{add,smul}_apply` simp args; `simpa [wirtingerDbar] using …` (×1) → `exact
  …` (same `Dbar/Wirtinger.lean` pattern, this unit's own copy per its docstring).
- [fport] `Jacobian/Dbar/Form01.lean`: deleted 4 now-vacuous `dsimp only;` calls in the
  `Add`/`Neg`/`Sub`/`SMul (Form01 X)` instance proofs (`dsimp` made no progress).
- [fport] `Jacobian/Dbar/CauchyKernel.lean`: `simpa [hh_def, wirtingerDbar] using …` →
  `rw [hh_def]; exact …`; two `simpa [Gr/Gθ, map_neg] using (HasFDerivAt.comp_hasDerivAt_of_eq …)`
  → `simp only [map_neg] at h4; exact h4` (`.comp_hasDerivAt_of_eq` has no `to_fun` sibling, no
  `Function.comp`-eta needed once `map_neg` alone is applied as a plain rewrite first);
  `ofReal_norm_eq_enorm` → `ofReal_norm`.
- [fport] `Jacobian/JacFunctorial/Pullback.lean`: `mfderiv_chartAt_self` — `simpa [extChartAt_coe]
  using h` no longer collapses `↑𝓘(ℂ,ℂ) ∘ ↑(chartAt ℂ y)` down to `↑(chartAt ℂ y)` alone; added
  `modelWithCornersSelf_coe, Function.id_comp` to the simp set and switched the close to
  `simp only […] at h; exact h` (the residual `TangentSpace 𝓘(ℂ,ℂ) y` vs `ℂ` gap is defeq-only,
  not simp-eq); `AnalyticAt.comp'` → `AnalyticAt.fun_comp`.
- [fport] `Jacobian/CanonicalForms/MForm.lean`: deleted 4 now-vacuous `dsimp only;` calls (same
  `Add`/`Neg`/`Sub`/`SMul (MFormData X)` pattern as `Dbar/Form01.lean`).
- [fport] `Jacobian/Dbar/Operator.lean`: `SmoothC.instFunLike`'s `coe_injective'` field →
  `coe_injective` (mathlib change: `DFunLike`'s field renamed, dropped the trailing prime, and
  is now typed as `Function.Injective coe` rather than the unfolded `∀ a b, …` form).
- [fport] `Jacobian/MeromorphicTrace/ToP1.lean`: `simpa using (hd.sub hconst)` → `simp only
  [sub_self] at hsub; exact hsub` (`Filter.Tendsto.sub` has no `to_fun` sibling).
- [fport] `Jacobian/FormTrace/TraceZkForm.lean`: `.zpow` → `.fun_zpow` (×2).
- [fport] `Jacobian/PlanarStokes/AnnulusResidue.lean`: `MeasureTheory.ae_iff.mpr (by simpa using
  hRecOpen_null_diff)` → `rw [MeasureTheory.ae_iff]; simp only [not_not]; exact
  hRecOpen_null_diff` (the goal has a genuine `¬¬P` needing `not_not`, not just a defeq gap, so
  `exact` alone doesn't suffice this time); renamed 4 deprecated lemmas project-wide within the
  file: `Icc_diff_Ioo_same`/`Icc_diff_Ico_same` → `Icc_sdiff_{Ioo,Ico}_same`, `Set.mem_diff` (×2)
  → `Set.mem_sdiff`, `Set.diff_eq_empty` → `Set.sdiff_eq_empty`.
- [fport] `Jacobian/Cech/Cochains.lean`: added `instAddCommGroupZ1`/`instModuleZ1` — direct
  `AddCommGroup (Z1 D 𝒰)`/`Module ℂ (Z1 D 𝒰)` instances via `(Z1 D 𝒰).addCommGroup`/`.module`,
  registered once so `H1Cover`'s `Z1 D 𝒰 ⧸ _` and every downstream user finds them verbatim
  instead of re-deriving `AddCommGroup (C1 D 𝒰)` through the (now-fragile) dependent Pi-instance
  path per use (see the round summary above; was surfacing as `failed to synthesize
  HasQuotient …` plus knock-on `Function expected at H1Cover` parse-level errors from the first
  failure poisoning the rest of the file's elaboration).
- [fport] `Jacobian/JacFunctorial/TraceCoeff.lean`: `.zpow` → `.fun_zpow`.
- [fport] `Jacobian/FormTrace/ResidueTraceCompat.lean`: `.comp_of_eq` → `.fun_comp_of_eq`;
  `.zpow` → `.fun_zpow`; `.mul` → `.fun_mul` (×2, both operands of a nested product); dropped 2
  now-unused `deriv_sub_const` simp args.
- [fport] `Jacobian/DolbeaultComparison/Splitting.lean`: `simpa using hcast` → `exact hcast`
  (`congrArg Subtype.val` of a `Z1`-membership equation vs. the `restrictL_apply_coe`-unfolded
  goal — `rfl`-true, not simp-eq).
- [fport] `Jacobian/Dbar/DiskAcyclic.lean`: deleted a vacuous `dsimp only at heval`; two more
  `simpa using hcast` → `exact hcast` (same `LinSysOn.restrictL`/`MeroGermOn.restrict`
  defeq-bridge pattern as `Splitting.lean`).
- [fport] `Jacobian/AbelWeak/ChainAssembly.lean`: `HasDerivAt.div` → `HasDerivAt.fun_div`.
- [fport] `Jacobian/Cech/WindowRank.lean`: added `instAddCommGroupWindowAt`/
  `instModuleWindowAt`/`instModuleFreeWindowAt` — direct instances for the generic
  `WindowAt p d d'` (same dependent-Pi-instance fix as `Cech/Cochains.lean`, one level up:
  `Window D D' := ∀ q, WindowAt (q:X) (D q) (D' q)`); `finiteDimensional_windowAt`/
  `finiteDimensional_window`: `instance` → `theorem` (both take a non-instance-implicit `≤`
  hypothesis Lean can no longer accept on an `instance` at all — `"This instance has 1 argument
  that cannot be inferred using typeclass synthesis"` is now a hard error; every call site
  already invoked them explicitly, so this is a pure declaration-kind change, zero behavior
  change).
- [fport] `Jacobian/DolbeaultComparison/Leray.lean`: `simpa using hcast` → `exact hcast` (same
  `LinSysOn.restrictL`/`MeroGermOn.restrict` pattern).
- [fport] `Jacobian/Finiteness/TradeBounded.lean`: `simpa using hcast` → `exact hcast` (same
  pattern); deleted a vacuous `simp only at hcongr`.
- [fport] `Jacobian/DolbeaultComparison/Comparison.lean`: `simpa using this` → `exact this`
  (`resH1_comp`'s conclusion `(ρ ∘ τ𝒱) ∘ σV` vs. the goal's `ρ ∘ τ𝒱 ∘ σV` — associativity of
  `Function.comp` is `rfl`-true via its `fun x => f (g x)` definition, not simp-eq).
- [fport] `Jacobian/Abel/SerreFunctional.lean`: `simpa using (RS.wirtingerDbar_const z 0)` →
  added `Pi.zero_def` to the simp set (same `Predicates.lean` pattern); `pairingDual_injective`'s
  `simpa using happ` → added `pairingDual, pairingH01_mk` to the simp set (needed the `def`'s own
  unfolding lemma spelled out, plus the already-`@[simp]` `pairingH01_mk`, together in one call).
- [fport] `Jacobian/Abel/Sufficiency.lean`: two `simpa using …` closing a `Basis.ext`/`LinearMap`
  sum-of-`pathIntegralₗ` argument → `simp only [LinearMap.sum_apply] at …; exact …` (distribute
  the finite sum of linear maps first, then the leftover `pathIntegralₗ γ θ = pathIntegral γ θ`
  gap is `rfl`-true).
- [fport] `Jacobian/Abel/UpgradeDischarge.lean`: `simpa using ((chartAt ℂ x).symm.
  isOpen_inter_preimage h1)` → `rw [hV_def]; exact …` (`simp` was distributing the preimage over
  `\`/`ᶜ` on the hypothesis side only, breaking the match against the untouched `let`-bound goal
  `V`; unfolding `V` via its own `set … with hV_def` equation first and skipping simp entirely
  avoids the mismatch since both sides are then syntactically identical); `Set.diff_subset` →
  `Set.sdiff_subset`.

**Verification**: `lake build` — Build completed successfully (3366 jobs), all six rounds of
cascades resolved, zero remaining errors. `lake env lean GistAcceptance.lean` — clean (7.2s).
`grep -rn -w sorry Jacobian/` — empty. Axiom audit (`GistAcceptance.lean`'s own `#print axioms`
lines on `genus`, `Jacobian`, `Jacobian.ofCurve_inj`, `genus_eq_zero_iff_homeo`,
`Jacobian.pushforward_pullback`, `ContMDiff.degree`) — all six report exactly
`[propext, Classical.choice, Quot.sound]`. No statement-level issues: every fix above is a
tactic/name/instance-registration change: no theorem signature, definition type, or the
`Jacobian.lean`/`GistAcceptance.lean`/`comparator/`/`verify.sh`/`lakefile.toml`/
`lake-manifest.json`/`lean-toolchain` files were touched.
