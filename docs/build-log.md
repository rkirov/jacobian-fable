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
