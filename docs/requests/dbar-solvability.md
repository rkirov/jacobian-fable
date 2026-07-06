# Requests to dbar-solvability

From **dolbeault-comparison** (design doc §6, §8; each provable in our Compat section if not
absorbed — none blocking):

1. Please keep the DiskAcyclic germ/function bridge helpers PUBLIC (your design §4.8 already
   lists them as exports — this is just a "don't make them `private`" note):
   `meromorphicOnX_of_contMDiffOn_omega`, `mk_mem_linSysOn_zero`. We use both in the
   comparison's injectivity/surjectivity steps (design §6.4).
2. Nice-to-have additivity/monotonicity for the ∂̄-predicate (3-liners from `wirtingerDbar_add`
   + your `coeffAt_add`; we otherwise prove them in `GlueForm01.lean` Compat):
   - `IsDbarOn.add : IsDbarOn u ω s → IsDbarOn v η s → IsDbarOn (u + v) (ω + η) s`
   - `IsDbarOn.mono : IsDbarOn u ω s → t ⊆ s → IsDbarOn u ω t`
   - `IsDbarOn.smul (c : ℂ)` companion.
3. Nice-to-have (candidate upstream of our Compat lemma, design §4.2): center-determinacy
   `Form01.ext_center : (∀ x, ω.coeffAt x (chartAt ℂ x x) = η.coeffAt x (chartAt ℂ x x)) →
   ω = η` — derivable from your `compat` + `ext` fields; natural home is `Form01.lean`.

From **planar-stokes-atoms** (design doc `docs/design/planar-stokes.md` §5.1, §12 R1; not
blocking — proved locally in our `Compat.lean` meanwhile, spike-verified):

4. Missing from `Wirtinger.lean`: the **Leibniz rule** for `wirtingerDbar`,
   `wirtingerDbar_mul (hg : DifferentiableAt ℝ g z) (hf : DifferentiableAt ℝ f z) :
   wirtingerDbar (fun w => g w * f w) z = wirtingerDbar g z * f z + g z * wirtingerDbar f z`
   (one-liner from `fderiv_fun_mul` + the same `ContinuousLinearMap.add_apply`/`ring` pattern
   already used for `wirtingerDbar_add`/`wirtingerDbar_const_mul`). We use it repeatedly (product
   with a holomorphic factor, composition with `Complex.exp`); natural home is `Wirtinger.lean`
   right after `wirtingerDbar_const_mul`.
5. Nice-to-have: a `C¹`-only (not `ContDiff ℝ ∞`) form of `continuous_wirtingerDbar` — your
   exported version needs `ContDiff ℝ ∞ f`, but the underlying proof only needs one derivative
   (`hf.continuous_fderiv (le_refl 1)`); we hit this because our atoms (matching your own
   `cauchyPompeiu`'s `ContDiff ℝ 1` hypothesis) never assume more than `C¹`.
