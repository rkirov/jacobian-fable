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
