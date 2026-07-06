# Requests: meromorphic-and-divisors

## From cech-cohomology (designer, see docs/design/cech-cohomology.md §8)

All three are small; if inconvenient to absorb, cech-cohomology will prove them locally in a
marked `Compat` section — nothing blocks either unit.

1. `linSysOn_mono (h : D ≤ D') : LinSysOn D U ≤ LinSysOn D' U`
   (carrier implication: `-(D' x) ≤ -(D x) ≤ ord`; one line next to `linSys_mono`).

2. `MeroGermOn.evalAt_eq_zero_iff (hU : IsOpen U) (hx : x ∈ U) (h : 0 ≤ φ.ord x) :
       φ.evalAt x = 0 ↔ 0 < φ.ord x`
   (from `tendsto_evalAt` + planar `tendsto_zero_iff_meromorphicOrderAt_pos` transported
   through the chart + `Filter.Tendsto.limUnder_eq` uniqueness — all atoms already in your
   verified list; natural home is `OrderEval.lean` next to `evalAt`).

3. Nice-to-have: `MeroGermOn.congrSet (h : U = V) : MeroGermOn X U ≃ₗ[ℂ] MeroGermOn X V`
   (restrict along `h.le`/`h.ge`, inverse by `restrict_restrict` + `restrict_id`), with
   `ord_congrSet`/`evalAt_congrSet` rigidity. Used to transport gluing targets
   `⋃ i, ↑(U i)` vs `↑Ω`. If skipped, cech builds it in Compat.
