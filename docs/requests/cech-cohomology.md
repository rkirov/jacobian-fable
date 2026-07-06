# Requests: cech-cohomology

## From laurent-tails (continuation builder, see `docs/design/laurent-tails.md`, `Comparison.lean`)

1. **Register `AddCommGroup (H1 D)` (and, if it turns out to be needed too, `Module ℂ (H1 D)`) as
   a genuine global instance in `Jacobian/Cech/Colimit.lean` itself**, right next to `H1`'s own
   definition. Concretely:
   ```lean
   noncomputable instance instAddCommGroupH1 (D : RS.Divisor X) : AddCommGroup (H1 D) :=
     Module.DirectLimit.addCommGroup (fun 𝒰 : FinCover (⊤ : Opens X) => H1Cover D 𝒰)
       (fun _ _ h => resH1' D h)
   ```
   **Why this is needed, not merely nice-to-have**: plain `inferInstance`/typeclass search for
   `AddCommGroup (H1 D)` **fails** through the `H1` `abbrev`, even with every other relevant
   instance (`DecidableEq`/`Preorder`/`IsDirectedOrder (FinCover ⊤)`) in scope — confirmed by an
   isolated failing example (`example (D) : AddCommGroup (Cech.H1 D) := inferInstance`, in a fresh
   file importing only `Jacobian.Cech.Colimit`). Root cause: `Module.DirectLimit.addCommGroup`
   (`Mathlib.Algebra.Colimit.Module`) re-declares its index family `G` and connecting maps `f` as
   **explicit** arguments (shadowing the section variables under which `addCommMonoid`/`module`
   are declared as plain instances a few lines above), which appears to defeat automatic instance
   discovery through the `abbrev` even though the *explicit* application
   `Module.DirectLimit.addCommGroup (fun 𝒰 => H1Cover D 𝒰) (fun _ _ h => resH1' D h)` type-checks
   instantly. This is presumably why the *existing* `Colimit.lean`/`Skyscraper.lean`/`SixTerm.lean`
   code never hits the issue: every `+`/`0`/`Submodule` use of `H1 D` in those files goes through
   an *already-elaborated*, opaque combinator (`toH1`, `mlClass`, `H1Incl`, …) whose own type was
   fixed once and for all when *that* declaration was checked, never re-deriving the instance from
   a bare `AddCommGroup (H1 D)` search the way a *new* `Submodule.liftQ`/anonymous-constructor
   `LinearMap` targeting `H1 D` does.
2. **Symptom for future consumers, so no one repeats the diagnosis**: any new file building a
   `LinearMap … →ₗ[ℂ] H1 D` from scratch (not by composing already-built `Cech` combinators) will
   hit this. `laurent-tails` worked around it locally (`Comparison.lean`'s own
   `instAddCommGroupH1`, marked as load-bearing in that file's docstring) — this request is to
   upstream the same one-line fix so `serre-duality-tails`/`riemann-roch`/any other future
   consumer building a fresh `LinearMap` into `H1 D` doesn't need to rediscover it. Two failed
   attempts recorded for the archive: a `haveI`-scoped local instance (instead of a global
   `instance`) caused a multi-minute `whnf` heartbeat timeout rather than a clean error when
   combined with `Submodule.liftQ`; the global `instance` route is the one that actually resolves
   cleanly and quickly.

Non-blocking either way: `laurent-tails`' own `Comparison.lean` already carries the local fix, so
nothing of ours depends on this landing upstream — filed purely so the fix is shared rather than
re-derived by each future consumer.
