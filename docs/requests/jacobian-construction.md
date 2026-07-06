# Requests to unit: jacobian-construction

## From jacobian-functoriality (2026-07-06)

The `jacobian-functoriality` design doc (`docs/design/jacobian-functoriality.md` §9.2, §14)
records that a request for the following two lemmas was "filed" here — that record was stale;
this file did not exist on disk before this entry, and `Jacobian/JacobianConstruction/Torus.lean`
does not currently define `Torus.inducedHom_id`/`Torus.inducedHom_comp` (confirmed by direct
inspection: everything in that file lives in `namespace RS`, not `namespace Torus`, and no
`inducedHom_id`/`inducedHom_comp`-named declaration exists there).

**Needed** (composition functoriality of the abstract `V ⧸ L →ₜ+ V' ⧸ L'` substrate
`RS.inducedHom`, `Torus.lean:409-410`), for `Jacobian.pushforward_id_apply`/
`Jacobian.pushforward_comp_apply` and the pullback-direction analogues:

```lean
theorem RS.inducedHom_id (L : AddSubgroup V) [...] :
    RS.inducedHom L L LinearMap.id (hT : L ≤ L.comap (LinearMap.id).toAddMonoidHom) =
      ContinuousAddMonoidHom.id _

theorem RS.inducedHom_comp (L L' L'' : AddSubgroup _) (T : V →ₗ[ℂ] V') (T' : V' →ₗ[ℂ] V'')
    (hT : L ≤ L'.comap T.toAddMonoidHom) (hT' : L' ≤ L''.comap T'.toAddMonoidHom)
    (hTT' : L ≤ L''.comap (T'.comp T).toAddMonoidHom) :
    (RS.inducedHom L' L'' T' hT').comp (RS.inducedHom L L' T hT) =
      RS.inducedHom L L'' (T'.comp T) hTT'
```

Both should be one-line consequences of `RS.inducedHom`'s own definition as
`{ QuotientAddGroup.map L L' T.toAddMonoidHom hT with continuous_toFun := ... }`
(`Torus.lean:411`) plus `QuotientAddGroup.map_id`/`QuotientAddGroup.map_comp_map`-style
group-quotient functoriality (standard mathlib API) — checked via `RS.inducedHom_apply_mk`
(`Torus.lean:421`, already exported) at the representative level, then
`AddMonoidHom.ext`/continuity-is-a-`Prop` to finish. Estimated ~20-30 lines, mechanical, low
risk (this matches the design doc's own R4 assessment).

**Status**: non-blocking for what `jacobian-functoriality` actually delivered — this builder did
not attempt a local `Compat` copy in the time available (the design's own local-fallback route),
so `Jacobian.pushforward_id_apply`/`Jacobian.pushforward_comp_apply` and the pullback-direction
analogues are simply **not built** by `jacobian-functoriality` (see its root file's LEDGER).
Whoever picks up `Torus.inducedHom_id`/`_comp` (here or as a local `Compat` proof in a future
pass over `jacobian-functoriality`) unblocks exactly those four lemmas.
