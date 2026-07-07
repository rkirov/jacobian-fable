import Jacobian.Challenge

/-!
# Submission helpers

The submission delegates every hole to the path-required `jacobian` library. `Jacobian.Challenge`
is the library's assembled challenge API: it pulls in `genus`/`genus_eq_zero_iff_homeo`
(`Jacobian.Forms`/`Jacobian.GenusSphereHeadline`), the `Jacobian` type with all its instances
(`Jacobian.JacobianConstruction`), the Abel–Jacobi map and its injectivity
(`Jacobian.JacobianConstruction.OfCurve`, `Jacobian.CechCount.Final` — which also registers the
global `DiscreteTopology`/`IsZLattice` period-lattice instances), `ContMDiff.degree`
(`Jacobian.ProperDegree`), and the functorial API including the cross-universe layer
(`Jacobian.JacFunctorial.CrossUniverse`: `RS.Jacobian.pushforwardCU`/`pullbackCU` and their laws
at independent universes `u v w`, as the submission template requires).
-/
