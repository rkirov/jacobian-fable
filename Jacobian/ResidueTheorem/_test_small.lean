import Jacobian.CanonicalForms
import Jacobian.ProjectiveLine.Charts

open scoped ContDiff Manifold OnePoint
open Set Filter Topology OnePoint

noncomputable section
namespace RS.P1

example (R : ℂ → ℂ) (q : ℂ)
    (hz : (coeChart (q:OnePoint ℂ) : ℂ) ∈ ⇑(chartAt ℂ ((q:ℂ):OnePoint ℂ)) '' ((chartAt ℂ (∞:OnePoint ℂ)).source ∩ (chartAt ℂ ((q:ℂ):OnePoint ℂ)).source)) :
    True := by
  trivial

end RS.P1
