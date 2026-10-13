import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

/-- Multiplying a function that is locally integrable on the open half-line `(0,∞)` by the
continuous function `z ↦ z` preserves local integrability there.  This is the instance
`g = id` of `MeasureTheory.LocallyIntegrableOn.continuousOn_mul`, applicable because `Set.Ioi 0`
is open, hence locally closed. -/
theorem locallyIntegrableOn_mul_id {W : ℝ → ℝ}
    (hW : MeasureTheory.LocallyIntegrableOn W (Set.Ioi 0)) :
    MeasureTheory.LocallyIntegrableOn (fun z => z * W z) (Set.Ioi 0) := by
  exact hW.continuousOn_mul continuousOn_id isOpen_Ioi.isLocallyClosed

end Work.FTS.StrongEps.EComparison
