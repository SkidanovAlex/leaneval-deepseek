import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

/-- The tail integral `z ↦ ∫ s in Ioi z, g s` of a function integrable on `Ioi 0` is
continuous on `Ici 0`.  This is the instance `a₀ = 0` of
`MeasureTheory.IntegrableOn.continuousOn_Ici_primitive_Ioi`. -/
theorem continuousOn_integral_Ioi {g : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn g (Set.Ioi 0)) :
    ContinuousOn (fun z => ∫ s in Set.Ioi z, g s) (Set.Ici 0) :=
  hint.continuousOn_Ici_primitive_Ioi

end Work.FTS.StrongEps
