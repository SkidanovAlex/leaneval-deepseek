import Mathlib
import Submission.Work.MotR.Transcendental.exists_transcendental_of_pos_topologicalKrullDim
import Submission.Work.MotT.infinite_of_transcendental

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotWire

/-- A positive-dimensional variety over a field has infinite function field: by
`exists_transcendental_of_pos_topologicalKrullDim` there is an element of `X.functionField`
transcendental over `𝔽`, and a field with a transcendental element is infinite. -/
theorem infinite_functionField (𝔽 : Type) [Field 𝔽] (X : AlgebraicGeometry.Scheme)
    [MotivicInvariants.Variety 𝔽 X] (hX : 0 < topologicalKrullDim X) : Infinite ↥X.functionField := by
  letI := Work.FFResidual.overFunctionFieldAlgebra 𝔽 X
  exact Work.MotT.infinite_of_transcendental
    (Work.MotR.Transcendental.exists_transcendental_of_pos_topologicalKrullDim 𝔽 X hX)

end Work.MotWire
