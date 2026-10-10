import Mathlib
import Submission.Work.Twist.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

open CategoryTheory AlgebraicGeometry
open Work.Twist

/-- **The projective model layer is exactly what separates Mathlib from a curve** (a roadmap
statement).  If the three missing facts about `ℙ¹` are supplied — `Smooth`, `GeometricallyIntegral`
and `topologicalKrullDim = 1`, i.e. `ProjectiveModelGap 𝕜 1` of
`Submission/Work/PointlessIndexFive/Model.lean` — then `ℙ¹_𝕜` is a `CurveModel 𝕜`: the first
smooth proper geometrically integral curve over a field in the development.  (`IsProper`,
`LocallyOfFiniteType`, `QuasiCompact` and `IsSeparated` for `projectiveSpaceToSpec 𝕜 1` are already
proved in `Model.lean`; use `variety_projectiveSpace`, `isProper_projectiveSpaceToSpec` and the
`Over` instance `projectiveSpaceOver`.)

This makes precise what the *geometric* residual `TwistRealization` still needs from the model
layer.  `ℙ¹` has rational points, so this is not the `C(𝕜) = ∅` configuration itself: the second
half — a curve with no rational point — is the twist. -/
theorem curveModel_projectiveSpace_one (𝕜 : Type) [Field 𝕜]
    (hS : Smooth (Work.PointlessIndexFive.projectiveSpaceToSpec 𝕜 1))
    (hG : GeometricallyIntegral (Work.PointlessIndexFive.projectiveSpaceToSpec 𝕜 1))
    (hD : topologicalKrullDim (Work.PointlessIndexFive.projectiveSpace 𝕜 1) = 1) :
    Nonempty (CurveModel 𝕜) :=
  ⟨{ C := Work.PointlessIndexFive.projectiveSpace 𝕜 1
     variety := Work.PointlessIndexFive.variety_projectiveSpace 𝕜 1 hG
     isProper := Work.PointlessIndexFive.isProper_projectiveSpaceToSpec 𝕜 1
     isSmooth := hS
     isGeomIntegral := hG
     dim_eq_one := hD }⟩

end Work.Twist
