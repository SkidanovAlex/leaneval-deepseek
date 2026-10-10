import Mathlib
import Submission.Work.PointlessIndexFive.Defs
import Submission.Work.PointlessIndexFive.divisorOfDegree_iff_five_dvd_of_pointless

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PointlessIndexFive

/-- The orbit divisor: a curve model realizing a pointless quintic twist carries a `𝕜`-rational
divisor of degree `5`. -/
theorem hasRatDivisorOfDegree_five_twistCurveModel {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    {D : QuinticTwist 𝕜} (M : TwistCurveModel D) (h : D.Pointless) :
    Work.Arithmetic.HasRatDivisorOfDegree 𝕜 M.C 5 :=
  ((M.divisorOfDegree_iff 5).trans (divisorOfDegree_iff_five_dvd_of_pointless D h 5)).mpr
    (dvd_refl 5)

end Work.PointlessIndexFive
