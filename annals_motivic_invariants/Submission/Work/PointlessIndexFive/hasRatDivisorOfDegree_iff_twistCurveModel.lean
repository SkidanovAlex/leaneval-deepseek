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

/-- The divisors of a curve model realizing a pointless quintic twist have degrees exactly the
multiples of `5`: this is the index-`5` condition transported along the bridge
`TwistCurveModel.divisorOfDegree_iff`. -/
theorem hasRatDivisorOfDegree_iff_twistCurveModel {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    {D : QuinticTwist 𝕜} (M : TwistCurveModel D) (h : D.Pointless) (n : ℕ) :
    Work.Arithmetic.HasRatDivisorOfDegree 𝕜 M.C n ↔ 5 ∣ n :=
  (M.divisorOfDegree_iff n).trans (divisorOfDegree_iff_five_dvd_of_pointless D h n)

end Work.PointlessIndexFive
