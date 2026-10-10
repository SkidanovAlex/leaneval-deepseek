import Mathlib
import Submission.Work.PointlessIndexFive.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PointlessIndexFive

/-- A curve model realizing a pointless quintic twist has no rational point. -/
theorem not_hasRatPoint_twistCurveModel {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    {D : QuinticTwist 𝕜} (M : TwistCurveModel D) (h : D.Pointless) :
    ¬ Work.Arithmetic.HasRatPoint 𝕜 M.C := by
  -- A `𝕜`-rational point of `M.C` is, by the descent bridge `hasPoint_iff`, a trivial class
  -- `D.toTorsor.cls = 1`; unwinding `Multiplicative.ofAdd` this is `D.cls = 0`, contradicting
  -- `D.Pointless`.
  intro hp
  exact h (ofAdd_eq_one.mp (M.hasPoint_iff.mp hp))

end Work.PointlessIndexFive
