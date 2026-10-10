import Mathlib
import Submission.Work.PointlessIndexFive.Defs
import Submission.Work.TorsorExistence.period_toTorsor_eq_five_iff

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PointlessIndexFive

/-- A pointless quintic twist has period exactly `5` in the `Work.Arithmetic.Torsor`
presentation. -/
theorem period_eq_five_of_pointless {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜)
    (h : D.Pointless) : D.toTorsor.period = 5 :=
  (Work.TorsorExistence.period_toTorsor_eq_five_iff D).mpr h

end Work.PointlessIndexFive
