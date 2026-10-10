import Mathlib
import Submission.Work.PointlessIndexFive.Defs
import Submission.Work.PointlessIndexFive.period_eq_five_of_pointless
import Submission.Work.Arithmetic.jacSq_not_iso

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PointlessIndexFive

/-- **Shinder–Zhang, Lemma 2.7, for the quintic twist.**  A pointless quintic twist has period `5`,
hence `Jac²C` is not isomorphic to `C`: the automorphism criterion
`Work.Arithmetic.jacSq_not_iso` applies with `T.period = 5`.  This is the `C ≇ Jac²C` input of the
L-link construction, at the level of the twist. -/
theorem notIsoJacSq_of_pointless {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜)
    (h : D.Pointless) : D.toTorsor.NotIsoJacSq :=
  Work.Arithmetic.jacSq_not_iso D.toTorsor (period_eq_five_of_pointless D h)

end Work.PointlessIndexFive
