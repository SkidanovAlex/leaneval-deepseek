import Mathlib
import Submission.Work.Twist.Defs
import Submission.Work.Twist.Assembly

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

open CategoryTheory AlgebraicGeometry
open Work.Twist

/-- **The arithmetic residual, in the paper's own data.**  `HasPointlessTwist 𝕜` holds if and only
if there are a curve `E/𝕜` with a rational point of order `5` and `j ≠ 1728` (step (B)) and a
cyclic quintic extension `L/𝕜` (step (A)) whose twist is pointless.  In other words the residual of
`Work.PointlessIndexFive` may be stated without naming the bundle `QuinticTwist`.

Direction `⟸` is `Work.PointlessIndexFive.hasPointlessTwist_of_pointless_data`; direction `⟹` uses
`quinticTwistOf_toFiveTorsionCurve` (`Submission/Work/Twist/Assembly.lean`), which rebuilds a
`QuinticTwist` from its `FiveTorsionCurve` and its extension. -/
theorem hasPointlessTwist_iff_exists_pointless {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] :
    HasPointlessTwist 𝕜 ↔
      ∃ (C₅ : FiveTorsionCurve 𝕜) (L : CyclicExtension 𝕜 5), PointlessOf C₅ L := by
  constructor
  · -- A pointless twist yields the paper's own data: its `FiveTorsionCurve` and its extension.
    rintro ⟨D, hD⟩
    refine ⟨Work.TorsorExistence.QuinticTwist.toFiveTorsionCurve D, D.ext, ?_⟩
    show Work.TorsorExistence.QuinticTwist.Pointless
      (quinticTwistOf (Work.TorsorExistence.QuinticTwist.toFiveTorsionCurve D) D.ext)
    rw [quinticTwistOf_toFiveTorsionCurve D]
    exact hD
  · -- Conversely, the paper's data is a `QuinticTwist`.
    rintro ⟨C₅, L, h⟩
    exact Work.PointlessIndexFive.hasPointlessTwist_of_pointless_data C₅ L h

end Work.Twist
