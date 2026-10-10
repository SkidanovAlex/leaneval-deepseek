import Mathlib
import Submission.Work.Twist.Defs
import Submission.Work.Twist.Assembly
import Submission.Work.Twist.hasLocalObstruction_of_pointless

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

open CategoryTheory AlgebraicGeometry
open Work.Twist

/-- **The arithmetic residual may be attacked in local-obstruction form.**  There is a pointless
quintic twist if and only if there is a quintic twist which admits a local obstruction
(`LocalObstruction`, `Submission/Work/Twist/Defs.lean`).  One direction is the criterion
`localObstruction_pointless` (`Submission/Work/Twist/Assembly.lean`), the other is
`hasLocalObstruction_of_pointless` (the tautological obstruction
`E(L) → E(L)/(σ - 1)E(L)`, in `Submission/Work/Twist/hasLocalObstruction_of_pointless.lean`).

Note the honest caveat: because `LocalObstruction` allows an arbitrary target group, this
equivalence is a formal one; what the paper supplies is a *place-based* way of producing such an
obstruction.  This result records that the obstruction *form* of the residual is faithful. -/
theorem hasPointlessTwistByObstruction_iff {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] :
    HasPointlessTwistByObstruction 𝕜 ↔ HasPointlessTwist 𝕜 := by
  constructor
  · intro h
    obtain ⟨D, hD⟩ := h
    exact ⟨D, localObstruction_pointless D hD⟩
  · rintro ⟨D, hD⟩
    exact ⟨D, hasLocalObstruction_of_pointless D hD⟩

end Work.Twist
