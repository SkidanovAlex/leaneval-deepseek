import Mathlib
import Submission.Work.PointlessIndexFive.Defs
import Submission.Work.TorsorExistence.cls_eq_zero_iff

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PointlessIndexFive

/-- The coboundary criterion in element form: the twist is pointless iff `P` is not in the image
of the shift `σ - 1` acting on `E(L)`. -/
theorem pointless_iff_not_exists_shift {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : QuinticTwist 𝕜) : D.Pointless ↔ ¬ ∃ R : D.LPoints, D.shift R = D.PL :=
  not_congr (Work.TorsorExistence.cls_eq_zero_iff D)

end Work.PointlessIndexFive
