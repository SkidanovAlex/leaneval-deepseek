import Mathlib
import Submission.Work.PointlessIndexFive.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PointlessIndexFive

/-- The dictionary between the multiplicative presentation of the class of the twist and the
additive one: `(ofAdd cls)^n = 1` iff `n • cls = 0`. -/
theorem ofAdd_cls_pow_eq_one_iff {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜)
    (n : ℕ) : (Multiplicative.ofAdd D.cls) ^ n = 1 ↔ n • D.cls = 0 := by
  rw [← ofAdd_nsmul, ofAdd_eq_one]

end Work.PointlessIndexFive
