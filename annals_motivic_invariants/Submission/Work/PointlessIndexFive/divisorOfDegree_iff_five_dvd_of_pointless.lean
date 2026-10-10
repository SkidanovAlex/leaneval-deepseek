import Mathlib
import Submission.Work.PointlessIndexFive.Defs
import Submission.Work.PointlessIndexFive.five_dvd_of_pointless
import Submission.Work.PointlessIndexFive.toTorsor_divisorOfDegree_iff

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PointlessIndexFive

/-- **The index-`5` condition, in twist form.**  For a pointless quintic twist, the twist carries a
rational divisor of degree `n` if and only if `5 ∣ n`: the set of degrees of rational divisors is
exactly `5ℕ`.  This is the orbit-divisor statement (period divides `5`, `five_smul_cls`) together
with the non-vanishing of the class. -/
theorem divisorOfDegree_iff_five_dvd_of_pointless {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : QuinticTwist 𝕜) (h : D.Pointless) (n : ℕ) :
    D.toTorsor.DivisorOfDegree n ↔ 5 ∣ n := by
  -- `DivisorOfDegree n` is `cls ^ n = 1` in the multiplicative presentation, i.e. `n • cls = 0`
  -- additively (`toTorsor_divisorOfDegree_iff`), and `n • cls = 0` holds exactly when the
  -- additive order of `cls` divides `n` (`addOrderOf_dvd_iff_nsmul_eq_zero`); that order is `5`
  -- for a pointless twist (`addOrderOf_cls_eq_five`, from the orbit-divisor statement
  -- `five_smul_cls` together with `cls ≠ 0`).
  rw [toTorsor_divisorOfDegree_iff, addOrderOf_dvd_iff_nsmul_eq_zero.symm,
    addOrderOf_cls_eq_five D h]

end Work.PointlessIndexFive
