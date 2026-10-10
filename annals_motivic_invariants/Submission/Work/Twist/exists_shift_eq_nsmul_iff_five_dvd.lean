import Mathlib
import Submission.Work.Twist.Defs
import Submission.Work.Twist.nsmul_cls_eq_zero_iff

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Twist

open CategoryTheory AlgebraicGeometry
open Work.Twist

/-- **The index-`5` condition of the twist, in element form.**  For a pointless quintic twist,
`n • P` is a coboundary if and only if `5 ∣ n`: the class `cls` has exact additive order `5`, so
`n • cls = 0` exactly for the multiples of `5`, and `n • cls = 0` is `∃ R, σ R - R = n • P`
(`nsmul_cls_eq_zero_iff`, `Submission/Work/Twist/nsmul_cls_eq_zero_iff.lean`).

Together with the identity `σ 0 - 0 = 0` this is the statement that the set of degrees of rational
divisors on the twist is exactly `5ℕ`, which is the `dvd` field of
`Work.TorsorExistence.PointlessIndexFiveCurve`. -/
theorem exists_shift_eq_nsmul_iff_five_dvd {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) (h : D.Pointless) (n : ℕ) :
    (∃ R : D.LPoints, D.shift R = (n : ℕ) • D.PL) ↔ 5 ∣ n := by
  -- `n • P` is a coboundary iff `n • cls = 0` (`nsmul_cls_eq_zero_iff`), and the class is
  -- `5`-torsion (`five_smul_cls`) without being zero (`h`), so it has exact additive order `5`.
  rw [← Work.Twist.nsmul_cls_eq_zero_iff D n, ← addOrderOf_dvd_iff_nsmul_eq_zero,
    Work.PointlessIndexFive.addOrderOf_cls_eq_five D h]

end Work.Twist
