import Mathlib
import Submission.Work.PointlessIndexFive.Defs
import Submission.Work.TorsorExistence.five_smul_cls

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.PointlessIndexFive

/-- The class of the cocycle `σ ↦ P` has additive order exactly `5` in
`H¹(ℤ/5, E(L)) = ker N / (σ - 1)E(L)` as soon as it is non-zero: it is annihilated by `5`
(the orbit-divisor statement `Work.TorsorExistence.five_smul_cls`), and it is non-zero by
`D.Pointless`, so its (necessarily `5`-torsion) order cannot be `1`. -/
theorem addOrderOf_cls_eq_five {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜)
    (h : D.Pointless) : addOrderOf D.cls = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact addOrderOf_eq_prime (Work.TorsorExistence.five_smul_cls D) h

/-- The index-`5` condition: for a pointless quintic twist, every degree of a rational divisor is
divisible by `5` (the class has exact additive order `5`). -/
theorem five_dvd_of_pointless {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜)
    (h : D.Pointless) {n : ℕ} (hn : n • D.cls = 0) : 5 ∣ n := by
  rw [← addOrderOf_cls_eq_five D h]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hn

end Work.PointlessIndexFive
