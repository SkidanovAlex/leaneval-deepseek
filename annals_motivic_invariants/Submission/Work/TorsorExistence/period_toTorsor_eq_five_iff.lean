import Mathlib
import Submission.Work.TorsorExistence.Twist
import Submission.Work.TorsorExistence.five_smul_cls
import Submission.Work.Arithmetic.period_eq_five_iff

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.TorsorExistence

/-- **Period five.**  The period of the twist, as a `Work.Arithmetic.Torsor`
(`toTorsor D`, whose Weil–Châtelet group is `H¹(ℤ/5, E(L))` and whose class is the class of the
cocycle `σ ↦ P`), is `5` if and only if that class is non-trivial, i.e. iff `C(𝕜) = ∅`: the
period divides `5` by the orbit-divisor statement, and `addOrderOf (cls D) ≠ 1` exactly when
`cls D ≠ 0`.  (`D.toTorsor.period = orderOf (Multiplicative.ofAdd (D.cls)) = addOrderOf D.cls`.) -/
theorem period_toTorsor_eq_five_iff {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) :
    D.toTorsor.period = 5 ↔ D.Pointless := by
  show orderOf (Multiplicative.ofAdd (QuinticTwist.cls D)) = 5 ↔ QuinticTwist.cls D ≠ 0
  rw [orderOf_ofAdd_eq_addOrderOf]
  constructor
  · intro h h0
    rw [h0, addOrderOf_zero] at h
    exact absurd h (by decide)
  · intro h
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact addOrderOf_eq_prime (five_smul_cls D) h

end Work.TorsorExistence
