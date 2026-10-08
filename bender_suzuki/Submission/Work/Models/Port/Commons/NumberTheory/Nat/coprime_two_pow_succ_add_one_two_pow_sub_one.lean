import Mathlib
import Submission.Work.Models.Port.Commons.Nat.coprime_one_add_two_pow_succ

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.NumberTheory.Nat

/-- `2^(n+1) + 1` is coprime to `2^(2n+1) - 1`.

Any common divisor `d` of `2^(n+1) + 1` and `2^(2n+1) - 1` divides
`2^(2(n+1)) - 1 = (2^(n+1) + 1)(2^(n+1) - 1)` and also
`2 · (2^(2n+1) - 1)`, hence divides the difference `1`; so `d = 1`.

This is the commutative rearrangement of the companion lemma
`Commons.Nat.coprime_one_add_two_pow_succ`. -/
theorem coprime_two_pow_succ_add_one_two_pow_sub_one (n : ℕ) :
    Nat.Coprime (2 ^ (n + 1) + 1) (2 ^ (2 * n + 1) - 1) := by
  simpa only [Nat.add_comm (2 ^ (n + 1)) 1] using
    Commons.Nat.coprime_one_add_two_pow_succ n

end Commons.NumberTheory.Nat
