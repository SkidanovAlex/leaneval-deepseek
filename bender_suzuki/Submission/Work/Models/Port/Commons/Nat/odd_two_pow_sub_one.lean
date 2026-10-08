import Mathlib.Algebra.Ring.Parity

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.Nat

theorem odd_two_pow_sub_one (k : ℕ) (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  refine ⟨2 ^ (k - 1) - 1, ?_⟩
  have h1 : 2 ^ k = 2 * 2 ^ (k - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hk]
    rw [pow_succ']
  have h2 : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
  omega

end Commons.Nat