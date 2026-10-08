import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV12

/-- Auxiliary bound: for `1 ≤ d`, `(2^d - 1)^2 + 2 ≤ 2^(2d)`. -/
private lemma sq_pred_two_pow_add_two_le (d : ℕ) (hd : 1 ≤ d) :
    (2 ^ d - 1) * (2 ^ d - 1) + 2 ≤ 2 ^ (2 * d) := by
  have hx2 : 2 ≤ 2 ^ d := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  have h1 : 1 ≤ 2 ^ d := le_trans (by norm_num) hx2
  have hsq : (2 ^ d - 1) * (2 ^ d - 1) + 2 ≤ (2 ^ d) * (2 ^ d) := by
    nlinarith [Nat.sub_add_cancel h1]
  have hpow : (2 ^ d) * (2 ^ d) = 2 ^ (2 * d) := by
    rw [← pow_two, ← pow_mul, Nat.mul_comm]
  omega

theorem mul_lt_two_pow_sub_one {d k m t : ℕ} (hd : 1 ≤ d) (hk : 2 * d ≤ k)
    (hm : m ≤ 2 ^ d - 1) (ht : t ≤ m) : m * t < 2 ^ k - 1 := by
  have hmul : m * t ≤ (2 ^ d - 1) * (2 ^ d - 1) :=
    Nat.mul_le_mul hm (le_trans ht hm)
  have hpowk : 2 ^ (2 * d) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h2 : m * t + 2 ≤ 2 ^ k := by
    have := sq_pred_two_pow_add_two_le d hd
    omega
  rw [Nat.lt_sub_iff_add_lt]
  omega

end Work.ThmF.ChV12
