import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Ineq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L6Aux

theorem abs_le_sextic (z s b c d e f g : ℝ) (hz : 0 ≤ z) :
    |s * z ^ 6 + b * z ^ 5 + c * z ^ 4 + d * z ^ 3 + e * z ^ 2 + f * z + g|
      ≤ (|s| + |b| + |c| + |d| + |e| + |f| + |g|) * (1 + z) ^ 6 := by
  have h1z : 1 ≤ 1 + z := by linarith
  -- each power of z is dominated by (1+z)^6
  have hpow : ∀ k ≤ 6, z ^ k ≤ (1 + z) ^ 6 := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simpa using one_le_pow₀ h1z (n := 6)
    · exact le_trans (pow_le_pow_left₀ hz (by linarith) k) (pow_le_pow_right₀ h1z hk)
  -- each summand is bounded by |coefficient| * (1+z)^6
  have key : ∀ a k, k ≤ 6 → |a * z ^ k| ≤ |a| * (1 + z) ^ 6 := by
    intro a k hk
    rw [abs_mul, abs_of_nonneg (pow_nonneg hz k)]
    exact mul_le_mul_of_nonneg_left (hpow k hk) (abs_nonneg a)
  have hs := key s 6 le_rfl
  have hb := key b 5 (by norm_num)
  have hc := key c 4 (by norm_num)
  have hd := key d 3 (by norm_num)
  have he := key e 2 (by norm_num)
  have hf := key f 1 (by norm_num)
  have hg : |g| ≤ |g| * (1 + z) ^ 6 :=
    le_mul_of_one_le_right (abs_nonneg g) (hpow 0 (by norm_num))
  rw [abs_le']
  constructor
  · have h1 := (abs_le.mp hs).2
    have h2 := (abs_le.mp hb).2
    have h3 := (abs_le.mp hc).2
    have h4 := (abs_le.mp hd).2
    have h5 := (abs_le.mp he).2
    have h6 := (abs_le.mp hf).2
    have h7 := (abs_le.mp hg).2
    linarith
  · have h1 := (abs_le.mp hs).1
    have h2 := (abs_le.mp hb).1
    have h3 := (abs_le.mp hc).1
    have h4 := (abs_le.mp hd).1
    have h5 := (abs_le.mp he).1
    have h6 := (abs_le.mp hf).1
    have h7 := (abs_le.mp hg).1
    linarith

end Work.FTS.StrongPersist.L6Aux
