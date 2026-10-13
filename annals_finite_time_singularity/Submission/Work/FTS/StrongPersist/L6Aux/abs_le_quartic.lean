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

theorem abs_le_quartic (z s b c d e : ℝ) (hz : 0 ≤ z) :
    |s * z ^ 4 + b * z ^ 3 + c * z ^ 2 + d * z + e| ≤ (|s| + |b| + |c| + |d| + |e|) * (1 + z) ^ 4 := by
  have h1z : (1 : ℝ) ≤ 1 + z := by linarith
  have h4 : z ^ 4 ≤ (1 + z) ^ 4 := pow_le_pow_left₀ hz (by linarith) 4
  have h3 : z ^ 3 ≤ (1 + z) ^ 4 :=
    le_trans (pow_le_pow_left₀ hz (by linarith) 3)
      (pow_le_pow_right₀ h1z (show (3 : ℕ) ≤ 4 by norm_num))
  have h2 : z ^ 2 ≤ (1 + z) ^ 4 :=
    le_trans (pow_le_pow_left₀ hz (by linarith) 2)
      (pow_le_pow_right₀ h1z (show (2 : ℕ) ≤ 4 by norm_num))
  have h1 : z ≤ (1 + z) ^ 4 := by
    have hz1 : z ≤ 1 + z := by linarith
    have hh : (1 + z) ≤ (1 + z) ^ 4 := by
      simpa using pow_le_pow_right₀ h1z (show (1 : ℕ) ≤ 4 by norm_num)
    exact le_trans hz1 hh
  have h0 : (1 : ℝ) ≤ (1 + z) ^ 4 := one_le_pow₀ h1z
  have step1 : |s * z ^ 4 + b * z ^ 3 + c * z ^ 2 + d * z + e|
      ≤ |s * z ^ 4| + |b * z ^ 3| + |c * z ^ 2| + |d * z| + |e| := by
    have hA := abs_add_le (s * z ^ 4 + b * z ^ 3 + c * z ^ 2 + d * z) e
    have hB := abs_add_le (s * z ^ 4 + b * z ^ 3 + c * z ^ 2) (d * z)
    have hC := abs_add_le (s * z ^ 4 + b * z ^ 3) (c * z ^ 2)
    have hD := abs_add_le (s * z ^ 4) (b * z ^ 3)
    linarith
  have step2 : |s * z ^ 4| + |b * z ^ 3| + |c * z ^ 2| + |d * z| + |e|
      = |s| * z ^ 4 + |b| * z ^ 3 + |c| * z ^ 2 + |d| * z + |e| := by
    simp only [abs_mul]
    rw [abs_of_nonneg (pow_nonneg hz 4), abs_of_nonneg (pow_nonneg hz 3),
      abs_of_nonneg (pow_nonneg hz 2), abs_of_nonneg hz]
  have step3 : |s| * z ^ 4 + |b| * z ^ 3 + |c| * z ^ 2 + |d| * z + |e|
      ≤ (|s| + |b| + |c| + |d| + |e|) * (1 + z) ^ 4 := by
    have hs := abs_nonneg s
    have hb := abs_nonneg b
    have hc := abs_nonneg c
    have hd := abs_nonneg d
    have he := abs_nonneg e
    have m4 : |s| * z ^ 4 ≤ |s| * (1 + z) ^ 4 := mul_le_mul_of_nonneg_left h4 hs
    have m3 : |b| * z ^ 3 ≤ |b| * (1 + z) ^ 4 := mul_le_mul_of_nonneg_left h3 hb
    have m2 : |c| * z ^ 2 ≤ |c| * (1 + z) ^ 4 := mul_le_mul_of_nonneg_left h2 hc
    have m1 : |d| * z ≤ |d| * (1 + z) ^ 4 := mul_le_mul_of_nonneg_left h1 hd
    have m0 : |e| ≤ |e| * (1 + z) ^ 4 := le_mul_of_one_le_right he h0
    nlinarith [m4, m3, m2, m1, m0]
  linarith [step1, step2, step3]

end Work.FTS.StrongPersist.L6Aux
