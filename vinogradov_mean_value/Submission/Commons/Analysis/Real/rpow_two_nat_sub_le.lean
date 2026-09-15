import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.unusedVariables false

namespace Commons.Analysis.Real

theorem rpow_two_nat_sub_le {N m : ℕ} {c e : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) (he : 0 ≤ e)
    (hm : c * (N : ℝ) ≤ (m : ℝ) + 1) :
    ((2 : ℝ) ^ (N - m)) ^ e ≤ (2 : ℝ) ^ ((N : ℝ) * (1 - c) * e) * (2 : ℝ) ^ e := by
  have hK : ((N - m : ℕ) : ℝ) ≤ (N : ℝ) * (1 - c) + 1 := by
    by_cases h : m ≤ N
    · have hcast : ((N - m : ℕ) : ℝ) = (N : ℝ) - (m : ℝ) := Nat.cast_sub h
      rw [hcast]
      have hm' : c * (N : ℝ) - 1 ≤ (m : ℝ) := by linarith
      nlinarith [hc, hc1]
    · have hzero : N - m = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_le h))
      rw [hzero]
      push_cast
      nlinarith [hc, hc1, (Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))]
  have hmul : ((N - m : ℕ) : ℝ) * e ≤ (N : ℝ) * (1 - c) * e + e := by
    have h1 := mul_le_mul_of_nonneg_right hK he
    nlinarith [h1]
  calc ((2 : ℝ) ^ (N - m)) ^ e
      = (2 : ℝ) ^ (((N - m : ℕ) : ℝ) * e) := by
        rw [← Real.rpow_natCast (2 : ℝ) (N - m),
          ← Real.rpow_mul (show (0 : ℝ) ≤ 2 by norm_num)]
    _ ≤ (2 : ℝ) ^ ((N : ℝ) * (1 - c) * e + e) :=
        Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) hmul
    _ = (2 : ℝ) ^ ((N : ℝ) * (1 - c) * e) * (2 : ℝ) ^ e :=
        Real.rpow_add (show (0 : ℝ) < 2 by norm_num) _ _

end Commons.Analysis.Real