import Mathlib

namespace Work.TMC16Core.Assembly

theorem tm_arith_scale {a b Q : ℝ} (hb : 0 < b) (hb2 : b ≤ 2 * a)
    (haQ : a ≤ Real.rpow Q (8 / 9)) (hQ : (40 : ℝ) ^ 9 ≤ Q) :
    10 * a + 15 * b ≤ Q := by
  have hQpos : (0:ℝ) < Q := by
    have : (0:ℝ) < (40:ℝ)^9 := by norm_num
    linarith
  -- Step 1: `40 ≤ Q^(1/9)`, since `Q ≥ 40^9` and `(40^9)^(1/9) = 40`.
  have h40 : (40:ℝ) ≤ Q ^ ((1:ℝ)/9) := by
    have h := Real.rpow_le_rpow (show (0:ℝ) ≤ (40:ℝ)^9 by norm_num) hQ
      (show (0:ℝ) ≤ (1:ℝ)/9 by norm_num)
    have h1 : ((40:ℝ)^9 : ℝ) ^ ((1:ℝ)/9) = 40 := by
      rw [← Real.rpow_natCast (40:ℝ) 9, ← Real.rpow_mul (show (0:ℝ) ≤ 40 by norm_num)]
      norm_num
    rw [h1] at h
    exact h
  -- Step 2: `40 * Q^(8/9) ≤ Q`, since `Q = Q^(1/9) * Q^(8/9)`.
  have hmain : 40 * Q ^ ((8:ℝ)/9) ≤ Q := by
    have hQeq : Q ^ ((1:ℝ)/9) * Q ^ ((8:ℝ)/9) = Q := by
      rw [← Real.rpow_add hQpos, show (1:ℝ)/9 + 8/9 = 1 by norm_num, Real.rpow_one]
    calc 40 * Q ^ ((8:ℝ)/9) ≤ Q ^ ((1:ℝ)/9) * Q ^ ((8:ℝ)/9) :=
          mul_le_mul_of_nonneg_right h40 (Real.rpow_nonneg (le_of_lt hQpos) _)
      _ = Q := hQeq
  -- Step 3: assemble `10a + 15b ≤ 40a ≤ 40 Q^(8/9) ≤ Q`.
  calc 10*a + 15*b ≤ 40*a := by linarith [hb, hb2]
    _ ≤ 40 * Q ^ ((8:ℝ)/9) := by
        exact mul_le_mul_of_nonneg_left haQ (show (0:ℝ) ≤ 40 by norm_num)
    _ ≤ Q := hmain

end Work.TMC16Core.Assembly
