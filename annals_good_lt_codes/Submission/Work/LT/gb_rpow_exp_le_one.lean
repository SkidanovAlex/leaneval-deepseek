import Mathlib
set_option linter.unusedVariables false

namespace Work.LT

/-- Auxiliary: `3 · 2^{-2} = 3/4 ≤ 2^{-1/4}`.  Both sides are nonnegative, so it suffices to
compare fourth powers, which is a rational arithmetic fact. -/
theorem gb_three_quarters_le_inv_quarter :
    (3 : ℝ) * (2 : ℝ) ^ (-(2 : ℝ)) ≤ (2 : ℝ) ^ (-(1 : ℝ) / 4) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h4 : ((3 : ℝ) / 4) ^ 4 ≤ ((2 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 4 := by
    rw [show ((2 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 4 = (2 : ℝ) ^ (-(1 : ℝ)) by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num]
    norm_num
  have hle := (pow_le_pow_iff_left₀ (show (0 : ℝ) ≤ 3 / 4 by norm_num)
    (Real.rpow_nonneg h2.le _) (by norm_num : (4 : ℕ) ≠ 0)).mp h4
  calc (3 : ℝ) * (2 : ℝ) ^ (-(2 : ℝ)) = 3 / 4 := by norm_num
    _ ≤ (2 : ℝ) ^ (-(1 : ℝ) / 4) := hle

/-- The `r = 1` case of the exponent comparison in Kalachev--Panteleev Lemma 4, in the form in which it is used: `3 · 2^{2D-2} ≤ 2^{2D} · 2^{-1/4}` for `D ≥ 1`. -/
theorem gb_rpow_exp_le_one (D : ℕ) (hD : 1 ≤ D) :
    (3 : ℝ) * (2 : ℝ) ^ (2 * (D : ℝ) - 2) ≤
      (2 : ℝ) ^ (2 * (D : ℝ)) * (2 : ℝ) ^ (-(1 : ℝ) / 4) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  -- `2^{2D-2} = 2^{2D} · 2^{-2}` splits off the positive factor `2^{2D}`.
  have hsplit : (2 : ℝ) ^ (2 * (D : ℝ) - 2) =
      (2 : ℝ) ^ (2 * (D : ℝ)) * (2 : ℝ) ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add h2]
    congr 1
  calc (3 : ℝ) * (2 : ℝ) ^ (2 * (D : ℝ) - 2)
      = (3 * (2 : ℝ) ^ (-(2 : ℝ))) * (2 : ℝ) ^ (2 * (D : ℝ)) := by
        rw [hsplit]; ring
    _ ≤ (2 : ℝ) ^ (-(1 : ℝ) / 4) * (2 : ℝ) ^ (2 * (D : ℝ)) :=
        mul_le_mul_of_nonneg_right gb_three_quarters_le_inv_quarter
          (Real.rpow_nonneg h2.le _)
    _ = (2 : ℝ) ^ (2 * (D : ℝ)) * (2 : ℝ) ^ (-(1 : ℝ) / 4) := by ring

end Work.LT
