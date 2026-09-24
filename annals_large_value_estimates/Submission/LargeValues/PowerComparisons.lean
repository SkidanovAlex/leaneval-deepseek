import Mathlib

set_option autoImplicit false

/-!
# Real-power comparisons used in the reduction of Guth–Maynard Theorem 1.1

Compare terms of the classical large-value bounds with terms of
`bound N V T = N^2 V^{-2} + N^{18/5} V^{-4} + T N^{12/5} V^{-4}`.
-/

namespace Submission.LargeValues

open Real

private lemma rpow_add_mul (x : ℝ) (hx0 : 0 < x) (a b : ℝ) :
    x ^ a * x ^ b = x ^ (a + b) := (Real.rpow_add hx0 a b).symm

/-- Case 2 (small `V`): if `V ≤ 3·N^{7/10}` then `N·V^{-2} ≤ 9·N^{12/5}·V^{-4}`. -/
theorem N_mul_V_neg_two_le (x V : ℝ) (hx1 : 1 ≤ x) (hV0 : 0 < V)
    (hV : V ≤ 3 * x ^ (7 / 10 : ℝ)) :
    x * V ^ (-2 : ℤ) ≤ 9 * x ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hVsq : V ^ 2 ≤ 9 * x ^ (7 / 5 : ℝ) := by
    have h1 : V ^ 2 ≤ (3 * x ^ (7 / 10 : ℝ)) ^ 2 := by
      refine sq_le_sq.mpr ?_
      rw [abs_of_nonneg (le_of_lt hV0), abs_of_nonneg (by positivity)]
      exact hV
    have h2 : (3 * x ^ (7 / 10 : ℝ)) ^ 2 = 9 * x ^ (7 / 5 : ℝ) := by
      rw [mul_pow, ← Real.rpow_natCast (x ^ (7 / 10 : ℝ)) 2, ← Real.rpow_mul (le_of_lt hx0)]
      norm_num
    linarith [h1, h2.symm.le, h2.le]
  have hmain : x * V ^ 2 ≤ 9 * x ^ (12 / 5 : ℝ) := by
    calc
      x * V ^ 2 ≤ x * (9 * x ^ (7 / 5 : ℝ)) := mul_le_mul_of_nonneg_left hVsq (le_of_lt hx0)
      _ = 9 * (x * x ^ (7 / 5 : ℝ)) := by ring
      _ = 9 * (x ^ (1 : ℝ) * x ^ (7 / 5 : ℝ)) := by rw [Real.rpow_one]
      _ = 9 * x ^ (12 / 5 : ℝ) := by rw [rpow_add_mul x hx0]; norm_num
  rw [zpow_neg, zpow_neg, inv_eq_one_div, inv_eq_one_div]
  field_simp
  nlinarith [hmain, sq_nonneg V]

/-- Case 3 (large `V`): if `N^{4/5} ≤ V` then `N^4·V^{-6} ≤ N^{12/5}·V^{-4}`. -/
theorem pow_four_mul_V_neg_six_le (x V : ℝ) (hx1 : 1 ≤ x) (hV0 : 0 < V)
    (hV : x ^ (4 / 5 : ℝ) ≤ V) :
    x ^ 4 * V ^ (-6 : ℤ) ≤ x ^ (12 / 5 : ℝ) * V ^ (-4 : ℤ) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hVsq : x ^ (8 / 5 : ℝ) ≤ V ^ 2 := by
    have h1 : (x ^ (4 / 5 : ℝ)) ^ 2 ≤ V ^ 2 := by
      refine sq_le_sq.mpr ?_
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (le_of_lt hV0)]
      exact hV
    have h2 : (x ^ (4 / 5 : ℝ)) ^ 2 = x ^ (8 / 5 : ℝ) := by
      rw [← Real.rpow_natCast (x ^ (4 / 5 : ℝ)) 2, ← Real.rpow_mul (le_of_lt hx0)]
      norm_num
    linarith [h1, h2.symm.le, h2.le]
  have hmain : x ^ 4 ≤ x ^ (12 / 5 : ℝ) * V ^ 2 := by
    have h4 : x ^ (4 : ℕ) = x ^ (4 : ℝ) := (Real.rpow_natCast x 4).symm
    rw [h4]
    calc
      x ^ (4 : ℝ) = x ^ (12 / 5 : ℝ) * x ^ (8 / 5 : ℝ) := by
          rw [rpow_add_mul x hx0]; norm_num
      _ ≤ x ^ (12 / 5 : ℝ) * V ^ 2 :=
        mul_le_mul_of_nonneg_left hVsq (Real.rpow_nonneg (le_of_lt hx0) _)
  rw [zpow_neg, zpow_neg, inv_eq_one_div, inv_eq_one_div]
  field_simp
  nlinarith [hmain, sq_nonneg V, sq_nonneg (V ^ 2), mul_pos hV0 hV0]

/-- Case 4 (middle regime): if `V ≤ N^{4/5}` then `N^2·V^{-2} ≤ N^{18/5}·V^{-4}`. -/
theorem pow_two_mul_V_neg_two_le (x V : ℝ) (hx1 : 1 ≤ x) (hV0 : 0 < V)
    (hV : V ≤ x ^ (4 / 5 : ℝ)) :
    x ^ 2 * V ^ (-2 : ℤ) ≤ x ^ (18 / 5 : ℝ) * V ^ (-4 : ℤ) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hVsq : V ^ 2 ≤ x ^ (8 / 5 : ℝ) := by
    have h1 : V ^ 2 ≤ (x ^ (4 / 5 : ℝ)) ^ 2 := by
      refine sq_le_sq.mpr ?_
      rw [abs_of_nonneg (le_of_lt hV0), abs_of_nonneg (by positivity)]
      exact hV
    have h2 : (x ^ (4 / 5 : ℝ)) ^ 2 = x ^ (8 / 5 : ℝ) := by
      rw [← Real.rpow_natCast (x ^ (4 / 5 : ℝ)) 2, ← Real.rpow_mul (le_of_lt hx0)]
      norm_num
    linarith [h1, h2.symm.le, h2.le]
  have hmain : x ^ 2 * V ^ 2 ≤ x ^ (18 / 5 : ℝ) := by
    have h2 : x ^ (2 : ℕ) = x ^ (2 : ℝ) := (Real.rpow_natCast x 2).symm
    rw [h2]
    calc
      x ^ (2 : ℝ) * V ^ 2 ≤ x ^ (2 : ℝ) * x ^ (8 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_left hVsq (by positivity)
      _ = x ^ (2 + 8 / 5 : ℝ) := rpow_add_mul x hx0 _ _
      _ = x ^ (18 / 5 : ℝ) := by norm_num
  rw [zpow_neg, zpow_neg, inv_eq_one_div, inv_eq_one_div]
  field_simp
  nlinarith [hmain, sq_nonneg V]

end Submission.LargeValues
