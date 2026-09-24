import Mathlib

namespace Work.GM.Affine

/-- `sinc (π y)^2 ≥ 3/5` for `|y| ≤ 1/3`.

For `t = π|y| ≤ π/3` we have `sin t ≥ t - t³/6 ≥ (4/5) t` (because `t² ≤ 6/5`), so
`|sinc (π y)| = sin t / t ≥ 4/5`, and `(4/5)² = 16/25 ≥ 3/5`. -/
theorem sinc_third_lower_bound {y : ℝ} (hy : |y| ≤ 1 / 3) :
    (3 / 5 : ℝ) ≤ Real.sinc (Real.pi * y) ^ 2 := by
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [mul_zero, Real.sinc_zero]; norm_num
  · have hyabs_pos : 0 < |y| := abs_pos.mpr hy0
    have ht0 : 0 ≤ Real.pi * |y| := by positivity
    have ht1 : Real.pi * |y| ≤ 21 / 20 := by
      calc Real.pi * |y| ≤ Real.pi * (1 / 3) := mul_le_mul_of_nonneg_left hy Real.pi_pos.le
        _ ≤ (21 / 20 : ℝ) := le_of_lt (by nlinarith [Real.pi_lt_d2])
    have ht2 : (Real.pi * |y|) ^ 2 ≤ 6 / 5 := by nlinarith [ht0, ht1]
    have hsin : (4 / 5) * (Real.pi * |y|) ≤ Real.sin (Real.pi * |y|) := by
      have h := Real.sin_ge_sub_cube ht0
      have ht3 : (Real.pi * |y|) ^ 3 ≤ (6 / 5) * (Real.pi * |y|) := by
        have hm := mul_le_mul_of_nonneg_right ht2 ht0
        nlinarith [hm]
      have h2 : (Real.pi * |y|) ^ 3 / 6 ≤ (Real.pi * |y|) / 5 := by linarith
      linarith
    have hsin_nonneg : ∀ {u : ℝ}, 0 ≤ u → u ≤ 1 / 3 → 0 ≤ Real.sin (Real.pi * u) := by
      intro u hu0 hu1
      exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by
        calc Real.pi * u ≤ Real.pi * (1 / 3) := mul_le_mul_of_nonneg_left hu1 Real.pi_pos.le
          _ ≤ Real.pi := by nlinarith [Real.pi_pos])
    have habs_sin : |Real.sin (Real.pi * y)| = Real.sin (Real.pi * |y|) := by
      rcases lt_or_ge y 0 with hneg | hnonneg
      · have h1 : |y| = -y := abs_of_neg hneg
        rw [h1, show Real.pi * y = -(Real.pi * -y) by ring, Real.sin_neg, abs_neg,
          abs_of_nonneg (hsin_nonneg (by linarith) (by linarith [hy, abs_of_neg hneg]))]
      · rw [abs_of_nonneg hnonneg,
          abs_of_nonneg (hsin_nonneg hnonneg (by linarith [abs_of_nonneg hnonneg ▸ hy]))]
    have hbound : (4 / 5 : ℝ) ≤ |Real.sinc (Real.pi * y)| := by
      rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hy0), abs_div, habs_sin,
        abs_mul, abs_of_pos Real.pi_pos, le_div_iff₀ (by positivity)]
      linarith [hsin]
    have hone : (3 / 5 : ℝ) ≤ (4 / 5) ^ 2 := by norm_num
    have hsq : (4 / 5 : ℝ) ^ 2 ≤ (Real.sinc (Real.pi * y)) ^ 2 := by
      rw [← sq_abs (Real.sinc (Real.pi * y))]
      exact pow_le_pow_left₀ (by norm_num) hbound 2
    linarith

end Work.GM.Affine
