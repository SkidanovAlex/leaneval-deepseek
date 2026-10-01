import Mathlib

namespace Work.ZeroDensity.Ingham

/-- For positive reals `x y`, the difference `|x - y|` is controlled by
`max x y` times `|log x - log y|`. This is the analytic content of the target,
obtained from `1 - 1/z ≤ log z` for `z ≥ 1`. -/
lemma abs_sub_le_max_mul_abs_log_sub_real {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |x - y| ≤ max x y * |Real.log x - Real.log y| := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hyne : y ≠ 0 := ne_of_gt hy
  rcases le_total x y with hxy | hyx
  · have hlog : Real.log x ≤ Real.log y := Real.log_le_log hx hxy
    have h1 : |x - y| = y - x := by rw [abs_of_nonpos (by linarith), neg_sub]
    have h2 : |Real.log x - Real.log y| = Real.log y - Real.log x := by
      rw [abs_of_nonpos (by linarith), neg_sub]
    have h3 : max x y = y := max_eq_right hxy
    rw [h1, h2, h3]
    have h := Real.one_sub_inv_le_log_of_pos (x := y / x) (div_pos hy hx)
    rw [inv_div, Real.log_div hyne hxne] at h
    have hmul := mul_le_mul_of_nonneg_left h (le_of_lt hy)
    have hsimp : y * (1 - x / y) = y - x := by field_simp
    rw [hsimp] at hmul
    exact hmul
  · have hlog : Real.log y ≤ Real.log x := Real.log_le_log hy hyx
    have h1 : |x - y| = x - y := by rw [abs_of_nonneg (by linarith)]
    have h2 : |Real.log x - Real.log y| = Real.log x - Real.log y := by
      rw [abs_of_nonneg (by linarith)]
    have h3 : max x y = x := max_eq_left hyx
    rw [h1, h2, h3]
    have h := Real.one_sub_inv_le_log_of_pos (x := x / y) (div_pos hx hy)
    rw [inv_div, Real.log_div hxne hyne] at h
    have hmul := mul_le_mul_of_nonneg_left h (le_of_lt hx)
    have hsimp : x * (1 - y / x) = x - y := by field_simp
    rw [hsimp] at hmul
    exact hmul

lemma abs_sub_le_max_mul_abs_log_sub (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    |(m : ℝ) - (n : ℝ)| ≤ max (m : ℝ) (n : ℝ) * |Real.log (m : ℝ) - Real.log (n : ℝ)| := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact abs_sub_le_max_mul_abs_log_sub_real hmpos hnpos

end Work.ZeroDensity.Ingham
