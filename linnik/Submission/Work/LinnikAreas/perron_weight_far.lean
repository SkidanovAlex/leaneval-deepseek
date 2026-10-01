import Mathlib

namespace Work.LinnikAreas

/-- Far-range weight bound for the Perron/truncation error: once `n ≥ 2x` and `T ≥ x²`,
the weight `min 1 (1 / (T |log (x/n)|))` is at most `2 / x²`. -/
theorem perron_weight_far :
    ∀ x T : ℝ, ∀ n : ℕ, 1 ≤ x → x ^ 2 ≤ T → 2 * x ≤ (n : ℝ) →
      min 1 (1 / (T * |Real.log (x / (n : ℝ))|)) ≤ 2 / x ^ 2 := by
  intro x T n hx hT hn
  have hxpos : 0 < x := lt_of_lt_of_le one_pos hx
  have hnpos : 0 < (n : ℝ) := by
    have : (0:ℝ) < 2 * x := by linarith
    linarith
  have hx2pos : 0 < x ^ 2 := by positivity
  have hTpos : 0 < T := lt_of_lt_of_le hx2pos hT
  have hratio_pos : 0 < x / (n : ℝ) := div_pos hxpos hnpos
  have hratio : x / (n : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hnpos]; linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2half : (1:ℝ)/2 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlog : Real.log (x / (n : ℝ)) ≤ - Real.log 2 := by
    have h := Real.log_le_log hratio_pos hratio
    rwa [Real.log_div one_ne_zero (by norm_num : (2:ℝ) ≠ 0), Real.log_one, zero_sub] at h
  have hy_neg : Real.log (x / (n:ℝ)) < 0 := by linarith [hlog, hlog2pos]
  have habs : |Real.log (x / (n:ℝ))| = - Real.log (x / (n:ℝ)) := abs_of_neg hy_neg
  have hge : Real.log 2 ≤ |Real.log (x / (n:ℝ))| := by
    rw [habs]; linarith [hlog]
  have hmul : x^2 * Real.log 2 ≤ T * |Real.log (x / (n:ℝ))| :=
    mul_le_mul hT hge (le_of_lt hlog2pos) (le_of_lt hTpos)
  have hhalf : x^2 * (1/2) ≤ T * |Real.log (x / (n:ℝ))| := by
    have : x^2 * (1/2) ≤ x^2 * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlog2half (le_of_lt hx2pos)
    linarith
  have hden_pos : 0 < x^2 * (1/2) := by positivity
  have hinv : 1 / (T * |Real.log (x / (n:ℝ))|) ≤ 1 / (x^2 * (1/2)) :=
    one_div_le_one_div_of_le hden_pos hhalf
  have hrhs : 1 / (x^2 * (1/2)) = 2 / x^2 := by field_simp
  calc min 1 (1 / (T * |Real.log (x / (n:ℝ))|)) ≤ 1 / (T * |Real.log (x / (n:ℝ))|) := min_le_right _ _
    _ ≤ 1 / (x^2 * (1/2)) := hinv
    _ = 2 / x^2 := hrhs

end Work.LinnikAreas
