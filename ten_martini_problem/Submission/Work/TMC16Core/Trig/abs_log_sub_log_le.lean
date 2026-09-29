import Mathlib

namespace Work.TMC16Core.Trig

/-- If `a, b > 0` and `|a - b| ≤ c ≤ b/2`, then `|log a - log b| ≤ 2 c / b`. -/
theorem abs_log_sub_log_le {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (h : |a - b| ≤ c) (hcb : c ≤ b / 2) :
    |Real.log a - Real.log b| ≤ 2 * c * b⁻¹ := by
  have hbinv : (0:ℝ) ≤ b⁻¹ := inv_nonneg.mpr hb.le
  have hb2pos : (0:ℝ) < b / 2 := by linarith
  -- `|a - b| ≤ c ≤ b/2` forces `b/2 ≤ a`
  have hba : b / 2 ≤ a := by
    have h1 : b - a ≤ c := by
      have := neg_le_abs (a - b); linarith
    linarith
  rcases lt_or_ge a b with hlt | hle
  · -- case `a < b`
    have habs : |a - b| = b - a := by simpa using abs_of_neg (sub_neg.mpr hlt)
    have h1 : b - a ≤ c := by rw [← habs]; exact h
    have hmono : Real.log a ≤ Real.log b := Real.log_le_log ha hlt.le
    have habslog : |Real.log a - Real.log b| = Real.log b - Real.log a := by
      rw [abs_of_nonpos (sub_nonpos.mpr hmono)]; ring
    rw [habslog]
    have hdiv : Real.log b - Real.log a = Real.log (b / a) := by
      rw [Real.log_div hb.ne' ha.ne']
    rw [hdiv]
    have h2 : Real.log (b / a) ≤ b / a - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h3 : b / a - 1 = (b - a) * a⁻¹ := by
      rw [div_eq_mul_inv, sub_mul, mul_inv_cancel₀ ha.ne']
    have h4 : (b - a) * a⁻¹ ≤ 2 * c * b⁻¹ := by
      have h5 : a⁻¹ ≤ (b / 2)⁻¹ := inv_anti₀ hb2pos hba
      have h6 : (b - a) * a⁻¹ ≤ (b - a) * (b / 2)⁻¹ :=
        mul_le_mul_of_nonneg_left h5 (sub_nonneg.mpr hlt.le)
      have h7 : (b - a) * (b / 2)⁻¹ = 2 * (b - a) * b⁻¹ := by
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring
      have h8 : 2 * (b - a) * b⁻¹ ≤ 2 * c * b⁻¹ := by
        nlinarith [h1, inv_pos.mpr hb]
      linarith
    linarith
  · -- case `b ≤ a`
    have habs : |a - b| = a - b := abs_of_nonneg (sub_nonneg.mpr hle)
    have h1 : a - b ≤ c := by rw [← habs]; exact h
    have hmono : Real.log b ≤ Real.log a := Real.log_le_log hb hle
    have habslog : |Real.log a - Real.log b| = Real.log a - Real.log b :=
      abs_of_nonneg (sub_nonneg.mpr hmono)
    rw [habslog]
    have hdiv : Real.log a - Real.log b = Real.log (a / b) := by
      rw [Real.log_div ha.ne' hb.ne']
    rw [hdiv]
    have h2 : Real.log (a / b) ≤ a / b - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h3 : a / b - 1 = (a - b) * b⁻¹ := by
      rw [div_eq_mul_inv, sub_mul, mul_inv_cancel₀ hb.ne']
    have h4 : (a - b) * b⁻¹ ≤ 2 * c * b⁻¹ := by
      have h5 : (a - b) * b⁻¹ ≤ c * b⁻¹ := mul_le_mul_of_nonneg_right h1 hbinv
      have h6 : (0:ℝ) ≤ c * b⁻¹ := mul_nonneg hc hbinv
      linarith
    linarith

end Work.TMC16Core.Trig
