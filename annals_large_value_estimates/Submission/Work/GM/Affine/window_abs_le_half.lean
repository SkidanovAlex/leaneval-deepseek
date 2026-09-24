import Mathlib

namespace Work.GM.Affine

theorem window_abs_le_half {δ a T M₃ y : ℝ} (hδ : 0 < δ) (ha : 1 ≤ a) (hT : 4 * a + 4 ≤ T)
    (hM₃ : T ^ 4 ≤ M₃)
    (hy : |y| ≤ a ^ (min δ 1 / 2) * T ^ (min δ 1 / 2) / M₃) : |y| ≤ 1 / 2 := by
  set e : ℝ := min δ 1 / 2 with he
  have he_pos : 0 < e := by rw [he]; positivity
  have he_le : 2 * e ≤ 1 := by
    rw [he]
    have h : min δ 1 ≤ 1 := min_le_right _ _
    linarith
  have hTpos : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hapos : 0 < a := by linarith
  have haT : a ≤ T := by linarith
  have step1 : a ^ e * T ^ e ≤ T := by
    have h1 : a ^ e * T ^ e ≤ T ^ e * T ^ e :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hapos.le haT he_pos.le)
        (Real.rpow_pos_of_pos hTpos e).le
    have h2 : T ^ e * T ^ e = T ^ (2 * e) := by
      rw [← Real.rpow_add hTpos]
      congr 1
      ring
    rw [h2] at h1
    have h3 : T ^ (2 * e) ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 he_le
    rw [Real.rpow_one] at h3
    linarith
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le (by positivity : (0 : ℝ) < T ^ 4) hM₃
  have hT4pos : (0 : ℝ) < T ^ 4 := by positivity
  have h4ge : 2 * T ≤ T ^ 4 := by
    have hT3 : (2 : ℝ) ≤ T ^ 3 := by
      have h : (2 : ℝ) ^ 3 ≤ T ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith : (2 : ℝ) ≤ T) 3
      linarith
    nlinarith [hT3, hTpos]
  have hhalf : T / T ^ 4 ≤ 1 / 2 := by
    rw [div_le_iff₀ hT4pos]
    linarith
  have hstep2 : a ^ e * T ^ e / M₃ ≤ T / M₃ := div_le_div_of_nonneg_right step1 hM₃pos.le
  have hstep3 : T / M₃ ≤ T / T ^ 4 := div_le_div_of_nonneg_left hTpos.le hT4pos hM₃
  linarith [hy, hstep2, hstep3, hhalf]

end Work.GM.Affine
