import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Real

theorem sqrt_eta_properties {M : ℝ} (hM : 4 ≤ M) :
    (1 / (8 * Real.sqrt M)) ^ 4 = 1 / (4096 * M ^ 2)
    ∧ 1 / (8 * Real.sqrt M) ≤ 1 / 16
    ∧ 8 * (M - 1) * (1 / (8 * Real.sqrt M)) ^ 2 ≤ 1 - 2 / M := by
  have hM0 : (0:ℝ) < M := by linarith
  have hsq : Real.sqrt M ^ 2 = M := Real.sq_sqrt (le_of_lt hM0)
  have hsnn : (0:ℝ) ≤ Real.sqrt M := Real.sqrt_nonneg M
  have hs2 : (2:ℝ) ≤ Real.sqrt M := by nlinarith [hsq, hsnn]
  refine ⟨?_, ?_, ?_⟩
  · have h4 : Real.sqrt M ^ 4 = M ^ 2 := by
      rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, hsq]
    rw [div_pow, one_pow, mul_pow, h4]
    norm_num
  · have h16 : (16:ℝ) ≤ 8 * Real.sqrt M := by linarith
    exact one_div_le_one_div_of_le (by norm_num) h16
  · have h2 : (1 / (8 * Real.sqrt M)) ^ 2 = 1 / (64 * M) := by
      rw [div_pow, one_pow, mul_pow, hsq]; norm_num
    have hL : 8 * (M - 1) * (1 / (64 * M)) = (M - 1) / (8 * M) := by
      field_simp; ring
    have h8 : 1 - 2 / M = (M - 2) / M := by field_simp
    have hpos : (0:ℝ) < 8 * M := by positivity
    rw [h2, hL, h8]
    rw [div_le_iff₀ hpos]
    have hm : (M - 2) / M * (8 * M) = 8 * (M - 2) := by field_simp
    rw [hm]
    nlinarith

end Commons.Analysis.Real