import Mathlib

namespace Work.NN.Newton.FTfibre

theorem holder_quot_le_nonneg {α : ℝ} (hα : 0 ≤ α) (i : ℕ) {N M P r d : ℝ}
    (hNM : N ≤ M * P ^ i) (hM : 0 ≤ M) (hP : 0 < P) (hr : 0 < r) (hd : 0 < d)
    (hle : d ≤ P * r) :
    N / r ^ α ≤ P ^ ((i : ℝ) + α) * (M / d ^ α) := by
  have hrpow : 0 < r ^ α := Real.rpow_pos_of_pos hr α
  have hdpow : 0 < d ^ α := Real.rpow_pos_of_pos hd α
  have hX : 0 ≤ M * P ^ i := mul_nonneg hM (pow_nonneg (le_of_lt hP) i)
  have hkey : 1 / r ^ α ≤ P ^ α / d ^ α := by
    rw [div_le_div_iff₀ hrpow hdpow]
    calc (1 : ℝ) * d ^ α = d ^ α := by ring
      _ ≤ (P * r) ^ α := Real.rpow_le_rpow (le_of_lt hd) hle hα
      _ = P ^ α * r ^ α := Real.mul_rpow (le_of_lt hP) (le_of_lt hr)
  have h2 : (M * P ^ i) / r ^ α ≤ M * P ^ i * (P ^ α / d ^ α) := by
    have h := mul_le_mul_of_nonneg_left hkey hX
    rw [mul_one_div] at h
    exact h
  have hPadd : P ^ ((i : ℝ) + α) = P ^ i * P ^ α := by
    rw [Real.rpow_add hP, Real.rpow_natCast]
  calc N / r ^ α ≤ (M * P ^ i) / r ^ α := div_le_div_of_nonneg_right hNM (le_of_lt hrpow)
    _ ≤ M * P ^ i * (P ^ α / d ^ α) := h2
    _ = P ^ ((i : ℝ) + α) * (M / d ^ α) := by
        rw [hPadd]; field_simp

end Work.NN.Newton.FTfibre
