import Mathlib

namespace Work.GM.S2

theorem geom_two_sums (K : ℕ) :
    (∑ kk ∈ Finset.range K, ((1 : ℝ) / 2) ^ kk) ≤ 2 ∧
    (∑ kk ∈ Finset.range K, (2 : ℝ) ^ kk) ≤ 2 ^ K := by
  constructor
  · have hhalf : ((1 : ℝ) / 2) ≠ 1 := by norm_num
    rw [geom_sum_eq hhalf K]
    have hpos : (0 : ℝ) < ((1 : ℝ) / 2) ^ K := by positivity
    have hval : (((1 : ℝ) / 2) ^ K - 1) / ((1 : ℝ) / 2 - 1) = 2 - 2 * ((1 : ℝ) / 2) ^ K := by
      field_simp
      ring
    rw [hval]
    linarith
  · have h2 : (2 : ℝ) ≠ 1 := by norm_num
    rw [geom_sum_eq h2 K]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ K := by positivity
    have hval : ((2 : ℝ) ^ K - 1) / (2 - 1) = (2 : ℝ) ^ K - 1 := by ring
    rw [hval]
    linarith

end Work.GM.S2
