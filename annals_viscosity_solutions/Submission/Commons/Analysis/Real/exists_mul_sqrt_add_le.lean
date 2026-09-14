import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Real

theorem exists_mul_sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ a * Real.sqrt r + b * (r * Real.sqrt r) ≤ ε := by
  obtain ⟨t, ht_pos, ht_le_one, ht_le⟩ :
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ t ≤ ε / (a + b + 1) :=
    ⟨min 1 (ε / (a + b + 1)), lt_min one_pos (div_pos hε (by linarith)),
      min_le_left _ _, min_le_right _ _⟩
  have hden : 0 < a + b + 1 := by linarith
  refine ⟨t ^ 2, pow_pos ht_pos 2, ?_⟩
  have hsqrt : Real.sqrt (t ^ 2) = t := Real.sqrt_sq ht_pos.le
  rw [hsqrt]
  have hpow : t ^ 2 * t ≤ t := by nlinarith [ht_pos, ht_le_one, sq_nonneg t]
  have h1 : a * t + b * (t ^ 2 * t) ≤ (a + b) * t := by
    have hb' : b * (t ^ 2 * t) ≤ b * t := mul_le_mul_of_nonneg_left hpow hb
    nlinarith [hb']
  have h2 : (a + b) * t ≤ (a + b) * (ε / (a + b + 1)) :=
    mul_le_mul_of_nonneg_left ht_le (by linarith)
  have h3 : (a + b) * (ε / (a + b + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ hden]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ a + b) hε.le]
  linarith

end Commons.Analysis.Real