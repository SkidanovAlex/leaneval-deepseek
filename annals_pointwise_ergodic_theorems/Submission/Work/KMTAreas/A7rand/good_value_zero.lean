import Mathlib

namespace Work.KMTAreas.A7rand

theorem good_value_zero (η : ℝ → ℂ) (hηone : ∀ y : ℝ, |y| ≤ 1 / 2 → η y = 1)
    (hηzero : ∀ y : ℝ, 1 ≤ |y| → η y = 0)
    (s : ℕ → ℕ) (hs : Monotone s) (m : ℕ) (ξ : ℝ)
    (hgood : ¬ (s (m + 1) > s m ∧ (2 : ℝ) ^ (s m) * |ξ| ≤ 1 ∧
      (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (m + 1)) * |ξ|)) :
    η ((2 : ℝ) ^ (s m) * ξ) - η ((2 : ℝ) ^ (s (m + 1)) * ξ) = 0 := by
  have hApos : (0 : ℝ) < (2 : ℝ) ^ (s m) := by positivity
  have hBpos : (0 : ℝ) < (2 : ℝ) ^ (s (m + 1)) := by positivity
  have hξnn : (0 : ℝ) ≤ |ξ| := abs_nonneg ξ
  have hAB : (2 : ℝ) ^ (s m) ≤ (2 : ℝ) ^ (s (m + 1)) :=
    pow_le_pow_right₀ (by norm_num) (hs (Nat.le_succ m))
  have hstep : (2 : ℝ) ^ (s m) * |ξ| ≤ (2 : ℝ) ^ (s (m + 1)) * |ξ| :=
    mul_le_mul_of_nonneg_right hAB hξnn
  have hAabs : |(2 : ℝ) ^ (s m) * ξ| = (2 : ℝ) ^ (s m) * |ξ| := by
    rw [abs_mul, abs_of_pos hApos]
  have hBabs : |(2 : ℝ) ^ (s (m + 1)) * ξ| = (2 : ℝ) ^ (s (m + 1)) * |ξ| := by
    rw [abs_mul, abs_of_pos hBpos]
  rw [sub_eq_zero]
  by_cases hsm : s m < s (m + 1)
  · have hlt : (2 : ℝ) ^ (s m) < (2 : ℝ) ^ (s (m + 1)) :=
      pow_lt_pow_right₀ (by norm_num) hsm
    by_cases hx : (2 : ℝ) ^ (s m) * |ξ| ≤ 1
    · by_cases hy : (1 : ℝ) / 2 ≤ (2 : ℝ) ^ (s (m + 1)) * |ξ|
      · exact absurd ⟨hsm, hx, hy⟩ hgood
      · push Not at hy
        have h1 : η ((2 : ℝ) ^ (s m) * ξ) = 1 := by
          apply hηone
          rw [hAabs]; linarith
        have h2 : η ((2 : ℝ) ^ (s (m + 1)) * ξ) = 1 := by
          apply hηone
          rw [hBabs]; linarith
        rw [h1, h2]
    · push Not at hx
      have h1 : η ((2 : ℝ) ^ (s m) * ξ) = 0 := by
        apply hηzero
        rw [hAabs]; linarith
      have h2 : η ((2 : ℝ) ^ (s (m + 1)) * ξ) = 0 := by
        apply hηzero
        rw [hBabs]; linarith
      rw [h1, h2]
  · have heq : s (m + 1) = s m := le_antisymm (not_lt.mp hsm) (hs (Nat.le_succ m))
    rw [heq]

end Work.KMTAreas.A7rand
