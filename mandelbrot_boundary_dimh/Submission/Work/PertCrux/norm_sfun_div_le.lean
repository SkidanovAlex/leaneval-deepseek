import Mathlib

namespace Work.PertCrux

theorem norm_sfun_div_le {σ ut t α : ℂ} {η : ℝ}
    (hη : η ≤ 1 / 1000) (hσ : ‖σ‖ ≤ 8 * Real.pi * ‖α‖) (hut : ‖ut‖ ≤ 3 / 2 + η)
    (ht : ‖t‖ ≤ 1 / 16) :
    ‖σ * ut / (1 + t * ut)‖ ≤ 60 * ‖α‖ := by
  have hα : (0 : ℝ) ≤ ‖α‖ := norm_nonneg α
  -- Bound ‖ut‖ by 1501/1000
  have hu : ‖ut‖ ≤ 1501 / 1000 := by linarith
  -- Bound ‖t * ut‖
  have htu : ‖t * ut‖ ≤ 1501 / 16000 := by
    rw [norm_mul]
    calc ‖t‖ * ‖ut‖ ≤ (1 / 16) * (1501 / 1000) :=
          mul_le_mul ht hu (norm_nonneg ut) (by norm_num)
      _ = 1501 / 16000 := by norm_num
  -- Lower bound on the denominator
  have hden : (14499 / 16000 : ℝ) ≤ ‖1 + t * ut‖ := by
    have h := norm_add_le (1 + t * ut) (-(t * ut))
    have hsum : (1 + t * ut) + -(t * ut) = (1 : ℂ) := by ring
    rw [hsum, norm_one, norm_neg] at h
    linarith
  have hdenpos : (0 : ℝ) < ‖1 + t * ut‖ := by linarith
  -- Bound ‖σ‖ using π < 4
  have hs : ‖σ‖ ≤ 32 * ‖α‖ := by
    calc ‖σ‖ ≤ 8 * Real.pi * ‖α‖ := hσ
      _ ≤ 8 * 4 * ‖α‖ := by
            apply mul_le_mul_of_nonneg_right _ hα
            linarith [Real.pi_lt_four]
      _ = 32 * ‖α‖ := by norm_num
  rw [norm_div, norm_mul]
  rw [div_le_iff₀ hdenpos]
  calc ‖σ‖ * ‖ut‖ ≤ (32 * ‖α‖) * (1501 / 1000) :=
        mul_le_mul hs hu (norm_nonneg ut) (by positivity)
    _ ≤ 60 * ‖α‖ * (14499 / 16000) := by nlinarith
    _ ≤ 60 * ‖α‖ * ‖1 + t * ut‖ :=
        mul_le_mul_of_nonneg_left hden (by positivity)

end Work.PertCrux
