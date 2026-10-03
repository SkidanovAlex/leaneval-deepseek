import Mathlib
import Submission.Work.FIArea7.NCBasic

namespace Work.FIArea7

/-- Since `0 < δ₁ < 3/32`, both exponents `3δ₁/8` and `1 - δ₁/4` are positive, so each of
`(log (N+2))^23 · log N` and `(log (N+2))^3 · (log N)^2` is eventually dominated by the
corresponding power of `N`. -/
theorem nc_log_threshold (δ₁ : ℝ) (hδ0 : 0 < δ₁) (hδ32 : δ₁ < 3 / 32) :
    ∃ N₀ : ℝ, 5 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      (Real.log (N + 2)) ^ 23 * Real.log N ≤ N ^ (3 * δ₁ / 8) ∧
      (Real.log (N + 2)) ^ 3 * (Real.log N) ^ 2 ≤ N ^ (1 - δ₁ / 4) := by
  have hs : (0 : ℝ) < 3 * δ₁ / 8 / 2 := by linarith
  have ht : (0 : ℝ) < (1 - δ₁ / 4) / 2 := by linarith
  obtain ⟨N₁, _, h₁⟩ := exists_log_pow_le_rpow 24 (ε := 3 * δ₁ / 8 / 2) hs
  obtain ⟨N₂, _, h₂⟩ := exists_log_pow_le_rpow 3 (ε := (1 - δ₁ / 4) / 2) ht
  refine ⟨max (max N₁ N₂) 5, le_max_right _ _, ?_⟩
  intro N hN
  have hNN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ 5)) hN
  have hNN₂ : N₂ ≤ N := le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ 5)) hN
  have hN5 : (5 : ℝ) ≤ N := le_trans (le_max_right (max N₁ N₂) 5) hN
  have hN3 : (3 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hlogN1 : 1 ≤ Real.log N := one_le_log_of_three_le hN3
  have hlogN2 : 1 ≤ Real.log (N + 2) := one_le_log_of_three_le (by linarith)
  have hlogN0 : 0 ≤ Real.log N := by linarith
  obtain ⟨h₁a, h₁b⟩ := h₁ N hNN₁
  obtain ⟨h₂a, h₂b⟩ := h₂ N hNN₂
  constructor
  · have hA : (Real.log (N + 2)) ^ 23 ≤ N ^ (3 * δ₁ / 8 / 2) :=
      le_trans (pow_le_pow_right₀ hlogN2 (by norm_num)) h₁b
    have hB : Real.log N ≤ N ^ (3 * δ₁ / 8 / 2) := by
      have hle : Real.log N ≤ (Real.log N) ^ 24 := by
        simpa using pow_le_pow_right₀ hlogN1 (by norm_num : (1 : ℕ) ≤ 24)
      exact le_trans hle h₁a
    calc (Real.log (N + 2)) ^ 23 * Real.log N
        ≤ N ^ (3 * δ₁ / 8 / 2) * N ^ (3 * δ₁ / 8 / 2) :=
          mul_le_mul hA hB hlogN0 (Real.rpow_nonneg hNpos.le _)
      _ = N ^ (3 * δ₁ / 8) := by
          rw [← Real.rpow_add hNpos]; congr 1; ring
  · have hA : (Real.log (N + 2)) ^ 3 ≤ N ^ ((1 - δ₁ / 4) / 2) := h₂b
    have hB : (Real.log N) ^ 2 ≤ N ^ ((1 - δ₁ / 4) / 2) := by
      have hle : (Real.log N) ^ 2 ≤ (Real.log N) ^ 3 :=
        pow_le_pow_right₀ hlogN1 (by norm_num : (2 : ℕ) ≤ 3)
      exact le_trans hle h₂a
    calc (Real.log (N + 2)) ^ 3 * (Real.log N) ^ 2
        ≤ N ^ ((1 - δ₁ / 4) / 2) * N ^ ((1 - δ₁ / 4) / 2) :=
          mul_le_mul hA hB (pow_nonneg hlogN0 2) (Real.rpow_nonneg hNpos.le _)
      _ = N ^ (1 - δ₁ / 4) := by
          rw [← Real.rpow_add hNpos]; congr 1; ring

end Work.FIArea7
