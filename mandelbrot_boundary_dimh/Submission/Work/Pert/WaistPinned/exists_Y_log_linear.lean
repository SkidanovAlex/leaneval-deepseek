import Mathlib
import Submission.Work.Pert.Pin3.arith_lemmas

namespace Work.Pert.WaistPinned

/-- For `A ≥ 0` the logarithm term `32 A log (t+2)` is eventually dominated by `t/2 + 1`,
using `Work.Pert.Ksub2.exists_log_le_half`. -/
theorem log_shift_eventually_le (A : ℝ) (hA : 0 ≤ A) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ t : ℝ, Y ≤ t →
      32 * A * Real.log (t + 2) ≤ t / 2 + 1 := by
  obtain ⟨R₀, hR₀⟩ := Work.Pert.Ksub2.exists_log_le_half (32 * A)
  refine ⟨max R₀ 2 + 1, by have : (2:ℝ) ≤ max R₀ 2 := le_max_right _ _; linarith, ?_⟩
  intro t ht
  have hmax : max R₀ 2 ≤ t := by linarith
  have hR0t : R₀ ≤ t := le_trans (le_max_left _ _) hmax
  have hx : R₀ ≤ t + 2 := by linarith
  have h1 := hR₀ (t + 2) hx
  have h2 : 32 * A * Real.log (t + 2) ≤ 32 * A * (1 + Real.log (t + 2)) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith : (0:ℝ) ≤ 32 * A)
    linarith
  linarith [le_trans h2 h1]

theorem exists_Y_log_linear (A C R₁ R₂ ξ : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ t : ℝ, Y ≤ t →
      R₁ + R₂ + 7 + 16 * C + 16 * A * Real.log (t + 2) ≤ (t - (ξ + 2)) / 2 := by
  have _hC : (0:ℝ) ≤ C := hC
  obtain ⟨Y₀, hY₀pos, hY₀⟩ := log_shift_eventually_le A hA
  set K : ℝ := ξ + 2 + 2 * (R₁ + R₂ + 7 + 16 * C) with hK
  refine ⟨max Y₀ (2 * K + 2), ?_, ?_⟩
  · have h : (0:ℝ) < Y₀ := hY₀pos
    exact lt_of_lt_of_le h (le_max_left _ _)
  · intro t ht
    have hY₀t : Y₀ ≤ t := le_trans (le_max_left _ _) ht
    have hKt : 2 * K + 2 ≤ t := le_trans (le_max_right _ _) ht
    have hle := hY₀ t hY₀t
    have hmid : t / 2 + 1 ≤ t - K := by
      rw [hK] at hKt ⊢
      linarith
    have key : 32 * A * Real.log (t + 2) ≤ t - K := le_trans hle hmid
    rw [hK] at key
    nlinarith [key]

end Work.Pert.WaistPinned
