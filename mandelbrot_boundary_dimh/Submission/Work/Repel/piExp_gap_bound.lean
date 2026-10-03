import Mathlib
import Submission.Work.Interfaces.Parabolic

namespace Work.Repel

/-- Auxiliary gap bound: for `δ ≤ 1/(16π)`, `4πδ‖c‖` is controlled by
`32πδ + 7‖c - 1‖`. -/
theorem piExp_gap_bound (c : ℂ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (16 * Real.pi)) :
    4 * Real.pi * δ * ‖c‖ ≤ 32 * Real.pi * δ + 7 * ‖c - 1‖ := by
  have hne : (16 * Real.pi) ≠ 0 := by positivity
  have h16 : 16 * Real.pi * δ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hδ (by positivity : (0 : ℝ) ≤ 16 * Real.pi)
    rw [mul_one_div, div_self hne] at h
    exact h
  have h4 : 4 * Real.pi * δ ≤ 7 := by nlinarith [h16, hδ0, Real.pi_pos]
  have h32 : 4 * Real.pi * δ ≤ 32 * Real.pi * δ := by nlinarith [hδ0, Real.pi_pos]
  have hA : 0 ≤ 4 * Real.pi * δ := by nlinarith [hδ0, Real.pi_pos]
  have hnorm : ‖c‖ ≤ ‖c - 1‖ + 1 := by
    have := norm_add_le (c - 1) 1
    simpa using this
  have hstep : 4 * Real.pi * δ * ‖c‖ ≤ 4 * Real.pi * δ * (‖c - 1‖ + 1) :=
    mul_le_mul_of_nonneg_left hnorm hA
  have h1 : 4 * Real.pi * δ * ‖c - 1‖ ≤ 7 * ‖c - 1‖ :=
    mul_le_mul_of_nonneg_right h4 (norm_nonneg (c - 1))
  have hsplit : 4 * Real.pi * δ * (‖c - 1‖ + 1)
      = 4 * Real.pi * δ * ‖c - 1‖ + 4 * Real.pi * δ := by ring
  linarith [hstep, h1, h32, hsplit]

end Work.Repel
