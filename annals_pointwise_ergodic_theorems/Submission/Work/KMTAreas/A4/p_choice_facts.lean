import Mathlib

namespace Work.KMTAreas.A4

/-- Elementary facts about the quantity `1 + 1 / (4 * K + 2)` used to choose the
exponent `p` in the `A4` area: it lies in `(1, 2)`, and the expression
`(1 + K) / (1 + 1/(4K+2)) - K` equals `(3K+2)/(4K+3) ≥ 1/2` for `K ≥ 1`. -/
theorem p_choice_facts {K : ℝ} (hK : 1 ≤ K) : 1 < 1 + 1 / (4 * K + 2) ∧ 1 + 1 / (4 * K + 2) < 2 ∧ 1 / 2 ≤ (1 + K) / (1 + 1 / (4 * K + 2)) - K := by
  refine ⟨?_, ?_, ?_⟩
  · have h : (0 : ℝ) < 1 / (4 * K + 2) := by positivity
    linarith
  · have h : 1 / (4 * K + 2) < 1 := by
      rw [div_lt_one (by linarith : (0 : ℝ) < 4 * K + 2)]
      linarith
    linarith
  · have key : (1 + K) / (1 + 1 / (4 * K + 2)) - K = (3 * K + 2) / (4 * K + 3) := by
      have h1 : (1 : ℝ) + 1 / (4 * K + 2) ≠ 0 := by positivity
      field_simp
      ring
    rw [key, le_div_iff₀ (by linarith : (0 : ℝ) < 4 * K + 3)]
    linarith

end Work.KMTAreas.A4
