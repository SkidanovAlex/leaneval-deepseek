import Mathlib

namespace Work.FIArea7

theorem pairExp172 {η ν δ : ℝ} (hδ : 0 ≤ δ) (hν : ν ≤ η / 12) :
    (1 - η) * (1 / 12) + 11 / 12 ≤ 1 - ν + 4 * δ := by
  have h : (1 - η) * (1 / 12) + 11 / 12 = 1 - η / 12 := by ring
  rw [h]
  linarith

end Work.FIArea7
