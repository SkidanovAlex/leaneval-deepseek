import Mathlib

namespace Work.Pert

/-- Two elementary cross-multiplied inequalities in `η ≥ 100`, `δu ≥ 0`. -/
theorem dev_arith_rad_cross_a {η δu : ℝ} (hη : 100 ≤ η) (hδu : 0 ≤ δu) :
    ((1 / 10000 + (32 / 31) * (12 / η + 3 / 2 * δu)) * (13 * η / 40)
        ≤ (3 / 2 * δu + 1 / 3000) * η + 20) ∧
    ((1 / 10000 + (32 / 31) * (12 / η + 3 / 2 * δu)) * (3 * η)
        ≤ (5 * δu + 1 / 1000) * η + 100) := by
  have hηpos : (0 : ℝ) < η := by linarith
  have hηne : η ≠ 0 := ne_of_gt hηpos
  have hδη : (0 : ℝ) ≤ δu * η := mul_nonneg hδu (le_of_lt hηpos)
  constructor
  · field_simp
    nlinarith [hη, hδu, hδη]
  · field_simp
    nlinarith [hη, hδu, hδη]

end Work.Pert
