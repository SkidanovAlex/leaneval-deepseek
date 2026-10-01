import Mathlib

namespace Work.LinnikAreas.JutilaPieces

theorem SumInvDivLogSq :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℕ, 1 ≤ A →
      (∑ q ∈ Finset.Icc 1 A,
          if 2 * q ≤ A then (1 / (q : ℝ)) / (Real.log ((A : ℝ) / (q : ℝ))) ^ 2 else 0) ≤ C := by sorry

end Work.LinnikAreas.JutilaPieces
