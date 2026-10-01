import Mathlib

namespace Work.LinnikAreas.JutilaPieces

theorem SumInvPowLogExpDecay (c : ℝ) (hc : 0 < c) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℕ, 1 ≤ A →
      (∑ q ∈ Finset.Icc 1 A,
          (1 / (q : ℝ)) * (Real.log ((A : ℝ) / (q : ℝ)) + 2) ^ k *
            Real.exp (-(c * Real.sqrt (Real.log ((A : ℝ) / (q : ℝ)))))) ≤ C := by sorry

end Work.LinnikAreas.JutilaPieces
