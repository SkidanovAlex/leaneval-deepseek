import Mathlib.Analysis.Real.Sqrt
import Submission.Commons.Analysis.ExpLog.harmonic_le_one_add_log

open scoped BigOperators

namespace Commons.Analysis.Real

/-- The head of the harmonic series is bounded by `1 + log X`. -/
theorem head_harmonic_le (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (n : ℝ)⁻¹) ≤ 1 + Real.log (X : ℝ) := by
  rcases Nat.eq_zero_or_pos X with hX | hX
  · subst hX; simp
  · have h1 : (∑ n ∈ Finset.Icc 1 X, (n : ℝ)⁻¹)
        = ∑ n ∈ Finset.Icc 1 X, (1 : ℝ) / (n : ℝ) :=
      Finset.sum_congr rfl (fun n _ => by rw [one_div])
    rw [h1]
    exact Commons.Analysis.ExpLog.harmonic_le_one_add_log X hX

end Commons.Analysis.Real