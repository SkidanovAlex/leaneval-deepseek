import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Commons.NumberTheory.Linnik.tentWeight_spec

namespace Commons.NumberTheory.Linnik

theorem tentWeight_bounds {L K : ℝ} (hK : 0 ≤ K) (h2K : 2 * K ≤ L) :
    (∀ x : ℝ, 0 ≤ tentWeight L K x) ∧
    (∀ x : ℝ, tentWeight L K x ≤ K) ∧
    (∀ x : ℝ, x ≤ L - 2 * K → tentWeight L K x = 0) ∧
    (∀ x : ℝ, L ≤ x → tentWeight L K x = 0) := by
  constructor
  · intro x
    rw [tentWeight_spec]
    split_ifs <;> linarith
  constructor
  · intro x
    rw [tentWeight_spec]
    split_ifs <;> linarith
  constructor
  · intro x hx
    rw [tentWeight_spec]
    simp [hx]
  · intro x hx
    rw [tentWeight_spec]
    split_ifs <;> linarith

end Commons.NumberTheory.Linnik