import Mathlib
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow

namespace Work.FIArea4

/-- The divisor bound `d(n) ≪_ε n^ε`: for every `ε > 0` the number of divisors of `n` is at
most a constant times `n ^ ε`.  (Available as `card_divisors_le_rpow` in the shared library,
without the harmless hypothesis `1 ≤ n`.) -/
theorem P13_tau_bound : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
    ((n.divisors.card : ℕ) : ℝ) ≤ C * (n : ℝ) ^ ε := by
  intro ε hε
  obtain ⟨C, hCpos, hC⟩ := Commons.NumberTheory.DivisorBound.card_divisors_le_rpow ε hε
  exact ⟨C, hCpos, fun n _ => hC n⟩

end Work.FIArea4
