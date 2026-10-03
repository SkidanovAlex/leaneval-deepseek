import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.Divisors

namespace Commons.NumberTheory.Divisors

theorem sum_chi4_divisors (n : ℕ) :
    (∑ d ∈ n.divisors, (if d % 4 = 1 then (1:ℤ) else if d % 4 = 3 then -1 else 0))
      = ((n.divisors.filter (fun d => d % 4 = 1)).card : ℤ)
        - ((n.divisors.filter (fun d => d % 4 = 3)).card : ℤ) := by
  have key : ∀ d : ℕ, (if d % 4 = 1 then (1:ℤ) else if d % 4 = 3 then -1 else 0)
      = (if d % 4 = 1 then (1:ℤ) else 0) - (if d % 4 = 3 then (1:ℤ) else 0) := by
    intro d
    by_cases h1 : d % 4 = 1
    · simp [h1]
    · by_cases h3 : d % 4 = 3
      · simp [h3]
      · simp [h3]
  rw [Finset.natCast_card_filter (fun d => d % 4 = 1) n.divisors,
    Finset.natCast_card_filter (fun d => d % 4 = 3) n.divisors]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun d _ => key d)

end Commons.NumberTheory.Divisors