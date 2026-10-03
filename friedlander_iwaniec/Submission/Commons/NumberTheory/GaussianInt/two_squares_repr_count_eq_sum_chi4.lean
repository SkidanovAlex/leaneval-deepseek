import Mathlib
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count
import Submission.Commons.NumberTheory.Divisors.sum_chi4_divisors

namespace Commons.NumberTheory.GaussianInt

open Finset

theorem two_squares_repr_count_eq_sum_chi4 (n : ℕ) (hn : 1 ≤ n) :
    ((Finset.filter (fun z : ℤ × ℤ => z.1 ^ 2 + z.2 ^ 2 = (n : ℤ))
      (Finset.Icc (-(n : ℤ)) (n : ℤ) ×ˢ Finset.Icc (-(n : ℤ)) (n : ℤ))).card : ℤ)
      = 4 * ∑ d ∈ n.divisors,
          (if d % 4 = 1 then (1 : ℤ) else if d % 4 = 3 then (-1 : ℤ) else 0) := by
  rw [Commons.NumberTheory.Divisors.sum_chi4_divisors n]
  have h : ((targetF n).card : ℤ)
      = 4 * ((n.divisors.filter (fun d => d % 4 = 1)).card : ℤ)
        - 4 * ((n.divisors.filter (fun d => d % 4 = 3)).card : ℤ) :=
    two_squares_repr_count n hn
  change ((targetF n).card : ℤ)
    = 4 * (((n.divisors.filter (fun d => d % 4 = 1)).card : ℤ)
      - ((n.divisors.filter (fun d => d % 4 = 3)).card : ℤ))
  rw [h]
  ring

end Commons.NumberTheory.GaussianInt
