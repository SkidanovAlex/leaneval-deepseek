import Mathlib
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count_eq_sum_chi4

namespace Commons.NumberTheory.GaussianInt

/-- The number of representations of `n ≥ 1` as an ordered sum of two squares is at
most `4 * d(n)`, since it equals `4 * ∑_{d | n} χ₄(d)` and each term of that sum is
bounded by `1`. -/
theorem two_squares_repr_count_le_tau_of_pos (n : ℕ) (hn : 1 ≤ n) :
    ((Finset.filter (fun z : ℤ × ℤ => z.1 ^ 2 + z.2 ^ 2 = (n : ℤ))
        (Finset.Icc (-(n : ℤ)) (n : ℤ) ×ˢ Finset.Icc (-(n : ℤ)) (n : ℤ))).card : ℤ)
      ≤ 4 * ((Nat.divisors n).card : ℤ) := by
  rw [two_squares_repr_count_eq_sum_chi4 n hn]
  have hle : (∑ d ∈ n.divisors,
        (if d % 4 = 1 then (1 : ℤ) else if d % 4 = 3 then (-1 : ℤ) else 0))
      ≤ ((n.divisors).card : ℤ) := by
    have h1 : (∑ d ∈ n.divisors,
          (if d % 4 = 1 then (1 : ℤ) else if d % 4 = 3 then (-1 : ℤ) else 0))
        ≤ ∑ _d ∈ n.divisors, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs <;> norm_num
    have h2 : (∑ _d ∈ n.divisors, (1 : ℤ)) = ((n.divisors).card : ℤ) := by
      simp
    linarith
  linarith

end Commons.NumberTheory.GaussianInt
