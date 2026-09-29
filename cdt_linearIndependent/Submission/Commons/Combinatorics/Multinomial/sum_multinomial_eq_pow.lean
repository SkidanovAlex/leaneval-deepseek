import Mathlib.Data.Real.Basic
import Submission.Commons.Algebra.BigOperators.sum_pow_eq_sum_multinomial

namespace Commons.Combinatorics.Multinomial

/-- The sum of all multinomial coefficients over the tuples of non-negative integers
summing to `t` equals `m ^ t`. -/
theorem sum_multinomial_eq_pow (m t : ℕ) :
    (∑ pv ∈ Fintype.piFinset (fun _ : Fin m => Finset.range (t + 1)),
        (if ∑ i, pv i = t then ((Nat.multinomial Finset.univ pv : ℕ) : ℝ) else 0))
      = (m : ℝ) ^ t := by
  rw [show (m : ℝ) = ∑ _ : Fin m, (1 : ℝ) by
        simp [Finset.sum_const]]
  rw [Commons.Algebra.BigOperators.sum_pow_eq_sum_multinomial (fun _ : Fin m => (1 : ℝ)) t]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h : ∑ i, p i = t <;> simp [h]

end Commons.Combinatorics.Multinomial