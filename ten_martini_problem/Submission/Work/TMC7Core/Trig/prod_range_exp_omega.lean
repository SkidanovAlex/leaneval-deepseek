import Mathlib
import Submission.Work.TMC7Core.Trig

namespace Work.TMC7Core.Trig

theorem prod_range_exp_omega (α x : ℝ) (n : ℕ) :
    (∏ j ∈ Finset.range n, (Complex.exp (2 * Real.pi * Complex.I * x) * (omega α) ^ j))
      = (Complex.exp (2 * Real.pi * Complex.I * x)) ^ n
        * (omega α) ^ (n * (n - 1) / 2) := by
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.sum_range_id]
  simp

end Work.TMC7Core.Trig
