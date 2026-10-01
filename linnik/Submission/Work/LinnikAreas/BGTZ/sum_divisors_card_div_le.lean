import Mathlib
import Submission.Work.LinnikAreas.sum_card_divisors_div_le
import Submission.Work.LinnikAreas.harmonic_sum_le_one_add_log

namespace Work.LinnikAreas.BGTZ

/-- The classical hyperbola/Harmonic bound for the divisor function:
`∑_{n ≤ N} d(n)/n ≤ (1 + log N)^2`.

The two ingredients are the hyperbola bound
`∑_{n ≤ N} d(n)/n ≤ (∑_{m ≤ N} 1/m)^2` (obtained by double counting the pairs `(a,b)` with
`a*b ≤ N`) and the elementary harmonic bound `∑_{m ≤ N} 1/m ≤ 1 + log N`. -/
theorem sum_divisors_card_div_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ) / (n : ℝ)) ≤ (1 + Real.log N) ^ 2 := by
  calc (∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ) / (n : ℝ))
      ≤ (∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / (m : ℝ)) ^ 2 :=
        Work.LinnikAreas.sum_card_divisors_div_le N
    _ ≤ (1 + Real.log (N : ℝ)) ^ 2 := by
        have hH := Work.LinnikAreas.harmonic_sum_le_one_add_log N
        have hH0 : (0 : ℝ) ≤ ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / (m : ℝ) := by positivity
        exact pow_le_pow_left₀ hH0 hH 2

end Work.LinnikAreas.BGTZ
