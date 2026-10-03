import Mathlib
import Submission.Commons.Data.Nat.gcd_eq_sum_totient_divisors_ne_zero

namespace Work.FIArea3

/-- `gcd a c` is the sum of `φ d` over the divisors `d` of `a` which also divide `c`. -/
theorem gcd_cast_eq_sum_totient_ite (a c : ℕ) (ha : 1 ≤ a) :
    ((Nat.gcd a c : ℕ) : ℝ)
      = ∑ d ∈ a.divisors, (if d ∣ c then (Nat.totient d : ℝ) else 0) := by
  have ha0 : a ≠ 0 := by omega
  rw [Nat.gcd_comm a c]
  have h := Commons.Data.Nat.gcd_eq_sum_totient_divisors_ne_zero (c := c) (m := a) ha0
  rw [h, Nat.cast_sum, Finset.sum_filter]

end Work.FIArea3
