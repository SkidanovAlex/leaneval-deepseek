import Mathlib
import Submission.Work.FIArea2.TsumDefs
import Submission.Work.FIArea2.ramanujan_primepow
import Submission.Work.FIArea2.ram_primepow_exact

namespace Work.FIArea2

open scoped BigOperators

/-- **Value of the Ramanujan sum at a power of two.**
`Work.FIArea2.ram_primepow_exact` at the prime `2` gives
`ram (2^m) c = [(2^m) ∣ c]·2^m - [(2^(m-1)) ∣ c]·2^(m-1)`, which is the statement below once the
indicator is written as a multiplication by `1`/`0`. -/
theorem ram_two_pow_value (m : ℕ) (hm : 1 ≤ m) (c : ℤ) :
    ram (2 ^ m) c = (2 ^ m : ℂ) * (if ((2 ^ m : ℕ) : ℤ) ∣ c then 1 else 0)
      - (2 ^ (m - 1) : ℂ) * (if ((2 ^ (m - 1) : ℕ) : ℤ) ∣ c then 1 else 0) := by
  rw [ram_primepow_exact 2 m Nat.prime_two hm c]
  rw [mul_ite, mul_ite]
  simp only [mul_one, mul_zero]
  norm_num

end Work.FIArea2
