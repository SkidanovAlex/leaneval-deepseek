import Mathlib
import Submission.Work.MainP.basic

namespace Work.MainP

/-- `√(12 · D² · b) ≤ 5990 · (√b + 1)` for `D = 1729` and every `b` (in namespace `Work.MainP`,
importing `Submission.Work.MainP.basic`). This is the numerical input `isqrt(12D²b) ≤ 5990(isqrt b + 1)`
of the `MainP` area: from `b ≤ (√b+1)²` and the constant inequality `12·1729² ≤ 5990²`. -/
theorem sqrt_twelve_mul (b : ℕ) :
    Nat.sqrt (12 * HvdH.D ^ 2 * b) ≤ 5990 * (Nat.sqrt b + 1) := by
  simp only [HvdH.D]
  rw [← Nat.lt_succ_iff]
  apply Nat.sqrt_lt'.mpr
  have hb : b < (Nat.sqrt b + 1) ^ 2 := by
    simpa [pow_two] using Nat.lt_succ_sqrt b
  nlinarith [Nat.zero_le b, Nat.zero_le (Nat.sqrt b)]

end Work.MainP
