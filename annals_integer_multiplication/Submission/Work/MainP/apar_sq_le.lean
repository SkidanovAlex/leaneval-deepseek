import Mathlib
import Submission.Work.MainP.basic

namespace Work.MainP

/-- `isqrt (12·D²·b) ≤ 5990·(isqrt b + 1)`.

From `b ≤ (isqrt b + 1)²` (`Nat.lt_succ_sqrt`) and the numerical fact
`12·D² = 12·1729² = 35873292 ≤ 35880100 = 5990²`, multiplying gives
`12·D²·b ≤ (5990·(isqrt b + 1))²`, and `Nat.sqrt_lt'` yields the claim. -/
theorem sqrt_12D2_le (b : ℕ) :
    Nat.sqrt (12 * HvdH.D ^ 2 * b) ≤ 5990 * (Nat.sqrt b + 1) := by
  have hD : 12 * HvdH.D ^ 2 ≤ 5990 ^ 2 := by norm_num [HvdH.D]
  have h1 : b ≤ (Nat.sqrt b + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt b
    nlinarith
  have h2 : 12 * HvdH.D ^ 2 * b ≤ 12 * HvdH.D ^ 2 * (Nat.sqrt b + 1) ^ 2 :=
    Nat.mul_le_mul_left _ h1
  have h3 : 12 * HvdH.D ^ 2 * (Nat.sqrt b + 1) ^ 2 ≤ 5990 ^ 2 * (Nat.sqrt b + 1) ^ 2 :=
    Nat.mul_le_mul_right _ hD
  have h4 : (5990 ^ 2 * (Nat.sqrt b + 1) ^ 2 : ℕ) = (5990 * (Nat.sqrt b + 1)) ^ 2 := by ring
  have hmain : 12 * HvdH.D ^ 2 * b ≤ (5990 * (Nat.sqrt b + 1)) ^ 2 := by
    rw [← h4]
    exact h2.trans h3
  rw [← Nat.lt_succ_iff, Nat.sqrt_lt']
  exact lt_of_le_of_lt hmain (Nat.pow_lt_pow_left (Nat.lt_succ_self _) (by norm_num))

/-- Upper bound on `α²` behind `AparFacts`: for `b ≥ 2^61`, with `m = isqrt (12D²b - 1)` and
`α = isqrt m + 1` (with `HvdH.D = 1729`), one has `α² ≤ 17970·(b/2^30 + 1) + 1`.
Chain: `α² ≤ 3m + 1` (as `isqrt m ≤ m`), `m ≤ isqrt(12D²b) ≤ 5990(isqrt b + 1)`, and
`isqrt b ≤ b/2^30` (`Work.MainP.sqrt_le_div`). Namespace `Work.MainP`, importing `Submission.Work.MainP.basic`. -/
theorem apar_sq_le (b : ℕ) (hb : 2 ^ 61 ≤ b) :
    (Nat.sqrt (Nat.sqrt (12 * HvdH.D ^ 2 * b - 1)) + 1) ^ 2 ≤ 17970 * (b / 2 ^ 30 + 1) + 1 := by
  have hstep1 : (Nat.sqrt (Nat.sqrt (12 * HvdH.D ^ 2 * b - 1)) + 1) ^ 2 ≤
      3 * Nat.sqrt (12 * HvdH.D ^ 2 * b - 1) + 1 := by
    nlinarith [Nat.sqrt_le' (Nat.sqrt (12 * HvdH.D ^ 2 * b - 1)),
      Nat.sqrt_le_self (Nat.sqrt (12 * HvdH.D ^ 2 * b - 1))]
  have hmM : Nat.sqrt (12 * HvdH.D ^ 2 * b - 1) ≤ Nat.sqrt (12 * HvdH.D ^ 2 * b) :=
    Nat.sqrt_le_sqrt (Nat.sub_le _ _)
  have hstep3 : 3 * Nat.sqrt (12 * HvdH.D ^ 2 * b) + 1 ≤ 17970 * (Nat.sqrt b + 1) + 1 := by
    nlinarith [sqrt_12D2_le b]
  have hstep4 : 17970 * (Nat.sqrt b + 1) + 1 ≤ 17970 * (b / 2 ^ 30 + 1) + 1 := by
    have := Work.MainP.sqrt_le_div b hb
    nlinarith
  calc (Nat.sqrt (Nat.sqrt (12 * HvdH.D ^ 2 * b - 1)) + 1) ^ 2
      ≤ 3 * Nat.sqrt (12 * HvdH.D ^ 2 * b - 1) + 1 := hstep1
    _ ≤ 3 * Nat.sqrt (12 * HvdH.D ^ 2 * b) + 1 := by omega
    _ ≤ 17970 * (Nat.sqrt b + 1) + 1 := hstep3
    _ ≤ 17970 * (b / 2 ^ 30 + 1) + 1 := hstep4

end Work.MainP
