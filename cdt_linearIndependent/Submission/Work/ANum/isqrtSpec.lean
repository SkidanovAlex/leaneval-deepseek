import Submission.Work.ANum.isqrt_eq_sqrt

/-! # Derived specification of the kernel-reducible `isqrt`

`isqrt_eq_sqrt` (sibling module) gives `isqrt n = Nat.sqrt n` for every `n`; here we record the
`Nat.sqrt` specification lemmas under `isqrt` names, so that the interval library can use `isqrt`
while every existing proof about `Nat.sqrt` transfers verbatim. -/

namespace Work.ANum

theorem isqrt_le' (n : ℕ) : isqrt n ^ 2 ≤ n := by
  rw [isqrt_eq_sqrt]; exact Nat.sqrt_le' n

theorem lt_succ_isqrt' (n : ℕ) : n < (isqrt n + 1) ^ 2 := by
  rw [isqrt_eq_sqrt]; exact Nat.lt_succ_sqrt' n

theorem isqrt_le (n : ℕ) : isqrt n * isqrt n ≤ n := by
  rw [isqrt_eq_sqrt]; exact Nat.sqrt_le n

theorem lt_succ_isqrt (n : ℕ) : n < (isqrt n + 1) * (isqrt n + 1) := by
  rw [isqrt_eq_sqrt]; exact Nat.lt_succ_sqrt n


end Work.ANum
