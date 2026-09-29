import Mathlib
import Submission.Work.Pure.b4_defs

namespace Work.Pure

open PowerSeries

/-- `b4P n` is divisible by `X ^ ⌈n/2⌉`; equivalently, all coefficients `m` with
`2 * m < n` vanish.

The recurrence `b4P (n+2) = X * b4P (n+1) - X * b4P n` multiplies by `X`, so the
vanishing threshold improves by exactly one at every step, and a strong induction
on `n` closes the statement. -/
theorem b4_PF_vanishing : ∀ n m : ℕ, 2 * m < n → PowerSeries.coeff m (Work.Pure.b4P n) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rintro m hm
    rcases n with _ | _ | k
    · omega
    · have hm0 : m = 0 := by omega
      subst hm0
      simp [Work.Pure.b4P_one]
    · rw [Work.Pure.b4P_succ_succ]
      rcases m with _ | m'
      · simp only [map_sub, PowerSeries.coeff_zero_X_mul, sub_zero]
      · rw [map_sub, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
        rw [ih (k + 1) (by omega) m' (by omega), ih k (by omega) m' (by omega), sub_zero]

end Work.Pure
