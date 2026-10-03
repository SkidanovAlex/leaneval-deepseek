import Mathlib
import Submission.Work.FIArea4.SqfreeKernel

namespace Work.FIArea4

/-- The Jacobi symbol `J(n | m)` agrees with `J(n | sqfreeKernel m)` when `n` is coprime to `m`.
Route: from `Work.FIArea4.sqfree_kernel` (file `Submission/Work/FIArea4/sqfree_kernel.lean`)
we have `m = sqfreeKernel m * (sqPart m)^2`; then `jacobiSym.mul_right` and
`jacobiSym.pow_right` give `J(n|m) = J(n|sqfreeKernel m) * J(n|sqPart m)^2`, and
`jacobiSym.sq_one` applied to `J(n | sqPart m)` (using `sqPart m ∣ m` and `n.gcd m = 1`)
kills the square factor. Handle `m = 0` separately (there `n = 1` and both sides are `1`). -/
theorem jacobiSym_sqfreeKernel_of_coprime {m n : ℕ} (h : n.gcd m = 1) :
    jacobiSym (n : ℤ) m = jacobiSym (n : ℤ) (Work.FIArea4.sqfreeKernel m) := by
  rcases eq_or_ne m 0 with rfl | hm
  · -- `m = 0`: coprimality forces `n = 1`, and both sides are `1`.
    have hn : n = 1 := by simpa using h
    subst hn
    simp [Work.FIArea4.sqfreeKernel, Work.FIArea4.sqPart]
  · -- `m ≠ 0`: `sqPart m` is the largest `t` with `t^2 ∣ m`, so `(sqPart m)^2 ∣ m`
    -- and hence `m = sqfreeKernel m * (sqPart m)^2`.
    have hdvd : sqPart m ^ 2 ∣ m := by
      have hspec := Nat.findGreatest_spec (P := fun t => t ^ 2 ∣ m)
        (n := Nat.sqrt m) (m := 1)
        (by rw [Nat.le_sqrt]; simpa using Nat.one_le_iff_ne_zero.mpr hm)
        (by simp)
      simpa [sqPart] using hspec
    have hk : sqfreeKernel m * sqPart m ^ 2 = m := by
      rw [sqfreeKernel, Nat.div_mul_cancel hdvd]
    have hk0 : sqfreeKernel m ≠ 0 := by
      rintro h0; rw [h0, zero_mul] at hk; exact hm hk.symm
    have hs0 : sqPart m ^ 2 ≠ 0 := by
      rintro h0; rw [h0, mul_zero] at hk; exact hm hk.symm
    -- `sqPart m ∣ m` and `n` coprime to `m` force `n` coprime to `sqPart m`.
    have hsp : sqPart m ∣ m := dvd_trans (dvd_mul_left _ _) hdvd
    have hcop : (n : ℤ).gcd (sqPart m : ℕ) = 1 := by
      rw [Int.gcd_natCast_natCast]
      exact Nat.Coprime.coprime_dvd_right hsp h
    calc jacobiSym (n : ℤ) m
        = jacobiSym (n : ℤ) (sqfreeKernel m * sqPart m ^ 2) := by rw [hk]
      _ = jacobiSym (n : ℤ) (sqfreeKernel m) := by
            rw [jacobiSym.mul_right' _ hk0 hs0, jacobiSym.pow_right, jacobiSym.sq_one hcop,
              mul_one]

end Work.FIArea4
