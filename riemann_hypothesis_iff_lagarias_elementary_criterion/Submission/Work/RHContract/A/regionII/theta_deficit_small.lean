import Mathlib
import Submission.Commons.NumberTheory.Chebyshev.theta_bracket_finite_range

/-!
# Certified brackets for `θ` on `[173, 501]`

`thUB m` and `thLB m` are the sums of the certified brackets `utOf`/`ltOf`
(`Submission.Commons.NumberTheory.Chebyshev.ThetaBracket`) over the primes `p ≤ m`; they
bound `10^9 · θ m` from above and below.
-/

set_option maxRecDepth 400000

namespace Work.RHContract.A.RegionII

open Commons.NumberTheory.Chebyshev.ThetaBracket

/-- Certified upper bound for `10^9 · θ m` (sum of the `utOf` brackets). -/
def thUB (m : ℕ) : ℕ := ∑ p ∈ Nat.primesLE m, utOf p

/-- Certified lower bound for `10^9 · θ m` (sum of the `ltOf` brackets). -/
def thLB (m : ℕ) : ℕ := ∑ p ∈ Nat.primesLE m, ltOf p

lemma theta_le_thUB (m : ℕ) : Chebyshev.theta (m : ℝ) ≤ (thUB m : ℝ) / 10 ^ 9 := by
  have h1 : Chebyshev.theta (m:ℝ) = ∑ p ∈ Nat.primesLE m, Real.log (p:ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE, Nat.floor_natCast]
  have h2 : (thUB m : ℝ) / 10^9 = ∑ p ∈ Nat.primesLE m, (utOf p : ℝ)/10^9 := by
    rw [thUB]; push_cast; rw [Finset.sum_div]
  rw [h1, h2]
  apply Finset.sum_le_sum
  intro p hp
  have hp2 : 2 ≤ p := (Nat.mem_primesLE.mp hp).2.two_le
  have h := log_le_utOf p hp2
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 10^9)]
  linarith

lemma thLB_div_le_theta (m : ℕ) : (thLB m : ℝ) / 10 ^ 9 ≤ Chebyshev.theta (m : ℝ) := by
  have h1 : Chebyshev.theta (m:ℝ) = ∑ p ∈ Nat.primesLE m, Real.log (p:ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE, Nat.floor_natCast]
  have h2 : (thLB m : ℝ) / 10^9 = ∑ p ∈ Nat.primesLE m, (ltOf p : ℝ)/10^9 := by
    rw [thLB]; push_cast; rw [Finset.sum_div]
  rw [h1, h2]
  apply Finset.sum_le_sum
  intro p hp
  have hp2 : 2 ≤ p := (Nat.mem_primesLE.mp hp).2.two_le
  have h := ltOf_le_log p hp2
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10^9)]
  linarith

end Work.RHContract.A.RegionII
