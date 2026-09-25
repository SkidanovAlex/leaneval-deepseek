import Mathlib
import Submission.Commons.NumberTheory.Chebyshev.theta_bracket_finite_range
import Submission.Commons.NumberTheory.Chebyshev.theta_upper_11056

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

open scoped BigOperators

namespace Work.RHContract.A

open Commons.NumberTheory.Chebyshev.ThetaBracket (utOf log_le_utOf)

/-- For `n ≤ 58` one has `θ n ≤ n`: the primes `≤ 58` are so few that the certified integer
upper bounds `utOf p ≥ 10^9 * log p` still fit below `10^9 * n`. -/
theorem theta_small_le_self (n : ℕ) (hn : n ≤ 58) : Chebyshev.theta (n : ℝ) ≤ (n : ℝ) := by
  have hchk : ∀ k ∈ List.range 59, ∑ p ∈ Nat.primesLE k, utOf p ≤ 10 ^ 9 * k := by decide
  have hnum := hchk n (List.mem_range.mpr (by omega))
  have hpos : (0 : ℝ) < 10 ^ 9 := by norm_num
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  have hmul : (10 ^ 9 : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log (p : ℝ)
      ≤ (10 ^ 9 : ℝ) * (n : ℝ) := by
    rw [Finset.mul_sum]
    calc ∑ p ∈ Nat.primesLE n, (10 ^ 9 : ℝ) * Real.log (p : ℝ)
        ≤ ∑ p ∈ Nat.primesLE n, (utOf p : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          exact log_le_utOf p (Nat.two_le_of_mem_primesLE hp)
      _ ≤ (10 ^ 9 : ℝ) * (n : ℝ) := by
          have hc : ((∑ p ∈ Nat.primesLE n, utOf p : ℕ) : ℝ) ≤ ((10 ^ 9 * n : ℕ) : ℝ) :=
            Nat.cast_le.mpr hnum
          push_cast at hc
          linarith [hc]
  by_contra hcon
  have hlt : (10 ^ 9 : ℝ) * (n : ℝ) < (10 ^ 9 : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log (p : ℝ) :=
    mul_lt_mul_of_pos_left (not_le.mp hcon) hpos
  linarith [hmul, hlt]

theorem theta_le_self_small (t : ℝ) (h1 : 2 ≤ t) (h2 : t ≤ 1530) :
    Chebyshev.theta t ≤ t := by
  rw [Commons.NumberTheory.Chebyshev.theta_eq_theta_floor t]
  have hfloor : ⌊t⌋₊ ≤ 1530 := Nat.floor_le_of_le h2
  have hle : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le (by linarith)
  rcases le_or_gt 59 ⌊t⌋₊ with h | h
  · have hb := (Commons.NumberTheory.Chebyshev.theta_bracket_finite_range ⌊t⌋₊ h (by omega)).2
    linarith
  · have hb := theta_small_le_self ⌊t⌋₊ (by omega)
    linarith

end Work.RHContract.A
