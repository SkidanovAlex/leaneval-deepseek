import Mathlib
import Submission.Commons.NumberTheory.Chebyshev.theta_le_log3_mul
import Submission.Commons.NumberTheory.Chebyshev.lcmUpto_le_three_pow

namespace Commons.NumberTheory.Chebyshev

/-- The Chebyshev `θ` function agrees with its value at the floor. -/
lemma theta_eq_theta_floor (x : ℝ) :
    Chebyshev.theta x = Chebyshev.theta ((⌊x⌋₊ : ℕ) : ℝ) := by
  rw [Chebyshev.theta_eq_sum_primesLE x,
    Chebyshev.theta_eq_sum_primesLE ((⌊x⌋₊ : ℕ) : ℝ), Nat.floor_natCast]

theorem theta_upper_11056 : ∀ x : ℝ, 1530 ≤ x → Chebyshev.theta x ≤ (11056 / 10000) * x := by
  intro x hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have h73 : Real.log 3 ≤ (11056 : ℝ) / 10000 := by linarith [log3_le_num]
  rw [theta_eq_theta_floor x]
  have hn : (0 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hxle : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
  calc
    Chebyshev.theta ((⌊x⌋₊ : ℕ) : ℝ) ≤ Real.log 3 * ((⌊x⌋₊ : ℕ) : ℝ) :=
        theta_le_log3_mul _
    _ ≤ (11056 / 10000) * ((⌊x⌋₊ : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right h73 hn
    _ ≤ (11056 / 10000) * x :=
        mul_le_mul_of_nonneg_left hxle (by norm_num)

end Commons.NumberTheory.Chebyshev
