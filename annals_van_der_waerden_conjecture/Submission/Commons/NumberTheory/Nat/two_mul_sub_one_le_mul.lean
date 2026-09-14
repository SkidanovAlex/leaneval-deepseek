import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.NumberTheory.Nat

theorem two_mul_sub_one_le_mul (n j : ℕ) (hn : 2 ≤ n) (hj2 : 2 ≤ j) (hjn : j ≤ n - 1) :
    (2 : ℝ) * ((n : ℝ) - 1) ≤ (j : ℝ) * ((n : ℝ) + 1 - (j : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have hj2' : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj2
  have hjn' : (j : ℝ) ≤ (n : ℝ) - 1 := by
    have h := Nat.cast_le (α := ℝ) |>.mpr hjn
    rwa [Nat.cast_sub hn1, Nat.cast_one] at h
  have key : 0 ≤ ((j : ℝ) - 2) * ((n : ℝ) - 1 - (j : ℝ)) := by
    apply mul_nonneg <;> linarith
  nlinarith [key]

end Commons.NumberTheory.Nat