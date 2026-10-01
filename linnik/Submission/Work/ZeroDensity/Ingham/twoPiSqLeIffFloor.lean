import Mathlib

namespace Work.ZeroDensity.Ingham

theorem twoPiSqLeIffFloor (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    2 * Real.pi * ((n : ℝ) - 1) ^ 2 ≤ t ↔ n ≤ ⌊Real.sqrt (t / (2 * Real.pi))⌋₊ + 1 := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  have hdiv : 0 ≤ t / (2 * Real.pi) := div_nonneg ht (le_of_lt h2pi)
  have hnat : n ≤ ⌊Real.sqrt (t / (2 * Real.pi))⌋₊ + 1 ↔
      (n - 1 : ℕ) ≤ ⌊Real.sqrt (t / (2 * Real.pi))⌋₊ := by omega
  have hfloor : (n - 1 : ℕ) ≤ ⌊Real.sqrt (t / (2 * Real.pi))⌋₊ ↔
      ((n - 1 : ℕ) : ℝ) ≤ Real.sqrt (t / (2 * Real.pi)) :=
    Nat.le_floor_iff (Real.sqrt_nonneg _)
  have hreal : ((n - 1 : ℕ) : ℝ) ≤ Real.sqrt (t / (2 * Real.pi)) ↔
      2 * Real.pi * (((n - 1 : ℕ) : ℝ)) ^ 2 ≤ t := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) hdiv, le_div_iff₀ h2pi,
        mul_comm ((((n - 1 : ℕ) : ℝ)) ^ 2) (2 * Real.pi)]
  have heq : (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn]; simp
  rw [hnat, hfloor, hreal, heq]

end Work.ZeroDensity.Ingham
