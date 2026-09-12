import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling

namespace Commons.Analysis.Real

/-- For every positive natural `k`, `(k / e)^k ≤ k!`.

This is the elementary half of Stirling's approximation. It follows from the global
Stirling lower bound `Stirling.le_factorial_stirling`, since `√(2πk) ≥ 1` for `k ≥ 1`. -/
lemma factorial_lower_exp {k : ℕ} (hk : 1 ≤ k) :
    ((k : ℝ) / Real.exp 1) ^ k ≤ (k.factorial : ℝ) := by
  have hst := Stirling.le_factorial_stirling k
  -- The Stirling factor is at least one: `1 ≤ √(2 * π * k)`.
  have hsq : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) := by
    rw [Real.one_le_sqrt]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith [Real.pi_gt_three]
  -- The power is nonnegative.
  have hnonneg : 0 ≤ ((k : ℝ) / Real.exp 1) ^ k := by positivity
  calc
    ((k : ℝ) / Real.exp 1) ^ k = 1 * ((k : ℝ) / Real.exp 1) ^ k := by
      rw [one_mul]
    _ ≤ (Real.sqrt (2 * Real.pi * (k : ℝ))) * ((k : ℝ) / Real.exp 1) ^ k := by
      exact mul_le_mul_of_nonneg_right hsq hnonneg
    _ ≤ (k.factorial : ℝ) := hst

end Commons.Analysis.Real