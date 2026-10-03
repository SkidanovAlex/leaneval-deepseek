import Mathlib

namespace Work.A3

/-- `(k / e)^k ≤ k!` — the crude lower bound on the factorial coming from Stirling's
inequality (`Stirling.le_factorial_stirling`: `√(2πk)·(k/e)^k ≤ k!`) together with the
elementary `√(2πk) ≥ 1` for `k ≥ 1`. -/
theorem factorial_ge_div_exp (k : ℕ) : ((k : ℝ) / Real.exp 1) ^ k ≤ (Nat.factorial k : ℝ) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; norm_num
  · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hpi : (1 : ℝ) ≤ 2 * Real.pi * (k : ℝ) := by
      nlinarith [Real.pi_gt_three, hk1, Real.pi_pos]
    have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) := by
      rw [Real.one_le_sqrt]; exact hpi
    have hnonneg : (0 : ℝ) ≤ ((k : ℝ) / Real.exp 1) ^ k := by positivity
    calc ((k : ℝ) / Real.exp 1) ^ k
        ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k :=
          le_mul_of_one_le_left hnonneg hsqrt
      _ ≤ (Nat.factorial k : ℝ) := Stirling.le_factorial_stirling k

end Work.A3
