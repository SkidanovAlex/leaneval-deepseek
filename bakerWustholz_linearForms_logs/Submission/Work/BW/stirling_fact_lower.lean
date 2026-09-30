import Mathlib
import Submission.Work.BW.stirling_sq_identity
import Submission.Work.BW.factorial_sq_identity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- **Stirling, lower bound.** For `1 ≤ X`: `2π·X^{2X−1}·e^{−2X} ≤ ((X−1)!)²`.
Immediate from Mathlib's `Stirling.le_factorial_stirling` at `n = X`
(`√(2πX)·(X/e)^X ≤ X!`), squared and divided by `X²`, using `(X!)²/X² = ((X−1)!)²`. -/
theorem stirling_fact_lower (X : ℕ) (hX : 1 ≤ X) :
    2 * Real.pi * (X : ℝ) ^ (2 * X - 1) * Real.exp (-(2 * (X : ℝ))) ≤
      ((((X - 1).factorial : ℕ)) : ℝ) ^ 2 := by
  have hXr : (0 : ℝ) ≤ (X : ℝ) := by positivity
  have hS := Stirling.le_factorial_stirling X
  have hnn : 0 ≤ Real.sqrt (2 * Real.pi * ↑X) * (↑X / Real.exp 1) ^ X := by positivity
  have hsq := pow_le_pow_left₀ hnn hS 2
  rw [stirling_sq_identity (X : ℝ) X hX hXr, factorial_sq_identity X hX] at hsq
  have hX2 : (0 : ℝ) < (X : ℝ) ^ 2 := by
    have : (0 : ℕ) < X := by omega
    positivity
  exact le_of_mul_le_mul_left hsq hX2

end Work.BW
