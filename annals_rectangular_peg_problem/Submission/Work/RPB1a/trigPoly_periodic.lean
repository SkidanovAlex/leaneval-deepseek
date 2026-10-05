import Mathlib
import Submission.Work.RPB1a.Defs

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real
open Work.RPB1a

theorem trigPoly_periodic (N : ℕ) (a : ℤ → ℂ) (t : ℝ) :
    trigPoly N a (t + 2 * π) = trigPoly N a t := by
  simp only [trigPoly]
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  have hcast : (↑(t + 2 * π) : ℂ) = (↑t : ℂ) + ((2 : ℝ) * π : ℂ) := by
    push_cast; ring
  have h : (↑n : ℂ) * (↑(t + 2 * π) : ℂ) * I
      = (↑n : ℂ) * (↑t : ℂ) * I + (↑n : ℂ) * (2 * ↑π * I) := by
    rw [hcast]; push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end Work.RPB1a
