import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Commons.Analysis.Complex.one_sub_exp_mul_I

namespace Commons.Analysis.Complex

/-- Quantitative lower bound for `‖1 - exp (t * I)‖ = 2 sin (t/2)` on `[0, π]`:
`2 t / π ≤ ‖1 - exp (t * I)‖`.  (Equivalently `sin (t/2) ≥ t/π`, the standard
`sin x ≥ 2x/π` bound.) -/
theorem two_mul_div_pi_le_norm_one_sub_exp (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ Real.pi) :
    2 * t / Real.pi ≤ ‖(1 : ℂ) - Complex.exp (t * Complex.I)‖ := by
  have ht2 : 0 ≤ t / 2 := by linarith
  have hsin_nonneg : 0 ≤ Real.sin (t / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht2 (by linarith [Real.pi_pos])
  have hnorm : ‖(1 : ℂ) - Complex.exp (t * Complex.I)‖ = 2 * Real.sin (t / 2) := by
    rw [one_sub_exp_mul_I t]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I]
    rw [show ‖((Real.sin (t / 2) : ℝ) : ℂ)‖ = Real.sin (t / 2) from by
          rw [show ‖((Real.sin (t / 2) : ℝ) : ℂ)‖ = |Real.sin (t / 2)| from by
                simpa using RCLike.norm_ofReal (K := ℂ) (Real.sin (t / 2)),
              abs_of_nonneg hsin_nonneg]]
    norm_num
  rw [hnorm]
  have hj : t / Real.pi ≤ Real.sin (t / 2) := by
    calc t / Real.pi = 2 / Real.pi * (t / 2) := by ring
      _ ≤ Real.sin (t / 2) := by
            exact Real.mul_le_sin ht2 (by linarith [Real.pi_pos])
  have hmul : 2 * (t / Real.pi) ≤ 2 * Real.sin (t / 2) :=
    mul_le_mul_of_nonneg_left hj (by norm_num)
  calc 2 * t / Real.pi = 2 * (t / Real.pi) := by ring
    _ ≤ 2 * Real.sin (t / 2) := hmul

end Commons.Analysis.Complex