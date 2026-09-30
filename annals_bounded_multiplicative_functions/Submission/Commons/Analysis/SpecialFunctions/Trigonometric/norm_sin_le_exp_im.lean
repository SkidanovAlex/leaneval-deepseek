import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.norm_sinh_ofReal
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.norm_cosh_ofReal
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.cosh_add_abs_sinh

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.SpecialFunctions.Trigonometric

private theorem norm_sin_ofReal (x : ℝ) : ‖Complex.sin (x : ℂ)‖ = |Real.sin x| := by
  rw [← Complex.ofReal_sin]
  rw [Complex.norm_real, Real.norm_eq_abs]

private theorem norm_cos_ofReal (x : ℝ) : ‖Complex.cos (x : ℂ)‖ = |Real.cos x| := by
  rw [← Complex.ofReal_cos]
  rw [Complex.norm_real, Real.norm_eq_abs]

theorem norm_sin_le_exp_im (x y : ℝ) : ‖Complex.sin (x + Complex.I * (y : ℂ))‖ ≤ Real.exp |y| := by
  rw [show (x : ℂ) + Complex.I * (y : ℂ) = (x : ℂ) + (y : ℂ) * Complex.I by ring]
  rw [Complex.sin_add_mul_I]
  have h1 : ‖Complex.sin (x : ℂ) * Complex.cosh (y : ℂ)‖ ≤ ‖Complex.cosh (y : ℂ)‖ := by
    calc
      ‖Complex.sin (x : ℂ) * Complex.cosh (y : ℂ)‖ = ‖Complex.sin (x : ℂ)‖ * ‖Complex.cosh (y : ℂ)‖ := norm_mul _ _
      _ ≤ 1 * ‖Complex.cosh (y : ℂ)‖ := by
        exact mul_le_mul_of_nonneg_right (by rw [norm_sin_ofReal]; exact Real.abs_sin_le_one x) (norm_nonneg _)
      _ = ‖Complex.cosh (y : ℂ)‖ := by simp
  have h2 : ‖Complex.cos (x : ℂ) * Complex.sinh (y : ℂ) * Complex.I‖ ≤ |Real.sinh y| := by
    calc
      ‖Complex.cos (x : ℂ) * Complex.sinh (y : ℂ) * Complex.I‖
          = ‖Complex.cos (x : ℂ) * Complex.sinh (y : ℂ)‖ * ‖Complex.I‖ := norm_mul _ _
      _ = ‖Complex.cos (x : ℂ)‖ * ‖Complex.sinh (y : ℂ)‖ := by rw [norm_mul, Complex.norm_I, mul_one]
      _ ≤ 1 * ‖Complex.sinh (y : ℂ)‖ := by
        exact mul_le_mul_of_nonneg_right (by rw [norm_cos_ofReal]; exact Real.abs_cos_le_one x) (norm_nonneg _)
      _ = |Real.sinh y| := by rw [norm_sinh_ofReal]; simp
  calc
    ‖Complex.sin (x : ℂ) * Complex.cosh (y : ℂ) + Complex.cos (x : ℂ) * Complex.sinh (y : ℂ) * Complex.I‖
        ≤ ‖Complex.sin (x : ℂ) * Complex.cosh (y : ℂ)‖ + ‖Complex.cos (x : ℂ) * Complex.sinh (y : ℂ) * Complex.I‖ := norm_add_le _ _
    _ ≤ ‖Complex.cosh (y : ℂ)‖ + |Real.sinh y| := by exact add_le_add h1 h2
    _ = Real.exp |y| := by
      rw [norm_cosh_ofReal]
      exact cosh_add_abs_sinh y

end Commons.Analysis.SpecialFunctions.Trigonometric