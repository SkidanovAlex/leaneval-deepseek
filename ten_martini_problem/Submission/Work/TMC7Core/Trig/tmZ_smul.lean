import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Trig

namespace Work.TMC7Core.Trig

open Work.TMC7Core

/-- For `z = e^{2πix}` one has `z² + 1 = z · (2 cos 2πx)`: the algebraic identity that
converts the polynomial transfer matrix `tmZ` into `z • tmC`. -/
theorem exp_two_pi_I_sq_add_one (x : ℝ) :
    (Complex.exp (2 * Real.pi * Complex.I * x)) ^ 2 + 1
      = Complex.exp (2 * Real.pi * Complex.I * x)
        * (2 * (Real.cos (2 * Real.pi * x) : ℂ)) := by
  set θ : ℝ := 2 * Real.pi * x with hθ
  have hz : Complex.exp (2 * Real.pi * Complex.I * x)
      = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [hθ]
    congr 1
    push_cast
    ring
  rw [hz]
  have h2 := Complex.two_cos (θ : ℂ)
  rw [← Complex.ofReal_cos] at h2
  have h1 : Complex.exp ((θ : ℂ) * Complex.I)
      * Complex.exp (-((θ : ℂ) * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  rw [h2, mul_add, neg_mul, h1]
  ring

theorem tmZ_smul (lam : ℝ) (E : ℂ) (x : ℝ) : tmZ lam E (Complex.exp (2 * Real.pi * Complex.I * x)) = Complex.exp (2 * Real.pi * Complex.I * x) • tmC lam E x := by
  have hkey := exp_two_pi_I_sq_add_one x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [tmZ, tmC, Matrix.smul_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_fin_one] <;>
    rw [hkey] <;> push_cast <;> ring

end Work.TMC7Core.Trig
