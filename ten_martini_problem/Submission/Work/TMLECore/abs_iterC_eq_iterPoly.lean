import Mathlib
import Submission.Work.TMC7Core.Trig
import Submission.Work.TMC7Core.Trig.iterPoly_eval
import Submission.Work.TMC7Core.Trig.iterZ_smul
import Submission.Work.TMC7Core.Trig.exp_mul_omega_pow

namespace Work.TMLECore

open Polynomial

/-- The `(0,0)` entry of `A_n(x)`: its absolute value is the absolute value of the
`(0,0)` entry of the Laurent-polynomial transfer matrix `z^n A_n` evaluated at
`z = e^{2πix}`, the scalar factor `z^n ω^{n(n-1)/2}` being unimodular. -/
theorem abs_iterC_eq_iterPoly (α lam : ℝ) (E : ℂ) (n : ℕ) (x : ℝ) :
    ‖Work.TMC7Core.iterC α lam E n x 0 0‖ =
      ‖Polynomial.eval (Complex.exp (2 * Real.pi * Complex.I * x)) (Work.TMC7Core.iterPoly α lam E n 0 0)‖ := by
  -- evaluate the polynomial much as a matrix over `ℂ`
  rw [show Polynomial.eval (Complex.exp (2 * Real.pi * Complex.I * x))
        (Work.TMC7Core.iterPoly α lam E n 0 0)
      = (Work.TMC7Core.iterPoly α lam E n).map
          (Polynomial.eval (Complex.exp (2 * Real.pi * Complex.I * x))) 0 0 from rfl]
  -- the evaluated polynomial matrix is the algebraic cocycle `iterZ`
  rw [Work.TMC7Core.Trig.iterPoly_eval, Work.TMC7Core.Trig.iterZ_smul]
  simp only [Matrix.smul_apply]
  -- the scalar factor `z^n ω^{n(n-1)/2}` is unimodular
  have hz1 : ‖Complex.exp (2 * Real.pi * Complex.I * x)‖ = 1 := by
    rw [Complex.norm_exp]; simp
  have hω1 : ‖Work.TMC7Core.omega α‖ = 1 := by
    rw [Work.TMC7Core.omega, Complex.norm_exp]; simp
  have hsc : ‖Complex.exp (2 * Real.pi * Complex.I * x) ^ n
      * Work.TMC7Core.omega α ^ (n * (n - 1) / 2)‖ = 1 := by
    rw [norm_mul, norm_pow, norm_pow, hz1, hω1]; simp
  rw [norm_smul, hsc, one_mul]

end Work.TMLECore
