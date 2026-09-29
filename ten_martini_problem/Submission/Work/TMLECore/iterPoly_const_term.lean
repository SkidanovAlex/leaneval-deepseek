import Mathlib
import Submission.Work.TMC7Core.Trig

namespace Work.TMLECore

/-- The `(0,0)` entry of the polynomial cocycle `iterPoly α lam E n` evaluated at `z = 0`
is `(-λ)^n`: at `z = 0` each rescaled factor `tmPoly lam E w` reduces to the matrix
`!![-λ, 0; 0, 0]`, whose `(0,0)` entry is `-λ`. -/
theorem iterPoly_const_term (α lam : ℝ) (E : ℂ) (n : ℕ) :
    Polynomial.eval 0 (Work.TMC7Core.iterPoly α lam E n 0 0) = (-(lam : ℂ)) ^ n := by
  induction n with
  | zero => simp [Work.TMC7Core.iterPoly]
  | succ n ih =>
    rw [Work.TMC7Core.iterPoly]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Polynomial.eval_add, Polynomial.eval_mul]
    have h00 : Polynomial.eval 0
        (Work.TMC7Core.tmPoly lam E (Work.TMC7Core.omega α ^ n) 0 0) = -(lam : ℂ) := by
      simp [Work.TMC7Core.tmPoly]
    have h01 : Polynomial.eval 0
        (Work.TMC7Core.tmPoly lam E (Work.TMC7Core.omega α ^ n) 0 1) = 0 := by
      simp [Work.TMC7Core.tmPoly]
    rw [h00, h01]
    simp [ih, pow_succ, mul_comm]

end Work.TMLECore
