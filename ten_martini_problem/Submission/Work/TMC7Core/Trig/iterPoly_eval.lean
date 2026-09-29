import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Trig

namespace Work.TMC7Core.Trig

open Polynomial Matrix
open Work.TMC7Core

/-- Evaluating the polynomial transfer factor `tmPoly lam E w` at `z` gives the
concrete complex transfer matrix `tmZ lam E (w * z)`. -/
theorem tmPoly_map_eval (lam : ℝ) (E : ℂ) (w z : ℂ) :
    (tmPoly lam E w).map (Polynomial.eval z) = tmZ lam E (w * z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tmPoly, tmZ]

/-- The identity matrix of polynomials evaluates (entrywise) to the identity matrix. -/
theorem one_map_eval (z : ℂ) :
    (1 : Matrix (Fin 2) (Fin 2) ℂ[X]).map (Polynomial.eval z) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Matrix.map_one]
  · simp
  · simp

theorem iterPoly_eval (α lam : ℝ) (E : ℂ) (n : ℕ) (z : ℂ) :
    (iterPoly α lam E n).map (Polynomial.eval z) = iterZ α lam E n z := by
  induction n with
  | zero => simp [iterPoly, iterZ, Matrix.map_one]
  | succ n ih =>
    rw [iterPoly, iterZ]
    rw [show (tmPoly lam E (omega α ^ n) * iterPoly α lam E n).map (Polynomial.eval z)
        = (tmPoly lam E (omega α ^ n)).map (Polynomial.eval z)
          * (iterPoly α lam E n).map (Polynomial.eval z) from
      Matrix.map_mul (f := Polynomial.evalRingHom z)]
    rw [ih, tmPoly_map_eval]
    congr 1
    rw [mul_comm]

end Work.TMC7Core.Trig
