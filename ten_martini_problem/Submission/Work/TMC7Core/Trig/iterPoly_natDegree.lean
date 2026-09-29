import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Trig

/-!
# Degree bound for the polynomial transfer cocycle

`iterPoly α lam E n` is the matrix of polynomials (in `z`) which, evaluated at
`z = e^{2πix}`, equals `z^n A_n(x)` (see `iterPoly_eval`).  Each factor
`tmPoly lam E w` has entries of degree `≤ 2` and `iterPoly` starts at the
identity, so every entry of `iterPoly α lam E n` is a polynomial of degree
`≤ 2 n`.
-/

namespace Work.TMC7Core.Trig

open Polynomial Matrix

/-- `MatDegLe M d` records that every entry of a `2 × 2` matrix of polynomials has
`natDegree ≤ d`. -/
def MatDegLe (M : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) (d : ℕ) : Prop :=
  ∀ i j, (M i j).natDegree ≤ d

/-- Monotonicity of `MatDegLe` in the degree bound. -/
lemma matDegLe_mono {M : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)} {a b : ℕ}
    (h : MatDegLe M a) (hab : a ≤ b) : MatDegLe M b :=
  fun i j => (h i j).trans hab

/-- The identity matrix has all entries of degree `≤ 0`. -/
lemma matDegLe_one : MatDegLe (1 : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp

/-- Every entry of the single step `tmPoly lam E w` has degree `≤ 2`. -/
lemma matDegLe_tmPoly (lam : ℝ) (E : ℂ) (w : ℂ) : MatDegLe (tmPoly lam E w) 2 := by
  intro i j
  fin_cases i <;> fin_cases j
  · show (C E * (C w * X) - C (lam : ℂ) * ((C w * X) ^ 2 + 1)).natDegree ≤ 2
    compute_degree!
  · show (-(C w * X)).natDegree ≤ 2
    compute_degree!
  · show (C w * X).natDegree ≤ 2
    compute_degree!
  · show (0 : ℂ[X]).natDegree ≤ 2
    compute_degree!

/-- The product of matrices with entry degree bounds `a` and `b` has entry degree
bound `a + b`. -/
lemma matDegLe_mul {A B : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)} {a b : ℕ}
    (hA : MatDegLe A a) (hB : MatDegLe B b) : MatDegLe (A * B) (a + b) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Polynomial.natDegree_sum_le_of_forall_le Finset.univ (fun k => A i k * B k j)
    (fun k _ => Polynomial.natDegree_mul_le_of_le (hA i k) (hB k j))

/-- Every entry of `iterPoly α lam E n` is a polynomial of degree `≤ 2 n`. -/
lemma matDegLe_iterPoly (α lam : ℝ) (E : ℂ) (n : ℕ) :
    MatDegLe (iterPoly α lam E n) (2 * n) := by
  induction n with
  | zero =>
      show MatDegLe (iterPoly α lam E 0) (2 * 0)
      rw [show iterPoly α lam E 0 = 1 from by rw [iterPoly]]
      exact matDegLe_one
  | succ n ih =>
      rw [show iterPoly α lam E (n + 1) =
            tmPoly lam E (omega α ^ n) * iterPoly α lam E n from by rw [iterPoly]]
      exact matDegLe_mono (matDegLe_mul (matDegLe_tmPoly lam E (omega α ^ n)) ih) (by omega)

theorem iterPoly_natDegree (α lam : ℝ) (E : ℂ) (n : ℕ) (i j : Fin 2) :
    (iterPoly α lam E n i j).natDegree ≤ 2 * n :=
  matDegLe_iterPoly α lam E n i j

end Work.TMC7Core.Trig
