import Mathlib
import Submission.Work.TMC7Core.Cocycle

namespace Work.TMC7Core.Trig

/-- Scaling every factor of an ordered matrix product scales the product by the
product of the scalars. -/
theorem matProd_smul (c : ℕ → ℂ) (A : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ) :
    matProd (fun j => c j • A j) n = (∏ j ∈ Finset.range n, c j) • matProd A n := by
  induction n with
  | zero => simp [matProd_zero]
  | succ n ih =>
    rw [matProd_succ, ih, matProd_succ, Finset.prod_range_succ,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    ring

end Work.TMC7Core.Trig
