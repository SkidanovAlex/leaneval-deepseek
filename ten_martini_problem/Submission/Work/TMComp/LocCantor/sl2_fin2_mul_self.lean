import Mathlib

namespace Work.TMComp.LocCantor

/-- Cayley–Hamilton for `2 × 2` real matrices of determinant `1`:
`A * A = (tr A) • A - 1`. -/
theorem sl2_fin2_mul_self (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det = 1) :
    A * A = A.trace • A - 1 := by
  have h : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa [Matrix.det_fin_two] using hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
      Matrix.sub_apply, Matrix.smul_apply] <;>
    linarith [h]

end Work.TMComp.LocCantor
