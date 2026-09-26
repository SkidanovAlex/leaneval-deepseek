import Mathlib
import Submission.Work.SG.SellingStep

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

open scoped Matrix

/-- For every ordered pair of distinct superbase indices, the matrix effecting the Selling step
is unimodular: its determinant is `-1`, hence a unit of `ℤ`.

The Selling step is one of the twelve elementary operations of the Selling reduction; each of
them is a signed permutation-like elementary move, so its matrix lies in `GL₃(ℤ)`.  This is
checked by direct evaluation on the twelve cases `(i,j)`, `i ≠ j`. -/
theorem selling_step_det (i j : Fin 4) (hij : i ≠ j) : IsUnit (sellStepMat i j).det := by
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | rw [show (sellStepMat _ _).det = -1 from by decide]
      exact isUnit_one.neg

end Work.SG
