import Mathlib

namespace Work.L2F.Mat2

theorem commute_entries (F : Type*) [Field F] (X Y : Matrix (Fin 2) (Fin 2) F)
    (htr : X.trace = 0) (hcomm : Y * X = X * Y) :
    Y 0 1 * X 1 0 = X 0 1 * Y 1 0 ∧
    X 0 1 * (Y 0 0 - Y 1 1) = (2 * X 0 0) * Y 0 1 ∧
    X 1 0 * (Y 0 0 - Y 1 1) = (2 * X 0 0) * Y 1 0 := by
  -- The trace condition on a 2x2 matrix says the two diagonal entries sum to zero.
  have htr' : X 0 0 + X 1 1 = 0 := by
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_two] using htr
  -- The (0,0) entry of the commutation relation.
  have h00 : Y 0 0 * X 0 0 + Y 0 1 * X 1 0 = X 0 0 * Y 0 0 + X 0 1 * Y 1 0 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hcomm
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  -- The (0,1) entry of the commutation relation.
  have h01 : Y 0 0 * X 0 1 + Y 0 1 * X 1 1 = X 0 0 * Y 0 1 + X 0 1 * Y 1 1 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hcomm
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  -- The (1,0) entry of the commutation relation.
  have h10 : Y 1 0 * X 0 0 + Y 1 1 * X 1 0 = X 1 0 * Y 0 0 + X 1 1 * Y 1 0 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) hcomm
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  refine ⟨?_, ?_, ?_⟩
  · -- (0,0) entry: diagonal terms cancel, leaving the off-diagonal relation.
    linear_combination h00
  · -- (0,1) entry combined with the trace condition.
    linear_combination h01 - Y 0 1 * htr'
  · -- (1,0) entry combined with the trace condition.
    linear_combination -h10 - Y 1 0 * htr'

end Work.L2F.Mat2
