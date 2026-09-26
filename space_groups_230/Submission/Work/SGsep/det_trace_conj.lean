import Mathlib
import Submission.Work.SG.SGsepDefs

namespace Work.SGsep

open Work.SG

/-- Determinant and trace are invariant under conjugation by a unimodular integer matrix
(`U * invMat U = 1` and `invMat U * U = 1` because `IsUnit U.det` forces `U.det = ±1`). -/
theorem det_trace_conj {U : IMat} (hU : IsUnit U.det) (A : IMat) :
    (U * A * invMat U).det = A.det ∧ (U * A * invMat U).trace = A.trace := by
  constructor
  · -- multiplicativity of `det`, then `det (invMat U) = det U = ±1`.
    rw [Matrix.det_mul, Matrix.det_mul, det_invMat hU]
    rcases Int.isUnit_iff.mp hU with h | h <;> rw [h] <;> ring
  · -- cyclicity of `trace`, then `invMat U * U = 1`.
    rw [Matrix.trace_mul_cycle, invMat_mul hU, Matrix.one_mul]

end Work.SGsep
