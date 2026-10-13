import Mathlib
import Submission.Work.WilE9.Defs

namespace Work.WilE9.Mat

/-- Cramer: if `A v = w` then `adj(A) w = det(A) • v`. -/
theorem adjugate_mulVec_of_mulVec_eq {q : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin q) (Fin q) R) (v w : Fin q → R) (h : Matrix.mulVec A v = w) :
    Matrix.mulVec A.adjugate w = A.det • v := by
  rw [← h, Matrix.mulVec_mulVec v A.adjugate A, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec]

end Work.WilE9.Mat
