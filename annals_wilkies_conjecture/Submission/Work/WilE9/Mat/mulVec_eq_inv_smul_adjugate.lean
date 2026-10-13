import Mathlib
import Submission.Work.WilE9.Defs

namespace Work.WilE9.Mat

/-- The solution of an invertible linear system, written with the adjugate. -/
theorem mulVec_eq_inv_smul_adjugate {q : ℕ} {R : Type*} [Field R]
    (A : Matrix (Fin q) (Fin q) R) (v w : Fin q → R) (h : Matrix.mulVec A v = w)
    (hd : A.det ≠ 0) :
    v = (A.det)⁻¹ • Matrix.mulVec A.adjugate w := by
  have h1 : Matrix.mulVec A.adjugate w = A.det • v := by
    calc Matrix.mulVec A.adjugate w
        = Matrix.mulVec A.adjugate (Matrix.mulVec A v) := by rw [h]
      _ = Matrix.mulVec (A.adjugate * A) v := by rw [Matrix.mulVec_mulVec]
      _ = Matrix.mulVec (A.det • 1) v := by rw [Matrix.adjugate_mul]
      _ = A.det • v := by rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [h1, smul_smul, inv_mul_cancel₀ hd, one_smul]

end Work.WilE9.Mat
