import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.det_mono_posSemidef_sub

namespace Commons.Analysis.InnerProductSpace

/-- Determinant monotonicity for real positive-semidefinite matrices in the Loewner
order: if `A` and `B` are positive semidefinite and `A - B` is positive semidefinite,
then `det B ≤ det A`.

This is exactly `Commons.LinearAlgebra.Matrix.det_mono_posSemidef_sub` applied with the
roles of `A` and `B` interchanged: that lemma says that if `X` is positive semidefinite
and `Y - X` is positive semidefinite then `X.det ≤ Y.det`. Here we take `X := B` and
`Y := A`, using `hB` and `hsub : (A - B).PosSemidef`. -/
lemma det_le_det_of_posSemidef_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hsub : (A - B).PosSemidef) :
    B.det ≤ A.det := by
  exact Commons.LinearAlgebra.Matrix.det_mono_posSemidef_sub (A := B) (B := A) hB hsub

end Commons.Analysis.InnerProductSpace
