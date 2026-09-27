import Mathlib
import Submission.Work.Mostow.QIDefs

namespace Work.Mostow

/-- Conjugation by a linear isometry equivalence of `ℍⁿ` preserves the operator norm
of a continuous linear endomorphism.  Both directions are instances of Mathlib's
`opNorm_linearIsometryEquiv_mul` (postcomposition with an isometry) and
`opNorm_mul_linearIsometryEquiv` (precomposition with an isometry). -/
theorem normConjIsom {m : ℕ} (e : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
    (X : Submission.Mostow.E m →L[ℝ] Submission.Mostow.E m) :
    ‖(e : Submission.Mostow.E m →L[ℝ] Submission.Mostow.E m)
        * X * ((e.symm : Submission.Mostow.E m →L[ℝ] Submission.Mostow.E m))‖ = ‖X‖ := by
  rw [ContinuousLinearMap.opNorm_mul_linearIsometryEquiv,
    ContinuousLinearMap.opNorm_linearIsometryEquiv_mul]

end Work.Mostow
