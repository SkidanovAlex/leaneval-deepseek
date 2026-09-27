import Mathlib
import Submission.Work.Octonion.Basic

namespace Work.Octonion

/-- The octonions `𝕆 = WithLp 2 (ℍ × ℍ)`, with the `ℓ²`-norm, are isometric as a real normed
space to the standard Euclidean space `ℝ⁸`.  Indeed `𝕆` is an 8-dimensional inner product space
over `ℝ`, and any finite-dimensional inner product space admits an orthonormal basis, hence a
linear isometry equivalence with `EuclideanSpace ℝ (Fin (finrank ℝ 𝕆)) = ℝ⁸`. -/
theorem isometry_equiv_euclidean :
    Nonempty (Submission.Octonion ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 8)) := by
  have h : Module.finrank ℝ Submission.Octonion = 8 := by
    rw [LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ (Quaternion ℝ × Quaternion ℝ)),
      Module.finrank_prod, Quaternion.finrank_eq_four]
  exact ⟨((stdOrthonormalBasis ℝ Submission.Octonion).reindex (finCongr h)).repr⟩

end Work.Octonion
