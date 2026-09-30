import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Matrix

namespace Work.BW

/-- For a linear map `T : E →ₗ[ℝ] F` between finite-dimensional real inner product spaces,
the determinant of the matrix of `T` with respect to orthonormal bases `bE`, `bF` (indexed by
the same type `ι`), squared, equals the determinant of the endomorphism `T ∘ T*` of `F`.

Indeed, in orthonormal bases the adjoint is represented by the transpose matrix, so the matrix
of `T ∘ T*` is `A * Aᵀ`, whose determinant is `(det A)²`. -/
theorem det_toMatrix_sq_eq_det_comp_adjoint {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bE : OrthonormalBasis ι ℝ E) (bF : OrthonormalBasis ι ℝ F) (T : E →ₗ[ℝ] F) :
    (LinearMap.toMatrix bE.toBasis bF.toBasis T).det ^ 2
      = LinearMap.det (T.comp (LinearMap.adjoint T)) := by
  -- In orthonormal bases, the matrix of the adjoint is the transpose of the matrix of `T`.
  have hB : LinearMap.toMatrix bF.toBasis bE.toBasis (LinearMap.adjoint T)
      = (LinearMap.toMatrix bE.toBasis bF.toBasis T)ᵀ := by
    simpa using LinearMap.toMatrix_adjoint bE bF T
  -- Pass to matrices: `det (T ∘ T*) = det (A * Aᵀ) = det A * det Aᵀ = (det A)²`.
  rw [← LinearMap.det_toMatrix bF.toBasis (T.comp (LinearMap.adjoint T)),
      LinearMap.toMatrix_comp bF.toBasis bE.toBasis bF.toBasis T (LinearMap.adjoint T),
      hB, Matrix.det_mul, Matrix.det_transpose, ← pow_two]

end Work.BW
