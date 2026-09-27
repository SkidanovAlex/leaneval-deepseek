import Mathlib

namespace Work.Mostow

/--
The norm determinant (the absolute value of the determinant, i.e. the volume scaling
factor) of a linear endomorphism of a finite dimensional real inner product space is
invariant under taking the adjoint.

Both sides are rewritten as `‖det‖` (`LinearMap.normDet_eq_norm_det`), so it suffices
to compare the determinants.  In an orthonormal basis the matrix of the adjoint is the
transpose (conjugate transpose) of the matrix of the map, and the determinant of the
transpose equals the determinant.
-/
theorem normDet_adjoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L : E →ₗ[ℝ] E) :
    (LinearMap.adjoint L).normDet = L.normDet := by
  rw [LinearMap.normDet_eq_norm_det, LinearMap.normDet_eq_norm_det]
  congr 1
  let b := stdOrthonormalBasis ℝ E
  rw [← LinearMap.det_toMatrix b.toBasis (LinearMap.adjoint L),
      ← LinearMap.det_toMatrix b.toBasis L]
  rw [LinearMap.toMatrix_adjoint b b L, Matrix.det_conjTranspose]
  simp

end Work.Mostow
