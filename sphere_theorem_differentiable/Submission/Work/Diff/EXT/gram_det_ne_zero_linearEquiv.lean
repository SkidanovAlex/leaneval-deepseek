import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-- **Gram matrices of a positive definite bilinear form in a basis are non-singular**: if `L` is a
linear equivalence onto a real normed space `V` and `B` a symmetric positive definite continuous
bilinear form on `V`, then the matrix `i j ↦ B (L (bB i)) (L (bB j))` has non-zero determinant.
This is the linear-algebra core of `Work.Diff.EXT.gramM_det_ne_zero` (which proves the special case
where the frame is the coordinate frame of the chart at the base point), generalised to an arbitrary
linear equivalence `L` and an arbitrary positive definite `B`. -/
lemma gram_det_ne_zero_linearEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : E ≃ₗ[ℝ] V) (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hsymm : ∀ v w : V, B v w = B w v) (hpos : ∀ v : V, v ≠ 0 → 0 < B v v) :
    (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      B (L (Module.finBasis ℝ E i)) (L (Module.finBasis ℝ E j)))).det ≠ 0 := by
  classical
  -- The pull-back `Bₗ` of `B` along `L`, as a bilinear form on the model space `E`.
  let Bₗ : LinearMap.BilinForm ℝ E := LinearMap.mk₂ ℝ (fun ξ η => B (L ξ) (L η))
    (fun ξ η ζ => by simp) (fun c ξ η => by simp) (fun ξ η ζ => by simp) (fun c ξ η => by simp)
  have hBₗ_apply : ∀ ξ η : E, Bₗ ξ η = B (L ξ) (L η) := fun ξ η => by
    simp [Bₗ, LinearMap.mk₂_apply]
  -- `Bₗ` is symmetric and positive definite, because `B` is and `L` is injective.
  have hBₗsymm : Bₗ.IsSymm := LinearMap.BilinForm.IsSymm.mk (fun ξ η => by
    rw [hBₗ_apply, hBₗ_apply]; exact hsymm _ _)
  have hquad : Bₗ.toQuadraticMap.PosDef := by
    intro ξ hξ
    rw [LinearMap.BilinMap.toQuadraticMap_apply, hBₗ_apply]
    exact hpos _ (fun h => hξ (L.injective (by simpa using h)))
  -- The matrix in the statement is exactly the matrix of `Bₗ` in the basis `Module.finBasis ℝ E`.
  have hmat : (LinearMap.BilinForm.toMatrix (Module.finBasis ℝ E)) Bₗ =
      Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
        B (L (Module.finBasis ℝ E i)) (L (Module.finBasis ℝ E j))) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, Matrix.of_apply, hBₗ_apply]
  -- A positive definite quadratic form has a positive definite matrix in any basis ...
  have hpd : (Matrix.of (fun i j : Fin (Module.finrank ℝ E) =>
      B (L (Module.finBasis ℝ E i)) (L (Module.finBasis ℝ E j)))).PosDef := by
    rw [← hmat]
    exact (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix (Module.finBasis ℝ E) Bₗ hBₗsymm).mp
      hquad
  -- ... and a positive definite real matrix is non-singular.
  exact hpd.det_pos.ne'

end Work.Diff.EXT
