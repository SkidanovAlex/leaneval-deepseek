import Mathlib

/-!
# Norm-preserving linear maps of real inner product spaces preserve inner products

If `L : E →ₗ[ℝ] F` between real inner product spaces satisfies `‖L x‖ = ‖x‖`
for every `x` (i.e. `L` is a linear isometry), then
`⟪L x, L y⟫ = ⟪x, y⟫` for all `x y`.  This is the polarization step; it is
what turns an isometric immersion into a surface whose tangent frame is
orthonormal.
-/

namespace Commons.Analysis.InnerProductSpace

/-- A norm-preserving real-linear map between real inner product spaces
preserves inner products. -/
theorem inner_map_map_of_isometry {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] (L : E →ₗ[ℝ] F)
    (hL : ∀ x : E, ‖L x‖ = ‖x‖) (x y : E) : inner ℝ (L x) (L y) = inner ℝ x y := by
  have e1 : ‖L x + L y‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ (L x) (L y) + ‖y‖ ^ 2 := by
    rw [norm_add_sq_real (L x) (L y), hL x, hL y]
  have e2 : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x y + ‖y‖ ^ 2 := norm_add_sq_real x y
  have hLadd : L (x + y) = L x + L y := map_add L x y
  have e3 : ‖x + y‖ ^ 2 = ‖L x + L y‖ ^ 2 := by
    rw [← hL (x + y), hLadd]
  linarith [e1, e2, e3]

end Commons.Analysis.InnerProductSpace
