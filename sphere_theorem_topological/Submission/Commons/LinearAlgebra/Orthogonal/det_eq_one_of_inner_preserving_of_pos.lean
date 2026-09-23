import Mathlib
import Submission.Commons.LinearAlgebra.Orthogonal.odd_dim_det_one_fixed_vector

namespace Commons.LinearAlgebra.Orthogonal

open LinearMap

theorem det_eq_one_of_inner_preserving_of_pos {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (f : V →ₗ[ℝ] V) (hf : ∀ x y : V, inner ℝ (f x) (f y) = inner ℝ x y) (hpos : 0 < LinearMap.det f) : LinearMap.det f = 1 := by
  -- An inner-product-preserving endomorphism `f` satisfies `f.adjoint * f = 1`.
  have hcomp : f.adjoint * f = 1 := by
    ext x
    apply ext_inner_right ℝ
    intro y
    rw [Module.End.mul_apply, LinearMap.adjoint_inner_left]
    exact hf x y
  -- Taking determinants: `(det f)^2 = det(f.adjoint) * det(f) = det 1 = 1`.
  have hsq : (LinearMap.det f) ^ 2 = 1 := by
    have h := map_mul LinearMap.det f.adjoint f
    rw [hcomp, map_one LinearMap.det] at h
    rw [det_adjoint_eq_det] at h
    simpa [pow_two] using h.symm
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact h
  · rw [h] at hpos; norm_num at hpos

end Commons.LinearAlgebra.Orthogonal
