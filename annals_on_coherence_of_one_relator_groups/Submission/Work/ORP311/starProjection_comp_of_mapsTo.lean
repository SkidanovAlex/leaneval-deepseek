import Mathlib
import Submission.Work.ORP311.P311Defs

namespace Work.ORP311

open scoped InnerProductSpace

theorem starProjection_comp_of_mapsTo {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (K K' : Submodule ℂ E) [K.HasOrthogonalProjection] [K'.HasOrthogonalProjection] (T : E →L[ℂ] E) (hT : ∀ x ∈ K, T x ∈ K') (hT' : ∀ y ∈ K', ContinuousLinearMap.adjoint T y ∈ K) : K'.starProjection ∘L T = T ∘L K.starProjection := by
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  -- Decompose `x = K.starProjection x + (x - K.starProjection x)`; the second summand lies in `Kᗮ`.
  have hk : K.starProjection x ∈ K := by
    rw [Submodule.starProjection_apply]
    exact (K.orthogonalProjectionOnto x).2
  have hw : Kᗮ.starProjection x ∈ Kᗮ := by
    rw [Submodule.starProjection_apply]
    exact ((Kᗮ).orthogonalProjectionOnto x).2
  -- The adjoint hypothesis forces `T` to send `Kᗮ` into `K'ᗮ`.
  have hTu : T (Kᗮ.starProjection x) ∈ K'ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    rw [← ContinuousLinearMap.adjoint_inner_left T (Kᗮ.starProjection x) y]
    exact (Submodule.mem_orthogonal K _).mp hw (ContinuousLinearMap.adjoint T y) (hT' y hy)
  have hprojTu : K'.starProjection (T (Kᗮ.starProjection x)) = 0 := by
    have hmem : T (Kᗮ.starProjection x) ∈ (K'.starProjection : E →ₗ[ℂ] E).ker := by
      rw [Submodule.ker_starProjection K']
      exact hTu
    exact LinearMap.mem_ker.mp hmem
  rw [show K'.starProjection (T x) = K'.starProjection (T (K.starProjection x + Kᗮ.starProjection x)) by
        rw [Submodule.starProjection_add_starProjection_orthogonal]]
  rw [map_add, map_add, hprojTu, add_zero]
  exact Submodule.starProjection_eq_self_iff.mpr (hT _ hk)

end Work.ORP311
