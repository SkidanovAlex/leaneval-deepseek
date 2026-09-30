import Mathlib
import Submission.Work.PiS.Interfaces

set_option synthInstance.maxHeartbeats 400000

namespace Work.PiS

/-- Every linear isometry equivalence of `ℝⁿ⁺¹` restricts to a homeomorphism of the unit
sphere `Sⁿ`, acting on points by the same formula. -/
theorem sphereIsometryHomeomorph (n : ℕ)
    (h : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) :
    ∃ Φ : Sph n ≃ₜ Sph n, ∀ z : Sph n, (Φ z : EuclideanSpace ℝ (Fin (n + 1))) = h z := by
  have key : ∀ z : Sph n, h z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    fun z => by
      rw [mem_sphere_zero_iff_norm]; rw [h.norm_map]
      exact mem_sphere_zero_iff_norm.mp z.2
  have key' : ∀ z : Sph n, h.symm z ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    fun z => by
      rw [mem_sphere_zero_iff_norm]; rw [h.symm.norm_map]
      exact mem_sphere_zero_iff_norm.mp z.2
  refine ⟨{ toFun := fun z => ⟨h z, key z⟩
            invFun := fun z => ⟨h.symm z, key' z⟩
            left_inv := fun z => Subtype.ext (h.symm_apply_apply z)
            right_inv := fun z => Subtype.ext (h.apply_symm_apply z)
            continuous_toFun := Continuous.subtype_mk (h.continuous.comp continuous_subtype_val) key
            continuous_invFun :=
              Continuous.subtype_mk (h.symm.continuous.comp continuous_subtype_val) key' },
          fun z => rfl⟩

end Work.PiS
