import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.PTGeometric

/-- The trace of the orthogonal projection onto a submodule `K` of a Euclidean space (viewed as an
endomorphism of the ambient space) equals `finrank ℝ K`.

This is the standard fact that the trace of a projection is the rank of the projection. -/
theorem trace_starProjection {n : ℕ} (K : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    [K.HasOrthogonalProjection] :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
      (K.subtypeL.comp K.orthogonalProjectionOnto) = (Module.finrank ℝ K : ℝ) := by
  -- Reinterpret the continuous-linear-map composite as a composite of linear maps.
  rw [show (↑(K.subtypeL ∘SL K.orthogonalProjectionOnto) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) =
      (K.subtypeL : K →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) ∘ₗ
        (K.orthogonalProjectionOnto : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] K) from rfl]
  -- The trace is invariant under cyclic permutation of the two factors.
  rw [LinearMap.trace_comp_comm' (K.orthogonalProjectionOnto : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] K)
        (K.subtypeL : K →ₗ[ℝ] EuclideanSpace ℝ (Fin n))]
  -- The projection followed by the inclusion is the identity of `K`.
  have h : (K.orthogonalProjectionOnto : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] K) ∘ₗ
      (K.subtypeL : K →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) = LinearMap.id := by
    ext v
    simp
  rw [h, LinearMap.trace_id]

end Work.PTGeometric
