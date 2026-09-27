import Mathlib
import Submission.Work.OneDim.classify_connected_one_manifold

namespace Work.Drive.N2

/-- **A compact connected smooth 1-manifold is the circle.**  The classification of connected
smooth 1-manifolds (`Work.OneDim.classify_connected_one_manifold`) says that such a manifold is
diffeomorphic either to `ℝ` or to `Circle`; compactness rules out the first alternative, since a
homeomorphism transports compactness and `ℝ` is not compact. -/
theorem circleDiffeomorphCompactConnected {C : Type*} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) C]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) C]
    [T2Space C] [SecondCountableTopology C] [CompactSpace C] [ConnectedSpace C] :
    Nonempty (Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) Circle C
      ((⊤ : ℕ∞) : WithTop ℕ∞)) := by
  rcases Work.OneDim.classify_connected_one_manifold (C := C) with h | h
  · obtain ⟨e⟩ := h
    exfalso
    -- `e : ℝ ≃ₘ C` is in particular a homeomorphism, so `ℝ` would be compact.
    have hcomp : CompactSpace ℝ := e.toHomeomorph.symm.compactSpace
    exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℝ)) hcomp
  · exact h

end Work.Drive.N2
