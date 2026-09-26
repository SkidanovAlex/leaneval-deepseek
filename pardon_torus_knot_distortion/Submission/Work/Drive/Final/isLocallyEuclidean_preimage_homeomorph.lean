import Mathlib
import Submission.Work.Smooth.OneManifold.Basic

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion in
/-- **Local Euclidean-ness of dimension one is preserved by a homeomorphism of `ℝ³`**: the
preimage of a locally Euclidean (topological `1`-manifold) subset of `ℝ³` under a homeomorphism of
`ℝ³` is again locally Euclidean of dimension one. -/
theorem isLocallyEuclidean_preimage_homeomorph (Φ : R3 ≃ₜ R3) {Z : Set R3}
    (hZ : Work.Smooth.OneManifold.IsLocallyEuclidean Z) :
    Work.Smooth.OneManifold.IsLocallyEuclidean (Φ ⁻¹' Z) := by
  -- `Φ.symm` restricts to a homeomorphism `↥Z ≃ₜ ↥(Φ.symm '' Z)`, and `Φ.symm '' Z = Φ ⁻¹' Z`.
  have hset : Φ.symm '' Z = Φ ⁻¹' Z := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro hy
      exact ⟨Φ y, hy, by simp⟩
  exact Work.Smooth.OneManifold.isLocallyEuclidean_of_eq hset
    (Work.Smooth.OneManifold.isLocallyArc_of_homeomorph (Homeomorph.image Φ.symm Z) hZ)

end Work.Drive.Final
