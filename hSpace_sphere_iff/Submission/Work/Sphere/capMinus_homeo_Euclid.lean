import Mathlib
import Submission.Work.Sphere.Cohomology

open scoped EuclideanSpace

namespace Work.Sphere

/-- The open cap `capMinus n = {x : S^{n+1} | x ≠ -pole}` of the unit sphere of
`EuclideanSpace ℝ (Fin (n+2))` is homeomorphic to `ℝ^{n+1}`: this is the stereographic projection
from the antipode of the pole.  Mathlib's `stereographic'` (file
`Mathlib/Geometry/Manifold/Instances/Sphere.lean`) provides exactly this chart: for the unit sphere
in an `(n+1)+1`-dimensional inner product space it is an open partial homeomorphism onto
`EuclideanSpace ℝ (Fin (n+1))` with source the complement of the projection point and target
`univ`.  Use it with `E = EuclideanSpace ℝ (Fin (n+2))` and projection point `-(polePt (n+1))`
(so that the source is the complement of `negPolePt (n+1)`, which is
`Submission.Sphere.capMinus n` by `Submission.Sphere.capMinus_eq`), then
`OpenPartialHomeomorph.toHomeomorphSourceTarget` and `Homeomorph.Set.univ`. -/
theorem capMinus_homeo_Euclid (n : ℕ) :
    Nonempty (↥(Submission.Sphere.capMinus n) ≃ₜ EuclideanSpace ℝ (Fin (n + 1))) := by
  -- The stereographic projection from `negPolePt (n+1)` is a homeomorphism from the complement of
  -- that point (which is `capMinus n`) onto the whole of `EuclideanSpace ℝ (Fin (n+1))`.
  have h := (stereographic' (n+1) (Submission.Sphere.negPolePt (n+1))).toHomeomorphSourceTarget
  rw [stereographic'_source, stereographic'_target] at h
  exact ⟨(Submission.Sphere.capMinus_eq n).symm ▸ (h.trans (Homeomorph.Set.univ _))⟩

end Work.Sphere
