import Mathlib
import Submission.Work.Smooth.JordanSeparation.convexHull_eq_image_stdSimplex

/-!
# The convex hull of a compact subset of `ℂ` is compact

`ℂ` is a two-dimensional real vector space, so by Carathéodory's theorem every point of
`convexHull ℝ K` is a convex combination of at most three points of `K`
(`Work.Smooth.JordanSeparation.convexHull_eq_image_stdSimplex`):

`convexHull ℝ K` is the image of `stdSimplex ℝ (Fin 3) × K³` under the combination map
`(w, z) ↦ ∑ i, w i • z i`.  The simplex is compact, `K³` is compact as a finite product of `K`,
and the combination map is continuous, so the image is compact.
-/

namespace Work.Smooth.JordanSeparation

open Set

theorem isCompact_convexHull_of_isCompact {K : Set ℂ} (hK : IsCompact K) :
    IsCompact (convexHull ℝ K) := by
  rw [convexHull_eq_image_stdSimplex]
  exact ((isCompact_stdSimplex ℝ (Fin 3)).prod
    (isCompact_univ_pi (fun _ : Fin 3 => hK))).image (by fun_prop)

end Work.Smooth.JordanSeparation
