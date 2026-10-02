import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.injective_localisation_aux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Orient.Boundary

theorem injective_localisation_of_halfBallInterior (n : ℕ) (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (hy : y ∈ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (r : ℝ) (hr : 0 < r) (hgood : Work.Orient.halfBallGood (n + 1) W y r)
    (x : W) (hx : x ∈ (Work.Orient.halfBallPiece (n + 1) W y r) ∩
        {x : W | x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W}) :
    Function.Injective (Work.Orient.resRelH W (n + 1)
      (Set.singleton_subset_iff.mpr hx)) := by
  exact injective_localisation_of_halfBallInterior_aux n W y hy r hr hgood x hx

end Work.Orient.Boundary
