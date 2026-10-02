import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.HalfCover
import Submission.Work.Orient.Boundary.HalfCoverGlue

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A coordinate half-ball of the interior around every interior point

The side condition of `Work.Orient.IsHalfOrientationFamily` and of the localisation isomorphism
`Work.Orient.Boundary.HalfRestrictIsoAtPoint` is that a coordinate half-ball consists of **interior**
points.  This file supplies that side condition locally: around every point `x` of the interior
`W° = W ∖ ∂W` there is a coordinate half-ball `halfBallPiece (n+1) W z r` containing `x` and
contained in `W°`.

It is an immediate consequence of
`Work.Orient.Boundary.exists_halfBall_subset` (a point of an open set lies in a coordinate half-ball
inside it) applied to the open set `W°`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.Orient.Boundary

noncomputable section

/-- **A coordinate half-ball of the interior around every interior point.** -/
theorem ExistsInteriorHalfBall (n : ℕ) (W : TopCat.{0}) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W] (x : W)
    (hx : x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :
    ∃ (z : W) (r : ℝ), 0 < r ∧ Work.Orient.halfBallGood (n + 1) W z r ∧
      x ∈ Work.Orient.halfBallPiece (n + 1) W z r ∧
      ∀ y ∈ Work.Orient.halfBallPiece (n + 1) W z r,
        y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W := by
  have hU : IsOpen ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)ᶜ :=
    (isClosed_boundary_halfSpace n W).isOpen_compl
  obtain ⟨r, hr, hgood, hsub⟩ := exists_halfBall_subset (n := n) hU hx
  exact ⟨x, r, hr, hgood, mem_halfBallPiece_center hr, fun y hy => hsub hy⟩

end

end Work.Orient.Boundary
