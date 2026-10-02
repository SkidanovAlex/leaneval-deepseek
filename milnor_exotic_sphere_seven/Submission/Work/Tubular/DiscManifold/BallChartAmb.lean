import Submission.Work.Tubular.DiscManifold.Defs
import Submission.Work.SignatureBordism.BallBoundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The source of the preferred chart of the ball, as an ambient open set

The preferred chart `chartAt (Half n) b` of the closed ball `Ball n` has an open source, but the
latter is open only for the subspace topology of the ball: as a subset of `ℝ^{n+1}` it is the
intersection of an ambient open set with the (closed) ball.  When the ball is the fibre of the
normal disc bundle, the fibre coordinate of a point is an ambient vector that is *known* to be in
the ball, so the relevant set is the ambient open set `ballChartAmb n b` defined below.
-/

open scoped Manifold ContDiff Topology

namespace Work.Tubular.DiscManifold

open Work.SignatureBordism

/-- The source of the preferred chart of the closed ball at `b`, described as an **ambient** open
set: for a point of the ball the two descriptions agree. -/
noncomputable def ballChartAmb (n : ℕ) (b : Ball n) : Set (EuclideanSpace ℝ (Fin (n + 1))) := by
  classical
  exact if h : b ∈ interiorSource n then
    {v : EuclideanSpace ℝ (Fin (n + 1)) | -(1 / 2 : ℝ) < v 0 ∧ ‖v‖ < 1}
  else
    {v : EuclideanSpace ℝ (Fin (n + 1)) | 0 < bsign (decide (0 < (b : EuclideanSpace ℝ (Fin (n + 1)))
        (ballCoord n b (ball_ne_zero_of_not_mem n h)))) *
        v (ballCoord n b (ball_ne_zero_of_not_mem n h))}

end Work.Tubular.DiscManifold
