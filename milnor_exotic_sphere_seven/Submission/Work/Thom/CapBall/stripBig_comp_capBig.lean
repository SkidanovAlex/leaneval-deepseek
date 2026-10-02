import Mathlib
import Submission.Work.Thom.CapGeomDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom.CapBall

/-- The strip of the cap map recovers the original point: `stripBig` is a left inverse of `capBig`
on the level of the underlying Euclidean space.  This is because `capMap n w` has the same first
`n` coordinates as `w` and differs only in its last coordinate. -/
theorem strip_capMap (n : ℕ) (w : EuclideanSpace ℝ (Fin n)) :
    Work.Morse.strip (capMap n w) = w := by
  apply PiLp.ext
  intro i
  rw [Work.Morse.strip_ofLp, capMap_castSucc]

/-- The projection `stripBig` is a left inverse of the cap map `capBig`: the composite
`stripBig n ∘ capBig n` is the identity of the closed ball `MBall n`. -/
theorem stripBig_comp_capBig (n : ℕ) :
    (stripBig n).comp (capBig n) = ContinuousMap.id (MBall n) := by
  apply ContinuousMap.ext
  intro q
  apply Subtype.ext
  show Work.Morse.strip (capMap n q.1) = q.1
  rw [strip_capMap]

end Work.Thom.CapBall
