import Mathlib
import Submission.Work.MotK.LinkTwData
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The stereographic identity for the T-twisted quadric

Let `q = kleinTwQ` be the T-invariant quadric and `b = kleinTwBilin` its polar form,
`b(u,v) = q(u+v) - q(u) - q(v)`, so that `q(u+v) = q(u) + q(v) + b(u,v)` and
`b(u,u) = 2 q(u)`.  For the inverse stereographic projection
`y = kleinTwStereo a b h p v = q(v)·p - b(p,v)·v` one has, identically in `p` and `v`
(no hypothesis on `p`),

  `q(y) = q(v)^2 · q(p)`.

Indeed `q(q(v)p - b(p,v)v) = q(v)^2 q(p) - q(v) b(p,v)^2 + b(p,v)^2 q(v)`.  This is the
T-twisted analogue of `kleinQ_stereo` (`Work.MotK.KleinIdents`); it is what makes the
hyperplane/quadric reduction of the Crauder--Katz link work in Kummer coordinates.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotK

theorem KleinTwQ_stereo {R : Type*} [CommRing R] (a b h : R) (p v : Fin 5 → R) :
    Work.MotK.kleinTwQ a b h (Work.MotK.kleinTwStereo a b h p v)
      = Work.MotK.kleinTwQ a b h v ^ 2 * Work.MotK.kleinTwQ a b h p := by
  simp only [kleinTwQ, kleinTwP0, kleinTwStereo, kleinTwBilin, Pi.add_apply]
  first | refl_ring1 | ring

end Work.MotK
