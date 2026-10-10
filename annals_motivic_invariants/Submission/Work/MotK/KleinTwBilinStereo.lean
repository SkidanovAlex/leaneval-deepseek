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
# The polar form of the T-twisted quadric on the stereographic image

Let `q = kleinTwQ` be the T-invariant quadric (`q = kleinTwP0`, the twisted Pfaffian `p_0`)
and `b = kleinTwBilin` its polar form, `b(u,v) = q(u+v) - q(u) - q(v)`.  Then
`b(u,u) = 2 q(u)` and `b` is additive in each argument; for the inverse stereographic
projection

  `y = kleinTwStereo a b h p v = q(v)·p - b(p,v)·v`

one computes, identically in `p` and `v` (no hypothesis on `p`),

  `b(p, y) = 2 q(v) q(p) - b(p,v)^2`.

Indeed `b(p, q(v)p - b(p,v)v) = q(v)·b(p,p) - b(p,v)² = 2 q(v) q(p) - b(p,v)²`.  This is the
T-twisted analogue of `kleinBilin_stereo` (`Work.MotK.KleinIdents`) and, together with
`KleinTwQ_stereo`, is one of the two identities making the map `f = P ∘ y` of the
quadro-cubic link land in the hyperplane `H = {z_0 = 0}`: on the source equation
`b(p,v) = 0` it gives `b(p, y(v)) = 2 q(v) q(p)`.

The proof is a direct polynomial expansion (`ring`) after unfolding the definitions; every
form is a polynomial with integer coefficients in the ring atoms `a, b, h, p, v`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotK

/-- The polar form of the T-twisted quadric, evaluated on a vector: `b(v,v) = 2 q(v)`. -/
theorem kleinTwBilin_self {R : Type*} [CommRing R] (a b h : R) (v : Fin 5 → R) :
    Work.MotK.kleinTwBilin a b h v v = 2 * Work.MotK.kleinTwQ a b h v := by
  simp only [kleinTwBilin, kleinTwQ, kleinTwP0, Pi.add_apply]
  first | refl_ring1 | ring

theorem KleinTwBilinStereo {R : Type*} [CommRing R] (a b h : R) (p v : Fin 5 → R) :
    Work.MotK.kleinTwBilin a b h p (Work.MotK.kleinTwStereo a b h p v)
      = 2 * Work.MotK.kleinTwQ a b h v * Work.MotK.kleinTwQ a b h p
        - Work.MotK.kleinTwBilin a b h p v ^ 2 := by
  simp only [kleinTwBilin, kleinTwQ, kleinTwP0, kleinTwStereo, Pi.add_apply]
  first | refl_ring1 | ring

end Work.MotK
