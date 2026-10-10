import Mathlib
import Submission.Work.MotK.TwAmbh

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TGen

theorem KleinTwFhomPi {R : Type*} [CommRing R] (a b h : R) (p x : Fin 5 → R)
    (hp : Work.MotK.kleinTwQ a b h p = 0) :
    Work.MotK.kleinTwFhom a b h p (Work.MotK.kleinTwPi p x)
      = Work.MotK.kleinTwFhom a b h p x := by
  -- `kleinTwFhom p v = kleinTwBilin p v * kleinTwS (kleinTwStereo p v)`.  Both factors are
  -- unchanged by replacing `x` with the projection `π x = x - x₀·p`:
  -- * `kleinTwBilin p (π x) = kleinTwBilin p x` (`kleinTwBilin_pi_eq`), and
  -- * `kleinTwStereo p (π x) = kleinTwStereo p x`, which is the inverse-stereographic identity
  --   `KleinTwStereo_pi`: `y(π x) = q(x)·p - b(p,x)·x = y(x)`.
  rw [Work.MotK.kleinTwFhom, Work.MotK.kleinTwFhom,
    Work.MotK.kleinTwBilin_pi_eq a b h p x hp,
    Work.MotK.KleinTwStereo_pi a b h p x hp]
  rfl

end Work.MotK.TGen
