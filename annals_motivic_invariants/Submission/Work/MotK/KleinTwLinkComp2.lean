import Mathlib
import Submission.Work.MotK.KleinTwLink
import Submission.Work.MotK.TwDataMod5
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK

theorem KleinTwLinkComp2 {R : Type*} [CommRing R] (a b h : R) (p v : Fin 5 → R)
    (hp : Work.MotK.kleinTwQ a b h p = 0) (hp0 : p 0 = 1) (hv : v 0 = 0) :
    Work.MotK.kleinTwPi p (Work.MotK.kleinTwR a b h (Work.MotK.kleinTwP a b h
        (Work.MotK.kleinTwStereo a b h p v)))
      = fun k => -(Work.MotK.kleinTwFhom a b h p v) * v k := by
  funext k
  have hI1 := Work.MotK.KleinTwI1 a b h (Work.MotK.kleinTwStereo a b h p v)
  simp only [Work.MotK.kleinTwPi, Work.MotK.kleinTwFhom, Work.MotK.kleinTwStereo] at hI1 ⊢
  simp only [hI1, hp0, hv]
  first | refl_ring1 | ring

end Work.MotK
