import Mathlib
import Submission.Work.MotK.TwRule
import Submission.Work.MotK.KleinTwData
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TwRuling

theorem sdRankCert14 {R : Type*} [CommRing R] (a b h : R) (y : Fin 5 → R) :
    a * (((-a * b ^ 2 * (a * h * (y 4) ^ 2 + 2 * b * (y 0) * (y 3)))
            * (a * h * (a ^ 3 * (y 1) * (y 3) - 2 * b ^ 3 * (y 0) * (y 4))))
          - ((a ^ 2 * b * (2 * a * (y 0) ^ 2 - b * h * (y 1) * (y 4)))
            * (a ^ 2 * (a ^ 2 * h * (y 3) * (y 4) - 4 * b ^ 2 * (y 0) * (y 2))))
          - 2 * b ^ 2 * (y 0) ^ 2
            * (a * (b ^ 5 - 2 * a ^ 5) * (y 1) ^ 2 + b * (3 * a ^ 5 + b ^ 5) * (y 0) * (y 2)))
      = (-2 * a * b * (2 * a ^ 5 - b ^ 5) * (y 1) ^ 2
            - 2 * b ^ 2 * (a ^ 5 - b ^ 5) * (y 0) * (y 2))
          * Work.MotK.kleinTwP0 a b h y
        + (2 * a ^ 2 * b ^ 5 * h ^ 2 * (y 4) ^ 2 - 2 * a ^ 3 * b ^ 4 * h * (y 1) * (y 2)
            - 2 * a * b * h * (a ^ 5 - 2 * b ^ 5) * (y 0) * (y 3))
          * Work.MotK.kleinTwP1 a b h y
        + (-2 * a ^ 2 * b ^ 5 * h * (y 2) ^ 2 + 4 * a * b * h * (a ^ 5 - b ^ 5) * (y 1) * (y 3))
          * Work.MotK.kleinTwP2 a b h y
        + (2 * b ^ 2 * h * (2 * a ^ 5 - b ^ 5) * (y 1) * (y 4))
          * Work.MotK.kleinTwP3 a b h y := by
  simp only [Work.MotK.kleinTwP0, Work.MotK.kleinTwP1, Work.MotK.kleinTwP2, Work.MotK.kleinTwP3]
  first | refl_ring1 | ring

end Work.MotK.TwRuling
