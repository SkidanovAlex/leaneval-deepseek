import Mathlib
import Submission.Work.MotK.TwRule

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK

theorem KleinTwRMap {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b h : R)
    (z : Fin 5 → R) :
    (fun k => φ (Work.MotK.kleinTwR a b h z k))
      = Work.MotK.kleinTwR (φ a) (φ b) (φ h) (fun i => φ (z i)) := by
  funext k
  fin_cases k <;>
    simp [Work.MotK.kleinTwR, Work.MotK.kleinTwR0, Work.MotK.kleinTwR1,
      Work.MotK.kleinTwR2, Work.MotK.kleinTwR3, Work.MotK.kleinTwR4]

end Work.MotK
