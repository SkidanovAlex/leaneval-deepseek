import Mathlib
import Submission.Work.MotC2.InfPlaceCore
import Submission.Work.MotC2.affRing_eq_adjoin
import Submission.Work.MotC2.CoordPreserved

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

theorem infPlace_frac (L : Type*) [Field L] (E : WeierstrassCurve L) [E.IsElliptic] :
    ∀ f : Work.MotC2.Func E, ∃ s₁ s₂ : ↥(Work.MotC2.infPlace E),
      (s₂ : Work.MotC2.Func E) ≠ 0 ∧
        f * (s₂ : Work.MotC2.Func E) = (s₁ : Work.MotC2.Func E) :=
  infPlace_isFractionRing E

end Work.MotC2
