import Mathlib
import Submission.Work.LerayHirsch.modelQuotientTopChern

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The universal constant of the model quotient bundle

`Work.LerayHirsch.modelQuotientTopChern` states that the top Chern class of the tautological
quotient bundle over `P(ε^{n+1}) = ℂPⁿ` is *some* integer multiple of `ζⁿ`.  This module names that
integer, so that the ψ-analysis of the crux can refer to the *same* integer in every fibre
computation.
-/

namespace Work.Gen

open Work.TangentClasses Work.Thom

noncomputable section

/-- **The universal constant `k_n`**: the multiple such that `c_n(quotientBundle (trivCore (n+1)))`
is `k_n · ζⁿ` (`Work.Gen.modelK_spec`).  Its value is `(-1)^n` (the top Chern class of the
dual tautological quotient is `ζⁿ` up to sign), but only the existence of the integer is used. -/
def modelK (n : ℕ) : ℤ := Classical.choose (Work.LerayHirsch.modelQuotientTopChern n)

/-- The defining property of `Work.Gen.modelK`. -/
theorem modelK_spec (n : ℕ) :
    Work.Thom.chernClass n n (Work.LerayHirsch.quotientBundle (Work.LerayHirsch.trivCore (n + 1)))
      = modelK n • Work.LerayHirsch.zetaPow (Work.LerayHirsch.trivCore (n + 1)) n :=
  Classical.choose_spec (Work.LerayHirsch.modelQuotientTopChern n)

end

end Work.Gen
