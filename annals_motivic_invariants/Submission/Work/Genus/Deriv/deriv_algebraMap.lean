import Mathlib
import Submission.Work.Genus.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.Deriv

/-- The derivative of `F(t)` restricts to the formal derivative on polynomials.  (`RatFunc.num_algebraMap`,
`RatFunc.denom_algebraMap`.) -/
theorem deriv_algebraMap {F : Type*} [Field F] (p : Polynomial F) :
    Work.Genus.deriv (algebraMap (Polynomial F) (RatFunc F) p)
      = algebraMap (Polynomial F) (RatFunc F) (Polynomial.derivative p) := by
  unfold Work.Genus.deriv
  rw [RatFunc.num_algebraMap, RatFunc.denom_algebraMap]
  simp

end Work.Genus.Deriv
