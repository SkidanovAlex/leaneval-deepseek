import Mathlib
import Submission.Work.Genus.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Genus.OrderInf

open Polynomial

/-- The order at infinity of a polynomial: if `p` has degree `n` then `p` has a pole of order `n`
at infinity.  Immediate from `RatFunc.intDegree_polynomial`. -/
theorem ordInf_polynomial {F : Type*} [Field F] (p : Polynomial F) :
    Work.Genus.ordInf (algebraMap (Polynomial F) (RatFunc F) p) = -(p.natDegree : ℤ) := by
  rw [Work.Genus.ordInf, RatFunc.intDegree_polynomial]

end Work.Genus.OrderInf
