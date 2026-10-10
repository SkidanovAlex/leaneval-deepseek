import Mathlib
import Submission.Work.LLink.Count

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.LLink

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

/-- An exceptional divisor of `φ` is a point at which `φ` is not a local isomorphism. -/
theorem not_isIsoAt_of_mem_exDiv {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    {φ : X.BirationalMap Y} {x : X} (h : x ∈ exDiv φ) : ¬ IsIsoAt φ x := h.2

end Work.LLink
