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

/-- A birational map has `x` as its only exceptional divisor if and only if `x` is an exceptional
divisor and every other exceptional divisor is `x`. -/
theorem exDiv_eq_singleton_iff {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (φ : X.BirationalMap Y) (x : X) :
    exDiv φ = {x} ↔ x ∈ exDiv φ ∧ ∀ y, y ∈ exDiv φ → y = x :=
  Set.eq_singleton_iff_unique_mem

end Work.LLink
