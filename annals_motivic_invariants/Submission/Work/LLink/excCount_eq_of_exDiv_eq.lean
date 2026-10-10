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

/-- Canonical form of `excCount` on a named exceptional set: replacing `exDiv φ` by an explicit
description `A` of it.  No finiteness of `A` is assumed: when `A` is infinite both sides are `0`. -/
theorem excCount_eq_of_exDiv_eq (𝕜 : Type) [Field 𝕜] {X Y Z : Scheme.{0}}
    [IrreducibleSpace X] [IrreducibleSpace Y] [X.Over (Spec (.of 𝕜))] [Z.Over (Spec (.of 𝕜))]
    (z : Z) (φ : X.BirationalMap Y) {A : Set X} (h : exDiv φ = A) :
    excCount 𝕜 z φ = (A ∩ {x | ResEquiv 𝕜 x z}).ncard := by
  show (exDiv φ ∩ {x | ResEquiv 𝕜 x z}).ncard = (A ∩ {x | ResEquiv 𝕜 x z}).ncard
  rw [h]

end Work.LLink
