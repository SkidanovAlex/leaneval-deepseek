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

/-- At most as many exceptional divisors of `φ` match the base point `z` as there are exceptional
divisors of `φ` at all.  The finiteness hypothesis is needed because `Set.ncard` returns `0` on
infinite sets. -/
theorem excCount_le_ncard_exDiv (𝕜 : Type) [Field 𝕜] {X Y Z : Scheme.{0}}
    [IrreducibleSpace X] [IrreducibleSpace Y] [X.Over (Spec (.of 𝕜))] [Z.Over (Spec (.of 𝕜))]
    (z : Z) (φ : X.BirationalMap Y) (h : (exDiv φ).Finite) :
    excCount 𝕜 z φ ≤ (exDiv φ).ncard := by
  -- `excCount 𝕜 z φ` is the cardinality of the subset of `exDiv φ` consisting of those
  -- exceptional divisors whose birational class matches that of `z`.
  refine Set.ncard_le_ncard (fun x hx => hx.1) h

end Work.LLink
