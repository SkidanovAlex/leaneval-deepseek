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

/-- If no exceptional divisor of `φ` is birational to the base point `z`, then `φ` contributes
nothing to the `[κ(z)]`-coefficient in the forward direction. -/
theorem excCount_eq_zero_of_forall_not (𝕜 : Type) [Field 𝕜] {X Y Z : Scheme.{0}}
    [IrreducibleSpace X] [IrreducibleSpace Y] [X.Over (Spec (.of 𝕜))] [Z.Over (Spec (.of 𝕜))]
    (z : Z) (φ : X.BirationalMap Y) (h : ∀ x ∈ exDiv φ, ¬ ResEquiv 𝕜 x z) :
    excCount 𝕜 z φ = 0 := by
  have hset : {x : X | x ∈ exDiv φ ∧ ResEquiv 𝕜 x z} = ∅ := by
    ext y
    refine ⟨fun hy => absurd hy.2 (h y hy.1), fun hy => hy.elim⟩
  show Set.ncard {x : X | x ∈ exDiv φ ∧ ResEquiv 𝕜 x z} = 0
  rw [hset, Set.ncard_empty]

end Work.LLink
