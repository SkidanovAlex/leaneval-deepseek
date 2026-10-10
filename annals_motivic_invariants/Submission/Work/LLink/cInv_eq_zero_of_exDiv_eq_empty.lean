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

/-- A birational map with no exceptional divisor in either direction has vanishing invariant
coefficient. -/
theorem cInv_eq_zero_of_exDiv_eq_empty (𝕜 : Type) [Field 𝕜] {X Y Z : Scheme.{0}}
    [IrreducibleSpace X] [IrreducibleSpace Y] [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))]
    [Z.Over (Spec (.of 𝕜))] (z : Z) (φ : X.BirationalMap Y) (h : exDiv φ = ∅)
    (h' : exDiv φ.symm = ∅) : cInv 𝕜 z φ = 0 := by
  have h1 : excCount 𝕜 z φ.symm = 0 :=
    excCount_eq_zero_of_exDiv_eq_empty (X := Y) (Y := X) z φ.symm h'
  have h2 : excCount 𝕜 z φ = 0 :=
    excCount_eq_zero_of_exDiv_eq_empty z φ h
  show (excCount 𝕜 z φ.symm : ℤ) - (excCount 𝕜 z φ : ℤ) = 0
  rw [h1, h2]
  norm_num

end Work.LLink
