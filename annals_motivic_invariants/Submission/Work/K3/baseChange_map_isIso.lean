import Mathlib
import Submission.Work.K3.BaseChange

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.K3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

/-- Base change of an isomorphism over the base field is an isomorphism. -/
theorem baseChange_map_isIso (K L : Type) [Field K] [Field L] [Algebra K L]
    {X Y : Scheme.{0}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    (e : X ≅ Y) [e.hom.IsOver (Spec (.of K))] :
    IsIso (Work.K3.baseChangeMap K L e.hom) := by
  rw [Work.K3.baseChangeMap]
  exact pullback.map_isIso _ _ _ _ _ _ _ _ _

end Work.K3
