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

/-- Base change of the identity is the identity. -/
theorem baseChangeMap_id (K L : Type) [Field K] [Field L] [Algebra K L]
    (X : Scheme.{0}) [X.Over (Spec (.of K))] :
    Work.K3.baseChangeMap K L (𝟙 X) = 𝟙 (Work.K3.baseChange K L X) := by
  -- `baseChangeMap K L (𝟙 X)` unfolds to `pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) _ _`
  -- (the two compatibility proofs are proposition-valued, so definitional proof
  -- irrelevance identifies them with the `by simp` proofs of `pullback.map_id`),
  -- and `pullback.map` of three identities is the identity by `pullback.map_id`.
  simp [baseChangeMap, baseChange, pullback.map_id]

end Work.K3
