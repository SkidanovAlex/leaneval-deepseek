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

/-- Base change is functorial: it preserves composition.

Both sides are computed by the universal property of the fibred products
`baseChange K L X = X ×_{Spec K} Spec L`: the base change of `f ≫ g` is the map on pullbacks
induced by `𝟙Spec L` on the first leg, `f ≫ g` on the middle leg and `𝟙Spec K` on the base
`Spec K`.  The result is a special case of the functoriality of `pullback.map`
(`pullback.map_comp`), the two base legs being identities. -/
theorem baseChangeMap_comp (K L : Type) [Field K] [Field L] [Algebra K L]
    {X Y Z : Scheme.{0}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    [Z.Over (Spec (.of K))] (f : X ⟶ Y) (g : Y ⟶ Z) [f.IsOver (Spec (.of K))]
    [g.IsOver (Spec (.of K))] :
    Work.K3.baseChangeMap K L (f ≫ g) =
      Work.K3.baseChangeMap K L f ≫ Work.K3.baseChangeMap K L g := by
  -- Unfold the base changes into the corresponding fibred products and `pullback.map`s.
  simp only [Work.K3.baseChangeMap, Work.K3.baseChange]
  -- Functoriality of `pullback.map` in the middle leg, with the two base legs equal to
  -- `𝟙Spec L` and `𝟙Spec K`.
  rw [pullback.map_comp (𝟙 (Spec (.of L))) (𝟙 (Spec (.of L))) f g
    (𝟙 (Spec (.of K))) (𝟙 (Spec (.of K)))]
  -- Normalise the composite identities `𝟙 ≫ 𝟙` and absorb the compatibility proofs.
  simp

end Work.K3
