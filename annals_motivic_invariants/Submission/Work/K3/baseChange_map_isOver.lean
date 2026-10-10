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

/-- Base change of an over-morphism is again an over-morphism. -/
theorem baseChange_map_isOver (K L : Type) [Field K] [Field L] [Algebra K L]
    {X Y : Scheme.{0}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K))] :
    (Work.K3.baseChangeMap K L f).IsOver (Spec (.of L)) := by
  rw [Hom.isOver_iff]
  -- Unfold `baseChangeMap`, its source/target and the two `L`-structures into the explicit
  -- pullback data.  (`baseChangeMap` is `pullback.map` of the identity on `Spec L`, `f`, and the
  -- identity on `Spec K`.)
  change (pullback.map (Work.K3.specMap K L) (X ↘ Spec (.of K)) (Work.K3.specMap K L)
      (Y ↘ Spec (.of K)) (𝟙 (Spec (.of L))) f (𝟙 (Spec (.of K)))
      (by rw [Category.comp_id, Category.id_comp])
      (by rw [Category.comp_id]
          exact ((Hom.isOver_iff (S := Spec (.of K))).mp
            (inferInstance : f.IsOver (Spec (.of K)))).symm)) ≫
      pullback.fst (Work.K3.specMap K L) (Y ↘ Spec (.of K)) =
    pullback.fst (Work.K3.specMap K L) (X ↘ Spec (.of K))
  -- The first projection of `pullback.map` is `pullback.fst ≫ 𝟙`.
  rw [pullback.lift_fst]
  simp

end Work.K3
