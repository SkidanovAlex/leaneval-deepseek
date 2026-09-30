import Mathlib
import Submission.Work.AbVar.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.AbVar.Rigidity

open CategoryTheory in
theorem isReduced_tensorObj_of_geometricallyIntegral {k : Type*} [Field k] [IsAlgClosed k]
    (X Y : Work.AbVar.Sch k) [AlgebraicGeometry.GeometricallyIntegral X.hom]
    [AlgebraicGeometry.LocallyOfFiniteType X.hom]
    [AlgebraicGeometry.GeometricallyIntegral Y.hom]
    [AlgebraicGeometry.LocallyOfFiniteType Y.hom] :
    AlgebraicGeometry.IsReduced (MonoidalCategoryStruct.tensorObj X Y).left := by
  -- `Y.left` is integral: it is geometrically integral over the one-point integral scheme
  -- `Spec k`, so `Y.left = Y.left ×_k Spec k` is integral by definition of geometric
  -- integrality applied to the residue field `k` of the unique point of `Spec k`.
  have : AlgebraicGeometry.IsIntegral Y.left :=
    AlgebraicGeometry.GeometricallyIntegral.isIntegral_of_subsingleton Y.hom
  -- `Y.left` is locally noetherian as it is locally of finite type over the noetherian
  -- scheme `Spec k`.
  have : AlgebraicGeometry.IsLocallyNoetherian Y.left :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian Y.hom
  -- `(X ⊗ Y).left = X.left ×_k Y.left`; the projection to the reduced, locally noetherian
  -- scheme `Y.left` is geometrically reduced (base change of `X.hom`) and flat (any morphism
  -- to `Spec k` is flat), so the total space is reduced.
  exact AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
    (Limits.pullback.snd X.hom Y.hom)

end Work.AbVar.Rigidity
