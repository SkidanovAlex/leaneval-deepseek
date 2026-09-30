import Mathlib
import Submission.Work.CurveBasics.BCSquare

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.CurveBasics.Curve.BCSquare

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry in
universe u in
theorem fieldMap_comp {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {F' : Type u} [Field F'] [Algebra F F'] [Algebra k F'] [IsScalarTower k F F']
    {C : Curve k} {C' : Curve F} {C'' : Curve F'} (S : Curve.BCSquare C C')
    (T : Curve.BCSquare C' C'') :
    (S.comp T).fieldMap = S.fieldMap ≫ T.fieldMap := by
  rw [Curve.BCSquare.fieldMap, Curve.BCSquare.fieldMap, Curve.BCSquare.fieldMap]
  dsimp only [Curve.BCSquare.comp]
  rw [Scheme.Hom.stalkMap_comp]
  rw [Category.assoc]
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_assoc]
  rw [TopCat.Presheaf.stalkSpecializes_comp_assoc]
  rfl

end Work.CurveBasics.Curve.BCSquare
