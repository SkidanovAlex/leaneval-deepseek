import Mathlib
import Submission.Work.Domain.Resid.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.Domain.Resid

/-- For the stalk at `x` of an irreducible scheme, the algebra map to the function field
(the stalk at the generic point) is the specialization map of stalks. -/
theorem ofHom_algebraMap_eq_stalkSpecializes {X : AlgebraicGeometry.Scheme}
    [IrreducibleSpace X] (x : X) :
    CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) =
      X.presheaf.stalkSpecializes (genericPoint_specializes x) := by
  ext a
  simp only [CommRingCat.hom_ofHom, RingHom.algebraMap_toAlgebra]

theorem fromSpecStalk_algebraMap {X : AlgebraicGeometry.Scheme} [IrreducibleSpace X] (x : X) :
    CategoryTheory.CategoryStruct.comp
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x) X.functionField)))
      (X.fromSpecStalk x) = X.fromSpecStalk (genericPoint X) := by
  rw [ofHom_algebraMap_eq_stalkSpecializes x,
    AlgebraicGeometry.Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

end Work.Domain.Resid
