import Mathlib
import Submission.Work.SymQuot.DivOf.TowerSquare

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open Work.CurveBasics

universe u

namespace Work.SymQuot.DivOf

/-- **The `towerHom`-preimage of a base-changed open.**  For a tower of field extensions
`K → F → F'` the morphism `C_{F'} ⟶ C_F` (which is the base change of `Spec F' ⟶ Spec F`)
pulls the base-changed open `V_F` back to `V_{F'}`.  Equivalently, the preimage of `V_F`
under `towerHom` is `V_{F'}`, which is what makes `bcOpens` compatible with the tower
and lets `C.bcOpens F V`-sections be compared along `bcSquareTower`.

The proof is the computation `towerHom ≫ fst_F = fst_{F'}` (`BCSquareBaseChange.towerHom_fst`)
combined with `Opens.map_comp_obj` for `TopCat`. -/
theorem towerHom_preimage_bcOpens {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (F F' : Type u) [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F']
    [IsScalarTower K F F'] (V : C.left.Opens) :
    (TopologicalSpace.Opens.map (Work.SymQuot.DivOf.BCSquareBaseChange.towerHom (C := C) (F := F)
        (F' := F')).base).obj (Work.CurveBasics.Curve.bcOpens C F V) =
      Work.CurveBasics.Curve.bcOpens C F' V := by
  rw [show Work.CurveBasics.Curve.bcOpens C F' V =
      (TopologicalSpace.Opens.map (Curve.baseChangeFst C F').base).obj V from rfl]
  rw [show Work.CurveBasics.Curve.bcOpens C F V =
      (TopologicalSpace.Opens.map (Curve.baseChangeFst C F).base).obj V from rfl]
  rw [← TopologicalSpace.Opens.map_comp_obj]
  rw [← Scheme.Hom.comp_base, BCSquareBaseChange.towerHom_fst]

end Work.SymQuot.DivOf
