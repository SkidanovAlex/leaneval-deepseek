import Mathlib
import Submission.Work.GroupChunk.AJSym
import Submission.Work.GroupChunk.Group
import Submission.Work.GroupChunk.Gluing.Data

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.GroupChunk.GeomProps

universe u
open CategoryTheory in
open AlgebraicGeometry in
open scoped AlgebraicGeometry in
/-- **`G D` is connected.**

The space of the glued scheme `GSch D = Over.mk (gluedHom D)` is the image of the symmetric
power `Sym^g C` under the Abel–Jacobi morphism `AJSym : Sym^g C ⟶ G D`, which is surjective
(`Input.AJSym_surjective`; this is the covering property of the charts).  As `K` is a field,
`Sym^g C` is geometrically integral over `Spec K`, hence integral, hence irreducible, hence
connected; a surjective continuous image of a connected space is connected. -/
theorem connectedSpace_G {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
    [Work.SpecLin.DivBase C] (D : Work.GroupChunk.Input C P0) :
    ConnectedSpace (Work.GroupChunk.GSch D).left := by
  exact (Work.GroupChunk.Input.AJSym_surjective D).connectedSpace (D.AJSym).left.continuous

end Work.GroupChunk.GeomProps
