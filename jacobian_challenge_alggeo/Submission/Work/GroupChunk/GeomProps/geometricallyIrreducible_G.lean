import Mathlib
import Submission.Work.GroupChunk.AJSym
import Submission.Work.GroupChunk.Group
import Submission.Work.GroupChunk.Gluing.Data

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.GroupChunk.GeomProps

set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits AlgebraicGeometry in
/-- **Geometric irreducibility is preserved by a surjective morphism.**  If `g : X ⟶ Y` is a
surjective morphism of schemes and the composite `g ≫ h : X ⟶ S` is geometrically irreducible
over `S`, then so is `h : Y ⟶ S`.

Indeed, for every field `L` and point `y : Spec L ⟶ S` the base change
`X ×_S Spec L ⟶ Y ×_S Spec L` of `g` is surjective, and `X ×_S Spec L` is irreducible, so its
image `Y ×_S Spec L` is irreducible. -/
theorem geometricallyIrreducible_of_surjective {X Y S : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ S)
    [GeometricallyIrreducible (g ≫ h)] [Surjective g] :
    GeometricallyIrreducible h := by
  refine ⟨?_⟩
  rw [geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  haveI : IrreducibleSpace ↥(Limits.pullback (g ≫ h) y) :=
    pullback_of_geometrically (GeometricallyIrreducible.geometrically_irreducibleSpace
      (f := g ≫ h)) K y
  -- the base change of `g` along `pullback.fst h y`, pasted with the pullback of `g ≫ h`:
  let ψ : Limits.pullback (g ≫ h) y ⟶ Limits.pullback h y :=
    (pullbackRightPullbackFstIso h y g).inv ≫ pullback.snd g (pullback.fst h y)
  exact Function.Surjective.irreducibleSpace ψ.continuous ψ.surjective

open CategoryTheory in
open AlgebraicGeometry in
open scoped AlgebraicGeometry in
theorem geometricallyIrreducible_G {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
    [Work.SpecLin.DivBase C] (D : Work.GroupChunk.Input C P0) :
    GeometricallyIrreducible (Work.GroupChunk.GSch D).hom := by
  haveI : Work.GroupChunk.Input C P0 := D
  -- the Abel–Jacobi morphism `Sym^g C ⟶ G D` is surjective and `Sym^g C` is geometrically
  -- irreducible over `K`, so `G D` is geometrically irreducible over `K`
  have hw : (D.AJSym).left ≫ (Work.GroupChunk.GSch D).hom = (D.Sym D.g).hom :=
    Over.Hom.w D.AJSym
  haveI : GeometricallyIrreducible ((D.AJSym).left ≫ (Work.GroupChunk.GSch D).hom) :=
    hw.symm ▸ inferInstance
  haveI : Surjective (D.AJSym).left := ⟨Work.GroupChunk.Input.AJSym_surjective D⟩
  exact geometricallyIrreducible_of_surjective (D.AJSym).left (Work.GroupChunk.GSch D).hom

end Work.GroupChunk.GeomProps
