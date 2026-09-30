import Mathlib
import Submission.Work.SymQuot.BaseChange.exists_symBaseChangeIso
import Submission.Work.SpecLin.Conventions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.BaseChange

universe u

open CategoryTheory Limits AlgebraicGeometry in
/-- **The `F`-points of the base change `X_L` are the `F`-points of `X`.**

For a field extension `L/K` and a field `F` which is an `L`-algebra and such that
`K → L → F` is a scalar tower (`Spec F ⟶ Spec K` factors through `Spec L`), the
`F`-valued points of the base change `X_L = X ×_K Spec L` are in canonical bijection
with the `F`-valued points of `X`.

The bijection is the adjunction `Over.map f ⊣ Over.pullback f` for
`f = Spec L ⟶ Spec K`: a morphism `Spec F ⟶ X_L` over `Spec L` corresponds to a
morphism `Spec F ⟶ X` over `Spec K`, and the two structure morphisms of `Spec F`
agree precisely because `K → L → F` is a scalar tower. -/
theorem ptsBaseChange {K : Type u} [Field K] (X : Work.SpecLin.Sch K) {L : Type u} [Field L]
    [Algebra K L] {F : Type u} [Field F] [Algebra K F] [Algebra L F] [IsScalarTower K L F] :
    Nonempty (Work.SpecLin.FPt ((Over.pullback (Work.CurveBasics.Curve.specMap K L)).obj X) F ≃
      Work.SpecLin.FPt X F) := by
  -- `Spec F ⟶ Spec K` evaluated on the two structure morphisms agrees, by the scalar tower.
  have hhom : Spec.map (CommRingCat.ofHom (algebraMap L F)) ≫
      Work.CurveBasics.Curve.specMap K L = Spec.map (CommRingCat.ofHom (algebraMap K F)) := by
    rw [Work.CurveBasics.Curve.specMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    ext x
    simpa using (IsScalarTower.algebraMap_apply K L F x).symm
  -- hence `Spec F`, regarded as a scheme over `Spec L`, is also `Spec F` over `Spec K`.
  let α : (Over.map (Work.CurveBasics.Curve.specMap K L)).obj
        (Work.SpecLin.specOf (K := L) F) ≅ Work.SpecLin.specOf (K := K) F :=
    Over.isoMk (Iso.refl _) (by simpa using hhom.symm)
  refine ⟨((Over.mapPullbackAdj (Work.CurveBasics.Curve.specMap K L)).homEquiv
    (Work.SpecLin.specOf (K := L) F) X).symm.trans (α.homCongr (Iso.refl X))⟩

end Work.SymQuot.BaseChange
