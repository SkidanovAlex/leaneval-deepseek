import Mathlib
import Submission.Work.SymQuot.OfDiv
import Submission.Work.SymQuot.SymGeomInst

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.SymQuot.OfDiv

open CategoryTheory Limits AlgebraicGeometry in
theorem constMap_divOf {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SymQuot.CurveAffineCover C] {n : ℕ} [NeZero n] (E : Work.SpecLin.Dv C K)
    (hE : E.IsEffective) (hd : (C.baseChange K).deg E = n) (X : Work.SpecLin.Sch K)
    {F : Type u} [Field F] [Algebra K F] (p : Work.SpecLin.FPt X F) :
    Work.SymQuot.DivOf.divOf F (p ≫ Work.SymQuot.Sym.constMap C n E hE hd X)
      = Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K K F) E := by
  -- `constMap` is the structure map `X ⟶ Spec K` followed by the point `Sym.ofDiv`;
  -- composing with `p : Spec F ⟶ X` gives the base change of that point to `F`.
  have hconst : p ≫ Work.SymQuot.Sym.constMap C n E hE hd X =
      Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K K F)
        (Work.SymQuot.Sym.ofDiv C n E hE hd) := by
    rw [Work.SymQuot.Sym.constMap, Work.SpecLin.RPt.map, ← Category.assoc]
    congr 1
    apply Over.OverMorphism.ext
    simp only [Over.homMk_left, Over.comp_left]
    rw [Over.w p]
    rfl
  rw [hconst, Work.SymQuot.DivOf.divOf_map, Work.SymQuot.Sym.divOf_ofDiv]

end Work.SymQuot.OfDiv
