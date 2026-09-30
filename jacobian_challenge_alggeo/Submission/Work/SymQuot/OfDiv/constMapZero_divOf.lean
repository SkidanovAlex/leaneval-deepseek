import Mathlib
import Submission.Work.SymQuot.SymGeomInst
import Submission.Work.SymQuot.OfDiv.constMap_divOf
import Submission.Work.CurveBasics.Divisor.deg_eq_zero_iff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.SymQuot.OfDiv

open CategoryTheory Limits AlgebraicGeometry in
theorem constMapZero_divOf {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SymQuot.CurveAffineCover C] (E : Work.SpecLin.Dv C K) (hE : E.IsEffective)
    (hd : (C.baseChange K).deg E = (0 : ℤ)) (X : Work.SpecLin.Sch K)
    {F : Type u} [Field F] [Algebra K F] (p : Work.SpecLin.FPt X F) :
    (Work.SymQuot.symGeomZero C).divOf (p ≫ Work.SymQuot.Sym.symZeroPt C X)
      = Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K K F) E := by
  change (0 : Work.SpecLin.Dv C F) = Work.SpecLin.DivBase.bc (IsScalarTower.toAlgHom K K F) E
  have hE0 : E = 0 :=
    (Work.CurveBasics.Divisor.deg_eq_zero_iff (C := C.baseChange K) hE).mp hd
  rw [hE0, Work.SpecLin.DivBase.bc_zero]

end Work.SymQuot.OfDiv
