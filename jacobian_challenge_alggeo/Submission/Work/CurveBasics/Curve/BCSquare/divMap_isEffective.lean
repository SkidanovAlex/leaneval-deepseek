import Mathlib
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.Curve.BCSquare.ordAt_fieldMap_of_not_isClosed

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.Curve.BCSquare

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry in
universe u in
theorem divMap_isEffective {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') {D : Curve.Div C}
    (hD : Curve.Div.IsEffective D) : Curve.Div.IsEffective (S.divMap D) := by
  intro Q'
  rw [Curve.BCSquare.divMap_apply]
  simp only [Curve.BCSquare.divMapCoeff]
  split
  · rename_i h
    refine mul_nonneg (hD _) ?_
    rw [Curve.BCSquare.ramIdx, dite_eq_left h]
    exact ordAt_fieldMap_nonneg_of_mem_range S Q' ⟨_, rfl⟩
  · exact le_refl 0

end Work.CurveBasics.Curve.BCSquare
