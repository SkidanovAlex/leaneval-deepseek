import Mathlib
import Submission.Work.RTOwed.reflWallDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

/-- The diagonal Lorentz matrix `diagNeg5 (f3to5 t)` acts on a vector as `Q ↦ fun i => ±Q i`,
negating exactly the `t`-th coordinate (`t : Fin 3`). -/
lemma diagNeg5_f3to5_mulVec (t : Fin 3) (Q : Work.HypModel.V5) :
    Matrix.mulVec (Work.RTOwed.diagNeg5 (Work.FoldInst.f3to5 t)) Q
      = fun i => (if i = Work.FoldInst.f3to5 t then -1 else 1) * Q i := by
  ext i
  rw [Work.RTOwed.diagNeg5, Matrix.mulVec_diagonal]

/-- Negating one of the first three coordinates of a vector of `ℝ⁵` and then reading off the
upper half space coordinates is the same as reading off the coordinates first and reflecting the
corresponding horizontal coordinate.  This holds for *every* `Q`, in particular for a point of the
upper sheet, where `uhsOfHyp` is the inverse of the hyperboloid chart. -/
theorem uhsOfHyp_diagNeg5 (t : Fin 3) (Q : Work.HypModel.V5) :
    Work.HypModel.uhsOfHyp (Matrix.mulVec (Work.RTOwed.diagNeg5 (Work.FoldInst.f3to5 t)) Q)
      = Work.RTOwed.reflCoord t (Work.HypModel.uhsOfHyp Q) := by
  rw [diagNeg5_f3to5_mulVec]
  ext j
  fin_cases t <;> fin_cases j <;>
    simp [Work.RTOwed.reflCoord_apply, Work.HypModel.uhsOfHyp]

end Work.RTOwed
