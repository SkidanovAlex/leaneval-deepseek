import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HypModel

/-- The horospherical translation `x ↦ x + b` of the upper half space model fixes the ideal point
`∞`: the null vector `infty = (0,0,0,1,1)` is an eigenvector of `uhsTranslation b` with eigenvalue
`1`. -/
theorem uhsTranslation_mulVec_infty (b : E4) : (uhsTranslation b).mulVec infty = infty := by
  ext i
  fin_cases i <;> simp [uhsTranslation, infty, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
  all_goals ring

end Work.HypModel
