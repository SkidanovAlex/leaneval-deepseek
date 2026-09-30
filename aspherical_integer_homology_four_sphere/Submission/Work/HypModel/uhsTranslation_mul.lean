import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HypModel

/-- The horospherical translations of the upper half space model compose: the matrix of the
translation by `b + c` is the product of the matrices of the translations by `b` and by `c`.
Both sides depend only on the first three coordinates of `b` and `c`. -/
theorem uhsTranslation_mul (b c : E4) :
    uhsTranslation (b + c) = uhsTranslation b * uhsTranslation c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uhsTranslation, Matrix.mul_apply, Fin.sum_univ_five] <;> ring

end Work.HypModel
