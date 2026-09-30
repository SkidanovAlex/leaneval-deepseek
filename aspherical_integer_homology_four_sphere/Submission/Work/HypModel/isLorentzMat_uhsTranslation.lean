import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HypModel

open scoped Matrix InnerProductSpace
open Matrix

/-- The horospherical translation `x ↦ x + b` of the upper half space model is a Lorentz
transformation: its matrix `AᵀJA = J` lies in the Lorentz group and its `(4,4)` entry is positive.

Both conditions are direct computations.  For the first, the columns of `uhsTranslation b`
(each a vector of `ℝ⁵`, with the Lorentz form evaluated through `J`) are an orthonormal basis for
`⟨·,·⟩` of the same signature `(4,1)`: columns `0,1,2` have square `1`, column `3` has square `1`,
column `4` has square `-1`, and distinct columns are orthogonal -- the elementary identity behind
`x ↦ x + b` preserving the metric.  The second condition is
`(uhsTranslation b) 4 4 = 1 + (b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2) / 2 > 0`. -/
theorem isLorentzMat_uhsTranslation (b : E4) : IsLorentzMat (uhsTranslation b) := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [uhsTranslation, Matrix.mul_apply, Fin.sum_univ_five, J] <;> ring
  · simp [uhsTranslation]
    positivity

end Work.HypModel
