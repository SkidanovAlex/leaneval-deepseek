import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HypModel

/-- The Möbius transformation of the upper half space induced by the Lorentz matrix `uhsRotation O`
is the Euclidean rotation `x ↦ O x` of the horizontal coordinates with the height fixed:
`mobius (uhsRotation O) q = euclidAction O 0 q` for `q` in the upper half space.

This is a direct computation.  With `s = q 3`, the point `hypOfUHS q` has coordinates
`(q 0/s, q 1/s, q 2/s, (‖q‖²−1)/(2s), (‖q‖²+1)/(2s))`; applying `uhsRotation O` rotates only the
first three coordinates, and afterwards `P 4 − P 3 = ((‖q‖²+1) − (‖q‖²−1))/(2s) = s⁻¹`, so
`uhsOfHyp` multiplies back by `s`, leaving the Euclidean rotation and the unchanged height. -/
theorem mobius_uhsRotation {O : Matrix (Fin 3) (Fin 3) ℝ} {q : E4} (hq : 0 < q 3) :
    mobius (uhsRotation O) q = euclidAction O 0 q := by
  have h : ((‖q‖ ^ 2 + 1) / (2 * q 3) - (‖q‖ ^ 2 - 1) / (2 * q 3))⁻¹ = q 3 := by
    have h' : (‖q‖ ^ 2 + 1) / (2 * q 3) - (‖q‖ ^ 2 - 1) / (2 * q 3) = (q 3)⁻¹ := by
      field_simp
      ring
    rw [h', inv_inv]
  ext i
  fin_cases i <;>
    simp [mobius, uhsOfHyp, hypOfUHS, euclidAction, uhsRotation, Matrix.mulVec, dotProduct,
      Fin.sum_univ_five, Fin.sum_univ_three, h]
  · field_simp
  · field_simp
  · field_simp

end Work.HypModel
