import Mathlib
import Submission.Work.MotK.CensusFibre.kleinM_alt
import Submission.Work.TwistModel.adjugate_eq_skewPfaffian5

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.CensusFibre

/-- **The determinant of the principal `4 × 4` minor of `M(x)` is the square of the corresponding
Pfaffian quadric.**  `Work.MotK.kleinMat a b x` is the Klein matrix `M(x)` (`Work.MotK.kleinM`
packaged as a Mathlib matrix, see `Work.MotK.kleinMat` in `MotK/CensusFibre/kleinM_alt`), and
`Work.MotK.kleinP a b x k` is its `k`-th Pfaffian.

Route: `Work.MotK.kleinMat_transpose` and `Work.MotK.kleinMat_diag` give the skew-symmetry and
vanishing diagonal, so `Work.TwistModel.det_submatrix_eq_skewPfaffian5_mul` gives
`det = Matrix.skewPfaffian5 (kleinMat a b x) k * Matrix.skewPfaffian5 (kleinMat a b x) k`; it
remains to check `(Matrix.skewPfaffian5 (kleinMat a b x) k)^2 = (kleinP a b x k)^2`, a computation
(`fin_cases k`, unfold `Matrix.skewPfaffian5`/`Matrix.pfaffian4`, then `ring`); the two sides agree
up to the sign of `kleinP a b x k = ± Matrix.skewPfaffian5 (kleinMat a b x) k` (for `k = 0` the sign
is `+`). -/
theorem det_submatrix_kleinMat_eq_sq {R : Type*} [CommRing R] (a b : R) (x : Fin 5 → R)
    (k : Fin 5) :
    ((Work.MotK.kleinMat a b x).submatrix k.succAbove k.succAbove).det
      = (Work.MotK.kleinP a b x k) ^ 2 := by
  -- Every `4 × 4` minor of an alternating matrix is a product of two Pfaffians; here the two
  -- Pfaffians are the same one, so the minor is a square.
  rw [Work.TwistModel.det_submatrix_eq_skewPfaffian5_mul (Work.MotK.kleinMat a b x)
    (Work.MotK.kleinMat_transpose a b x) (Work.MotK.kleinMat_diag a b x) k k]
  -- It remains to identify `skewPfaffian5 (kleinMat a b x) k` with `± kleinP a b x k`; since only
  -- the square survives, it suffices to expand both sides and compare.
  fin_cases k <;>
    (rw [Work.TwistModel.Matrix.skewPfaffian5, Work.TwistModel.Matrix.pfaffian4]
     simp +decide [Matrix.submatrix_apply, Work.MotK.kleinM, Work.MotK.kleinM0, Work.MotK.kleinM1,
       Work.MotK.kleinM2, Work.MotK.kleinM3, Work.MotK.kleinM4, Work.MotK.kleinP,
       Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2, Work.MotK.kleinP3,
       Work.MotK.kleinP4, Fin.succAbove]
     ring)

end Work.MotK.CensusFibre
