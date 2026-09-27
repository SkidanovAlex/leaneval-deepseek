import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

/-- The Heisenberg shape `uparShape p q s = [[1,p,q],[0,1,0],[0,s,1]]` factors as the product of
the three root-group elements `u_{02}(q)`, `u_{01}(p - q s)` and `u_{21}(s)`.

This is EKL's decomposition of a generic element of `U_(01)` into the three root directions;
the `(p - q s)` in the middle slot is exactly what makes the `(0,1)` entry come out as `p`
after the `(0,2)`-entry `q` is transported by the `(2,1)`-shear `s`. -/
theorem uparShape_decomp (p q s : ℝ) :
    uij h02 q * uij h01 (p - q * s) * uij h21 s = uparShape p q s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uij, uparShape, Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.single_apply]

end Work.EKLC8Core
