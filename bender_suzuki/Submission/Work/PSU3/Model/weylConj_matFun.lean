import Mathlib
import Submission.Work.PSU3.Model
import Submission.Work.PSU3.FMap

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.Model

open Matrix

/-- The Weyl conjugation formula for the unitriangular matrices `A(x,y)`: if
`y ≠ 0` and `y + y^q = x·x^q` (the Hermitian relation satisfied by elements of
`SZ`), then
`J · A(x,y) · J = weylFactor x y · J · A(x/y, 1/y)`.

This is the entrywise computation underlying `weylConj_matFun`. -/
theorem weylConj_matOfXY {E : Type*} [Field E] [FrobeniusInvolution E] [CharP E 2]
    (x y : E) (hy : y ≠ 0) (hherm : y + σE y = x * σE x) :
    weylMat * matOfXY x y * weylMat = weylFactor x y * weylMat * matOfXY (x / y) y⁻¹ := by
  have hσy : σE y ≠ 0 := fun h => hy (σE.injective (by rw [h, map_zero]))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, matOfXY, weylFactor, weylMat, hermMat]
  all_goals field_simp
  · rw [zero_mul, one_add_one_eq_two, CharTwo.two_eq_zero, mul_zero]
  · rw [zero_mul, zero_mul, ← hherm,
      show σE y + (y + σE y) + y = (σE y + y) + (σE y + y) by ring,
      CharTwo.add_self_eq_zero]
  · rw [mul_comm (σE x) x, ← hherm, CharTwo.add_cancel_right]
  · rw [zero_mul, one_add_one_eq_two, CharTwo.two_eq_zero, mul_zero]

theorem weylConj_matFun {E : Type*} [Field E] [FrobeniusInvolution E] [CharP E 2]
    (p : SZ E) (hp : p ≠ 1) :
    weylMat * matFun p * weylMat = weylFactor p.x p.y * weylMat * matFun (SZ.fMap p hp) := by
  have h := weylConj_matOfXY p.x p.y (SZ.y_ne_zero_of_ne_one hp) p.herm
  simpa [matFun, SZ.fMap_x, SZ.fMap_y] using h

end Work.PSU3.Model
