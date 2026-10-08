import Mathlib
import Submission.Work.PSU3.Model

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.Model

theorem matOfXY_mul {E : Type*} [Field E] [FrobeniusInvolution E] (x y u v : E) :
    matOfXY x y * matOfXY u v = matOfXY (x + u) (y + v + x * σE u) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, matOfXY] <;> ring

end Work.PSU3.Model
