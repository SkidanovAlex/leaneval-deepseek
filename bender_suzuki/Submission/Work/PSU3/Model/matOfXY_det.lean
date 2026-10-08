import Mathlib
import Submission.Work.PSU3.Model

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.Model

/-- `A(x,y)` is upper unitriangular, so its determinant is `1`. -/
theorem matOfXY_det {E : Type*} [Field E] [FrobeniusInvolution E] (x y : E) :
    (matOfXY x y).det = 1 := by
  simp [Matrix.det_fin_three]

end Work.PSU3.Model
