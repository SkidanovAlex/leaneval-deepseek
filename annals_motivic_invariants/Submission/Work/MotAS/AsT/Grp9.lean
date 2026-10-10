import Submission.Work.MotAS.AsT.GrpAux
import Submission.Work.MotAS.AsT.Pat11
import Submission.Work.MotAS.AsT.Pat12
import Submission.Work.MotAS.AsT.Pat13
import Submission.Work.MotAS.AsT.Pat14
import Submission.Work.MotAS.AsT.Pat15
import Submission.Work.Reflect.PolyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

namespace Work.MotAS.AsT

variable {R : Type*} [CommRing R]

/-- Group `(9, 1)` of the terms of `kleinSec`, reduced modulo `5`. -/
theorem glem9 (a b g w : R) (h5 : (5:R) = 0) (hw : w ^ 5 = w + g) (y : Fin 5 → R) :
    (a^9*(b*(∑ l, K11_4 g y l * w ^ (l:ℕ)))) + (a^9*(b*(∑ l, K12_4 g y l * w ^ (l:ℕ)))) + (a^9*(b*(∑ l, K13_4 g y l * w ^ (l:ℕ)))) + (a^9*(b*(∑ l, K14_4 g y l * w ^ (l:ℕ)))) + (a^9*(b*(∑ l, K15_4 g y l * w ^ (l:ℕ)))) = 2*a^(9:ℕ)*b*y 4^(5:ℕ) + 2*a^(9:ℕ)*b*y 3^(2:ℕ)*y 4^(3:ℕ) + 4*a^(9:ℕ)*b*y 2*y 4^(4:ℕ) + 4*a^(9:ℕ)*b*y 2*y 3^(2:ℕ)*y 4^(2:ℕ) + a^(9:ℕ)*b*y 2*y 3^(4:ℕ) + 4*a^(9:ℕ)*b*y 2^(2:ℕ)*y 4^(3:ℕ) + a^(9:ℕ)*b*y 2^(2:ℕ)*y 3^(2:ℕ)*y 4 + 4*a^(9:ℕ)*b*y 2^(3:ℕ)*y 4^(2:ℕ) + 3*a^(9:ℕ)*b*y 2^(3:ℕ)*y 3^(2:ℕ) + 4*a^(9:ℕ)*b*y 2^(4:ℕ)*y 4 + 2*a^(9:ℕ)*b*y 2^(5:ℕ) + 4*a^(9:ℕ)*b*y 1*y 3^(3:ℕ)*y 4 + 2*a^(9:ℕ)*b*y 1*y 2*y 3^(3:ℕ) + 3*a^(9:ℕ)*b*y 1^(2:ℕ)*y 4^(3:ℕ) + 3*a^(9:ℕ)*b*y 1^(2:ℕ)*y 3^(2:ℕ)*y 4 + a^(9:ℕ)*b*y 1^(2:ℕ)*y 2*y 4^(2:ℕ) + 3*a^(9:ℕ)*b*y 1^(2:ℕ)*y 2*y 3^(2:ℕ) + 4*a^(9:ℕ)*b*y 1^(2:ℕ)*y 2^(2:ℕ)*y 4 + 2*a^(9:ℕ)*b*y 1^(2:ℕ)*y 2^(3:ℕ) + 2*a^(9:ℕ)*b*y 1^(3:ℕ)*y 3*y 4 + 4*a^(9:ℕ)*b*y 1^(3:ℕ)*y 2*y 3 + a^(9:ℕ)*b*y 1^(4:ℕ)*y 4 + 2*a^(9:ℕ)*b*y 0*y 4^(4:ℕ) + a^(9:ℕ)*b*y 0*y 3^(4:ℕ) + 4*a^(9:ℕ)*b*y 0*y 2*y 3^(2:ℕ)*y 4 + 2*a^(9:ℕ)*b*y 0*y 2^(2:ℕ)*y 4^(2:ℕ) + 3*a^(9:ℕ)*b*y 0*y 2^(2:ℕ)*y 3^(2:ℕ) + 4*a^(9:ℕ)*b*y 0*y 2^(3:ℕ)*y 4 + 2*a^(9:ℕ)*b*y 0*y 2^(4:ℕ) + 2*a^(9:ℕ)*b*y 0*y 1*y 3*y 4^(2:ℕ) + a^(9:ℕ)*b*y 0*y 1*y 3^(3:ℕ) + 3*a^(9:ℕ)*b*y 0*y 1*y 2^(2:ℕ)*y 3 + 2*a^(9:ℕ)*b*y 0*y 1^(2:ℕ)*y 4^(2:ℕ) + 3*a^(9:ℕ)*b*y 0*y 1^(2:ℕ)*y 3^(2:ℕ) + a^(9:ℕ)*b*y 0*y 1^(2:ℕ)*y 2*y 4 + 3*a^(9:ℕ)*b*y 0^(2:ℕ)*y 4^(3:ℕ) + 4*a^(9:ℕ)*b*y 0^(2:ℕ)*y 3^(2:ℕ)*y 4 + a^(9:ℕ)*b*y 0^(2:ℕ)*y 2*y 4^(2:ℕ) + 2*a^(9:ℕ)*b*y 0^(2:ℕ)*y 2^(2:ℕ)*y 4 + 4*a^(9:ℕ)*b*y 0^(2:ℕ)*y 1*y 3*y 4 + 3*a^(9:ℕ)*b*y 0^(3:ℕ)*y 4^(2:ℕ) + 2*a^(9:ℕ)*b*g*y 3*y 4^(4:ℕ) + 3*a^(9:ℕ)*b*g*y 3^(3:ℕ)*y 4^(2:ℕ) + 2*a^(9:ℕ)*b*g*y 3^(5:ℕ) + 4*a^(9:ℕ)*b*g*y 2*y 3*y 4^(3:ℕ) + a^(9:ℕ)*b*g*y 2^(2:ℕ)*y 3*y 4^(2:ℕ) + 4*a^(9:ℕ)*b*g*y 2^(2:ℕ)*y 3^(3:ℕ) + 3*a^(9:ℕ)*b*g*y 2^(3:ℕ)*y 3*y 4 + 3*a^(9:ℕ)*b*g*y 1*y 4^(4:ℕ) + 2*a^(9:ℕ)*b*g*y 1*y 3^(2:ℕ)*y 4^(2:ℕ) + 3*a^(9:ℕ)*b*g*y 1*y 3^(4:ℕ) + 3*a^(9:ℕ)*b*g*y 1*y 2*y 4^(3:ℕ) + 4*a^(9:ℕ)*b*g*y 1*y 2^(2:ℕ)*y 4^(2:ℕ) + a^(9:ℕ)*b*g*y 1^(2:ℕ)*y 3*y 4^(2:ℕ) + 2*a^(9:ℕ)*b*g*y 0*y 3^(3:ℕ)*y 4 + 2*a^(9:ℕ)*b*g*y 0*y 2*y 3*y 4^(2:ℕ) + a^(9:ℕ)*b*g*y 0*y 1*y 4^(3:ℕ) + a^(9:ℕ)*b*g^(2:ℕ)*y 4^(5:ℕ) + a^(9:ℕ)*b*g^(2:ℕ)*y 3^(2:ℕ)*y 4^(3:ℕ) + 4*a^(9:ℕ)*b*g^(2:ℕ)*y 2*y 4^(4:ℕ) := by
  simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, finVal0, finVal1, finVal2, finVal3, finVal4, K11_4, K12_4, K13_4, K14_4, K15_4]
  linear_combination (norm := refl_ring1 (mod := 5))

end Work.MotAS.AsT
