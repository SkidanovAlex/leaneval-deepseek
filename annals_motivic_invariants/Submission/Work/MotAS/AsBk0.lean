import Submission.Work.MotAS.AsDefs
import Submission.Work.MotAS.AsMo10
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.MotAS.AS5

variable {R : Type*} [CommRing R]

theorem blk0 (g w : R) (h5 : (5 : R) = 0) (hw : w ^ 5 = w + g) (y : Fin 5 → R) :
    Lsc0 (Xv5 w y) = Sc0 g y := by
  simp only [Lsc0, Xv5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  rw [mono_1_1_1_1_1 g w h5 hw y]
  simp only [V_1_1_1_1_1, Sc0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  norm_num
  linear_combination (norm := first | refl_ring1 | ring1) (g^(3:ℕ)*y 3*y 4^(4:ℕ) + g^(2:ℕ)*y 0*y 3^(2:ℕ)*y 4^(2:ℕ) + g^(2:ℕ)*y 1^(2:ℕ)*y 4^(3:ℕ) + g^(2:ℕ)*y 1*y 2*y 3*y 4^(2:ℕ) + g^(2:ℕ)*y 2^(3:ℕ)*y 4^(2:ℕ) + g^(2:ℕ)*y 2^(2:ℕ)*y 3^(2:ℕ)*y 4 + g^(2:ℕ)*y 2*y 3^(4:ℕ) + g*y 0^(2:ℕ)*y 1*y 4^(2:ℕ) + g*y 0^(2:ℕ)*y 2*y 3*y 4 + g*y 0^(2:ℕ)*y 3^(3:ℕ) + g*y 0*y 1^(2:ℕ)*y 3*y 4 + g*y 0*y 1*y 2^(2:ℕ)*y 4 + g*y 0*y 1*y 2*y 3^(2:ℕ) + g*y 0*y 1*y 4^(3:ℕ) + g*y 0*y 2*y 3*y 4^(2:ℕ) + g*y 0*y 3^(3:ℕ)*y 4 + g*y 1^(3:ℕ)*y 3^(2:ℕ) + g*y 1^(2:ℕ)*y 2^(2:ℕ)*y 3 + g*y 1^(2:ℕ)*y 3*y 4^(2:ℕ) + g*y 1*y 2^(4:ℕ) + g*y 1*y 4^(4:ℕ) + y 0^(4:ℕ)*y 4 + y 0^(3:ℕ)*y 2^(2:ℕ) + y 0^(2:ℕ)*y 1^(2:ℕ)*y 2 + y 0^(2:ℕ)*y 2*y 3^(2:ℕ) + y 0^(2:ℕ)*y 4^(3:ℕ) + y 0*y 1^(4:ℕ) + y 0*y 1^(2:ℕ)*y 2*y 4 + y 0*y 2^(2:ℕ)*y 4^(2:ℕ) + y 0*y 2*y 3^(2:ℕ)*y 4 + y 0*y 3^(4:ℕ)) * h5

end Work.MotAS.AS5
