import Submission.Work.MotAS.AsDefs
import Submission.Work.MotAS.AsMo0
import Submission.Work.MotAS.AsMo10
import Submission.Work.MotAS.AsMo14
import Submission.Work.MotAS.AsMo15
import Submission.Work.MotAS.AsMo24
import Submission.Work.MotAS.AsMo25
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

theorem blk5 (g w : R) (h5 : (5 : R) = 0) (hw : w ^ 5 = w + g) (y : Fin 5 → R) :
    Lsc5 (Xv5 w y) = Sc5 g y := by
  simp only [Lsc5, Xv5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  rw [mono_0_0_0_0_5 g w h5 hw y, mono_0_0_0_5_0 g w h5 hw y, mono_0_0_5_0_0 g w h5 hw y, mono_0_5_0_0_0 g w h5 hw y, mono_1_1_1_1_1 g w h5 hw y, mono_5_0_0_0_0 g w h5 hw y]
  simp only [V_0_0_0_0_5, V_0_0_0_5_0, V_0_0_5_0_0, V_0_5_0_0_0, V_1_1_1_1_1, V_5_0_0_0_0, Sc5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  norm_num
  linear_combination (norm := first | refl_ring1 | ring1) (2*g^(4:ℕ)*y 4^(5:ℕ) - 4*g^(3:ℕ)*w*y 4^(5:ℕ) + 2*g^(3:ℕ)*y 3^(5:ℕ) + 13*g^(3:ℕ)*y 3*y 4^(4:ℕ) - 2*g^(3:ℕ)*y 4^(5:ℕ) - g^(2:ℕ)*w^(2:ℕ)*y 4^(5:ℕ) - 3*g^(2:ℕ)*w*y 3^(5:ℕ) - 2*g^(2:ℕ)*w*y 4^(5:ℕ) + 3*g^(2:ℕ)*y 0*y 2*y 4^(3:ℕ) + 13*g^(2:ℕ)*y 0*y 3^(2:ℕ)*y 4^(2:ℕ) + 10*g^(2:ℕ)*y 1^(2:ℕ)*y 4^(3:ℕ) + 10*g^(2:ℕ)*y 1*y 2*y 3*y 4^(2:ℕ) + 3*g^(2:ℕ)*y 1*y 3^(3:ℕ)*y 4 + 2*g^(2:ℕ)*y 2^(5:ℕ) + 10*g^(2:ℕ)*y 2^(3:ℕ)*y 4^(2:ℕ) + 13*g^(2:ℕ)*y 2^(2:ℕ)*y 3^(2:ℕ)*y 4 + 13*g^(2:ℕ)*y 2*y 3^(4:ℕ) + 3*g^(2:ℕ)*y 2*y 4^(4:ℕ) - 2*g^(2:ℕ)*y 3^(5:ℕ) - 2*g^(2:ℕ)*y 4^(5:ℕ) - 4*g*w^(3:ℕ)*y 4^(5:ℕ) - 3*g*w^(2:ℕ)*y 3^(5:ℕ) - 2*g*w^(2:ℕ)*y 4^(5:ℕ) - 2*g*w*y 2^(5:ℕ) - 2*g*w*y 3^(5:ℕ) - 2*g*w*y 4^(5:ℕ) + 13*g*y 0^(2:ℕ)*y 1*y 4^(2:ℕ) + 10*g*y 0^(2:ℕ)*y 2*y 3*y 4 + 10*g*y 0^(2:ℕ)*y 3^(3:ℕ) + 10*g*y 0*y 1^(2:ℕ)*y 3*y 4 + 10*g*y 0*y 1*y 2^(2:ℕ)*y 4 + 10*g*y 0*y 1*y 2*y 3^(2:ℕ) + 10*g*y 0*y 1*y 4^(3:ℕ) + 3*g*y 0*y 2^(3:ℕ)*y 3 + 10*g*y 0*y 2*y 3*y 4^(2:ℕ) + 13*g*y 0*y 3^(3:ℕ)*y 4 + 2*g*y 1^(5:ℕ) + 3*g*y 1^(3:ℕ)*y 2*y 4 + 10*g*y 1^(3:ℕ)*y 3^(2:ℕ) + 13*g*y 1^(2:ℕ)*y 2^(2:ℕ)*y 3 + 13*g*y 1^(2:ℕ)*y 3*y 4^(2:ℕ) + 13*g*y 1*y 2^(4:ℕ) + 6*g*y 1*y 2^(2:ℕ)*y 4^(2:ℕ) + 3*g*y 1*y 2*y 3^(2:ℕ)*y 4 + 3*g*y 1*y 3^(4:ℕ) + 13*g*y 1*y 4^(4:ℕ) - 2*g*y 2^(5:ℕ) - 2*g*y 3^(5:ℕ) - 2*g*y 4^(5:ℕ) - w^(4:ℕ)*y 4^(5:ℕ) - w^(3:ℕ)*y 3^(5:ℕ) - 2*w^(3:ℕ)*y 4^(5:ℕ) - w^(2:ℕ)*y 2^(5:ℕ) - 2*w^(2:ℕ)*y 3^(5:ℕ) - 2*w^(2:ℕ)*y 4^(5:ℕ) - w*y 1^(5:ℕ) - 2*w*y 2^(5:ℕ) - 2*w*y 3^(5:ℕ) - 2*w*y 4^(5:ℕ) + 2*y 0^(5:ℕ) + 13*y 0^(4:ℕ)*y 4 + 3*y 0^(3:ℕ)*y 1*y 3 + 10*y 0^(3:ℕ)*y 2^(2:ℕ) + 3*y 0^(3:ℕ)*y 4^(2:ℕ) + 13*y 0^(2:ℕ)*y 1^(2:ℕ)*y 2 + 6*y 0^(2:ℕ)*y 1*y 3*y 4 + 3*y 0^(2:ℕ)*y 2^(2:ℕ)*y 4 + 13*y 0^(2:ℕ)*y 2*y 3^(2:ℕ) + 13*y 0^(2:ℕ)*y 4^(3:ℕ) + 13*y 0*y 1^(4:ℕ) + 13*y 0*y 1^(2:ℕ)*y 2*y 4 + 6*y 0*y 1^(2:ℕ)*y 3^(2:ℕ) + 3*y 0*y 1*y 2^(2:ℕ)*y 3 + 3*y 0*y 1*y 3*y 4^(2:ℕ) + 3*y 0*y 2^(4:ℕ) + 10*y 0*y 2^(2:ℕ)*y 4^(2:ℕ) + 13*y 0*y 2*y 3^(2:ℕ)*y 4 + 13*y 0*y 3^(4:ℕ) + 3*y 0*y 4^(4:ℕ) - 2*y 1^(5:ℕ) - 2*y 2^(5:ℕ) - 2*y 3^(5:ℕ) - y 4^(5:ℕ)) * h5

end Work.MotAS.AS5
