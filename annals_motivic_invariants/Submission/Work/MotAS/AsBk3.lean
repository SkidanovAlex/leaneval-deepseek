import Submission.Work.MotAS.AsDefs
import Submission.Work.MotAS.AsMo5
import Submission.Work.MotAS.AsMo6
import Submission.Work.MotAS.AsMo7
import Submission.Work.MotAS.AsMo20
import Submission.Work.MotAS.AsMo21
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

theorem blk3 (g w : R) (h5 : (5 : R) = 0) (hw : w ^ 5 = w + g) (y : Fin 5 → R) :
    Lsc3 (Xv5 w y) = Sc3 g y := by
  simp only [Lsc3, Xv5, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  rw [mono_0_0_2_1_2 g w h5 hw y, mono_0_2_1_2_0 g w h5 hw y, mono_1_2_0_0_2 g w h5 hw y, mono_2_0_0_2_1 g w h5 hw y, mono_2_1_2_0_0 g w h5 hw y]
  simp only [V_0_0_2_1_2, V_0_2_1_2_0, V_1_2_0_0_2, V_2_0_0_2_1, V_2_1_2_0_0, Sc3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  norm_num
  linear_combination (norm := refl_ring1 (mod := 5))

end Work.MotAS.AS5
