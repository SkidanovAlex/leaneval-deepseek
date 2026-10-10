import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.AsDefs
import Submission.Work.MotAS.AsBk0
import Submission.Work.MotAS.AsBk1
import Submission.Work.MotAS.AsBk2
import Submission.Work.MotAS.AsBk3
import Submission.Work.MotAS.AsBk4
import Submission.Work.MotAS.AsBk5
import Submission.Work.MotAS.AsBk6
import Submission.Work.MotAS.AsBk7
import Submission.Work.MotAS.AsBk8
import Submission.Work.MotAS.AsBk9
import Submission.Work.MotAS.AsBk10
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

namespace Work.MotAS

theorem AsTransportSstage {R : Type*} [CommRing R] (a b g w : R) (h5 : (5 : R) = 0)
    (hw : w ^ 5 = w + g) (y : Fin 5 → R) :
    Work.MotK.kleinSec a b (fun i => ∑ j, Work.MotAS.asM w i j * y j)
      = Work.MotAS.kleinSecAS a b g y := by
  have hx0 : (∑ j, Work.MotAS.asM w 0 j * y j) = AS5.Xv5 w y 0 := by
    simp only [Work.MotAS.asM, Matrix.of_apply, Fin.sum_univ_five, AS5.Xv5, AS5.Zv0, AS5.Zv1, AS5.Zv2, AS5.Zv3, AS5.Zv4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    norm_num
    first | refl_ring1 | ring
  have hx1 : (∑ j, Work.MotAS.asM w 1 j * y j) = AS5.Xv5 w y 1 := by
    simp only [Work.MotAS.asM, Matrix.of_apply, Fin.sum_univ_five, AS5.Xv5, AS5.Zv0, AS5.Zv1, AS5.Zv2, AS5.Zv3, AS5.Zv4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    norm_num
    linear_combination (norm := first | refl_ring1 | ring1) (w^(2:ℕ)*y 4) * h5
  have hx2 : (∑ j, Work.MotAS.asM w 2 j * y j) = AS5.Xv5 w y 2 := by
    simp only [Work.MotAS.asM, Matrix.of_apply, Fin.sum_univ_five, AS5.Xv5, AS5.Zv0, AS5.Zv1, AS5.Zv2, AS5.Zv3, AS5.Zv4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    norm_num
    linear_combination (norm := first | refl_ring1 | ring1) (w^(3:ℕ)*y 4 + w^(2:ℕ)*y 3 + 4*w^(2:ℕ)*y 4 + 2*w*y 3 + 6*w*y 4 + y 3 + 3*y 4) * h5
  have hx3 : (∑ j, Work.MotAS.asM w 3 j * y j) = AS5.Xv5 w y 3 := by
    simp only [Work.MotAS.asM, Matrix.of_apply, Fin.sum_univ_five, AS5.Xv5, AS5.Zv0, AS5.Zv1, AS5.Zv2, AS5.Zv3, AS5.Zv4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    norm_num
    linear_combination (norm := first | refl_ring1 | ring1) (2*w^(3:ℕ)*y 4 + w^(2:ℕ)*y 3 + 10*w^(2:ℕ)*y 4 + w*y 2 + 5*w*y 3 + 21*w*y 4 + y 2 + 5*y 3 + 16*y 4) * h5
  have hx4 : (∑ j, Work.MotAS.asM w 4 j * y j) = AS5.Xv5 w y 4 := by
    simp only [Work.MotAS.asM, Matrix.of_apply, Fin.sum_univ_five, AS5.Xv5, AS5.Zv0, AS5.Zv1, AS5.Zv2, AS5.Zv3, AS5.Zv4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
    norm_num
    linear_combination (norm := first | refl_ring1 | ring1) (3*w^(3:ℕ)*y 4 + 2*w^(2:ℕ)*y 3 + 19*w^(2:ℕ)*y 4 + w*y 2 + 9*w*y 3 + 51*w*y 4 + 3*y 2 + 12*y 3 + 51*y 4) * h5
  have hx : (fun i => ∑ j, Work.MotAS.asM w i j * y j) = AS5.Xv5 w y := by
    funext i
    fin_cases i
    · exact hx0
    · exact hx1
    · exact hx2
    · exact hx3
    · exact hx4
  have hs : Work.MotK.kleinSec a b (AS5.Xv5 w y) = a^(0:ℕ)*b^(10:ℕ)*(AS5.Lsc0 (AS5.Xv5 w y)) + a^(1:ℕ)*b^(9:ℕ)*(AS5.Lsc1 (AS5.Xv5 w y)) + a^(2:ℕ)*b^(8:ℕ)*(AS5.Lsc2 (AS5.Xv5 w y)) + a^(3:ℕ)*b^(7:ℕ)*(AS5.Lsc3 (AS5.Xv5 w y)) + a^(4:ℕ)*b^(6:ℕ)*(AS5.Lsc4 (AS5.Xv5 w y)) + a^(5:ℕ)*b^(5:ℕ)*(AS5.Lsc5 (AS5.Xv5 w y)) + a^(6:ℕ)*b^(4:ℕ)*(AS5.Lsc6 (AS5.Xv5 w y)) + a^(7:ℕ)*b^(3:ℕ)*(AS5.Lsc7 (AS5.Xv5 w y)) + a^(8:ℕ)*b^(2:ℕ)*(AS5.Lsc8 (AS5.Xv5 w y)) + a^(9:ℕ)*b^(1:ℕ)*(AS5.Lsc9 (AS5.Xv5 w y)) + a^(10:ℕ)*b^(0:ℕ)*(AS5.Lsc10 (AS5.Xv5 w y)) := by
    simp only [Work.MotK.kleinSec, AS5.Lsc0, AS5.Lsc1, AS5.Lsc2, AS5.Lsc3, AS5.Lsc4, AS5.Lsc5, AS5.Lsc6, AS5.Lsc7, AS5.Lsc8, AS5.Lsc9, AS5.Lsc10]
    norm_num
    first | refl_ring1 | ring
  have hb : a^(0:ℕ)*b^(10:ℕ)*(AS5.Lsc0 (AS5.Xv5 w y)) + a^(1:ℕ)*b^(9:ℕ)*(AS5.Lsc1 (AS5.Xv5 w y)) + a^(2:ℕ)*b^(8:ℕ)*(AS5.Lsc2 (AS5.Xv5 w y)) + a^(3:ℕ)*b^(7:ℕ)*(AS5.Lsc3 (AS5.Xv5 w y)) + a^(4:ℕ)*b^(6:ℕ)*(AS5.Lsc4 (AS5.Xv5 w y)) + a^(5:ℕ)*b^(5:ℕ)*(AS5.Lsc5 (AS5.Xv5 w y)) + a^(6:ℕ)*b^(4:ℕ)*(AS5.Lsc6 (AS5.Xv5 w y)) + a^(7:ℕ)*b^(3:ℕ)*(AS5.Lsc7 (AS5.Xv5 w y)) + a^(8:ℕ)*b^(2:ℕ)*(AS5.Lsc8 (AS5.Xv5 w y)) + a^(9:ℕ)*b^(1:ℕ)*(AS5.Lsc9 (AS5.Xv5 w y)) + a^(10:ℕ)*b^(0:ℕ)*(AS5.Lsc10 (AS5.Xv5 w y)) = a^(0:ℕ)*b^(10:ℕ)*(AS5.Sc0 g y) + a^(1:ℕ)*b^(9:ℕ)*(AS5.Sc1 g y) + a^(2:ℕ)*b^(8:ℕ)*(AS5.Sc2 g y) + a^(3:ℕ)*b^(7:ℕ)*(AS5.Sc3 g y) + a^(4:ℕ)*b^(6:ℕ)*(AS5.Sc4 g y) + a^(5:ℕ)*b^(5:ℕ)*(AS5.Sc5 g y) + a^(6:ℕ)*b^(4:ℕ)*(AS5.Sc6 g y) + a^(7:ℕ)*b^(3:ℕ)*(AS5.Sc7 g y) + a^(8:ℕ)*b^(2:ℕ)*(AS5.Sc8 g y) + a^(9:ℕ)*b^(1:ℕ)*(AS5.Sc9 g y) + a^(10:ℕ)*b^(0:ℕ)*(AS5.Sc10 g y) := by
    rw [AS5.blk0 g w h5 hw y, AS5.blk1 g w h5 hw y, AS5.blk2 g w h5 hw y, AS5.blk3 g w h5 hw y, AS5.blk4 g w h5 hw y, AS5.blk5 g w h5 hw y, AS5.blk6 g w h5 hw y, AS5.blk7 g w h5 hw y, AS5.blk8 g w h5 hw y, AS5.blk9 g w h5 hw y, AS5.blk10 g w h5 hw y]
  have ht : a^(0:ℕ)*b^(10:ℕ)*(AS5.Sc0 g y) + a^(1:ℕ)*b^(9:ℕ)*(AS5.Sc1 g y) + a^(2:ℕ)*b^(8:ℕ)*(AS5.Sc2 g y) + a^(3:ℕ)*b^(7:ℕ)*(AS5.Sc3 g y) + a^(4:ℕ)*b^(6:ℕ)*(AS5.Sc4 g y) + a^(5:ℕ)*b^(5:ℕ)*(AS5.Sc5 g y) + a^(6:ℕ)*b^(4:ℕ)*(AS5.Sc6 g y) + a^(7:ℕ)*b^(3:ℕ)*(AS5.Sc7 g y) + a^(8:ℕ)*b^(2:ℕ)*(AS5.Sc8 g y) + a^(9:ℕ)*b^(1:ℕ)*(AS5.Sc9 g y) + a^(10:ℕ)*b^(0:ℕ)*(AS5.Sc10 g y) = Work.MotAS.kleinSecAS a b g y := by
    simp only [AS5.Sc0, AS5.Sc1, AS5.Sc2, AS5.Sc3, AS5.Sc4, AS5.Sc5, AS5.Sc6, AS5.Sc7, AS5.Sc8, AS5.Sc9, AS5.Sc10, Work.MotAS.kleinSecAS]
    first | refl_ring1 | ring
  rw [hx, hs, hb, ht]

end Work.MotAS
