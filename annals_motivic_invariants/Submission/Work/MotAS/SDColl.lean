import Submission.Work.MotAS.ASData
import Submission.Work.MotAS.SDDefs
import Submission.Work.Reflect.PolyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.MotAS.SDStage

variable {R : Type*} [CommRing R]

theorem Xk_eq_asN (w : R) (z : Fin 5 → R) (k : Fin 5) :
    (∑ j : Fin 5, Work.MotAS.asN w k j * z j) = Xk w z k := by
  fin_cases k <;>
  · simp only [Fin.sum_univ_five, Work.MotAS.asN, Matrix.of_apply, Xk, Xv, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.val_two, Fin.reduceFinMk]
    norm_num
    first | refl_ring1 | ring

theorem kleinSecDual_collect (a b : R) (x : Fin 5 → R) :
    Work.MotK.kleinSecDual a b x = -(a)^(5:ℕ)*(b)^(5:ℕ) * ((x 4)^(5:ℕ)) + -(a)^(5:ℕ)*(b)^(5:ℕ) * ((x 3)^(5:ℕ)) + (2*(a)^(7:ℕ)*(b)^(3:ℕ)+-(a)^(2:ℕ)*(b)^(8:ℕ)) * (x 2*(x 3)^(3:ℕ)*x 4) + (-(a)^(9:ℕ)*b+3*(a)^(4:ℕ)*(b)^(6:ℕ)) * ((x 2)^(2:ℕ)*x 3*(x 4)^(2:ℕ)) + -(a)^(5:ℕ)*(b)^(5:ℕ) * ((x 2)^(5:ℕ)) + (-3*(a)^(6:ℕ)*(b)^(4:ℕ)+-a*(b)^(9:ℕ)) * (x 1*(x 3)^(2:ℕ)*(x 4)^(2:ℕ)) + ((a)^(8:ℕ)*(b)^(2:ℕ)+2*(a)^(3:ℕ)*(b)^(7:ℕ)) * (x 1*x 2*(x 4)^(3:ℕ)) + (2*(a)^(7:ℕ)*(b)^(3:ℕ)+-(a)^(2:ℕ)*(b)^(8:ℕ)) * (x 1*(x 2)^(3:ℕ)*x 3) + (-(a)^(9:ℕ)*b+3*(a)^(4:ℕ)*(b)^(6:ℕ)) * ((x 1)^(2:ℕ)*x 2*(x 3)^(2:ℕ)) + (-3*(a)^(6:ℕ)*(b)^(4:ℕ)+-a*(b)^(9:ℕ)) * ((x 1)^(2:ℕ)*(x 2)^(2:ℕ)*x 4) + ((a)^(8:ℕ)*(b)^(2:ℕ)+2*(a)^(3:ℕ)*(b)^(7:ℕ)) * ((x 1)^(3:ℕ)*x 3*x 4) + -(a)^(5:ℕ)*(b)^(5:ℕ) * ((x 1)^(5:ℕ)) + (2*(a)^(7:ℕ)*(b)^(3:ℕ)+-(a)^(2:ℕ)*(b)^(8:ℕ)) * (x 0*x 3*(x 4)^(3:ℕ)) + (-3*(a)^(6:ℕ)*(b)^(4:ℕ)+-a*(b)^(9:ℕ)) * (x 0*(x 2)^(2:ℕ)*(x 3)^(2:ℕ)) + ((a)^(8:ℕ)*(b)^(2:ℕ)+2*(a)^(3:ℕ)*(b)^(7:ℕ)) * (x 0*(x 2)^(3:ℕ)*x 4) + ((a)^(8:ℕ)*(b)^(2:ℕ)+2*(a)^(3:ℕ)*(b)^(7:ℕ)) * (x 0*x 1*(x 3)^(3:ℕ)) + (((a)^(10:ℕ)+-6*(a)^(5:ℕ)*(b)^(5:ℕ))+-(b)^(10:ℕ)) * (x 0*x 1*x 2*x 3*x 4) + (-(a)^(9:ℕ)*b+3*(a)^(4:ℕ)*(b)^(6:ℕ)) * (x 0*(x 1)^(2:ℕ)*(x 4)^(2:ℕ)) + (2*(a)^(7:ℕ)*(b)^(3:ℕ)+-(a)^(2:ℕ)*(b)^(8:ℕ)) * (x 0*(x 1)^(3:ℕ)*x 2) + (-(a)^(9:ℕ)*b+3*(a)^(4:ℕ)*(b)^(6:ℕ)) * ((x 0)^(2:ℕ)*(x 3)^(2:ℕ)*x 4) + (-3*(a)^(6:ℕ)*(b)^(4:ℕ)+-a*(b)^(9:ℕ)) * ((x 0)^(2:ℕ)*x 2*(x 4)^(2:ℕ)) + (-(a)^(9:ℕ)*b+3*(a)^(4:ℕ)*(b)^(6:ℕ)) * ((x 0)^(2:ℕ)*x 1*(x 2)^(2:ℕ)) + (-3*(a)^(6:ℕ)*(b)^(4:ℕ)+-a*(b)^(9:ℕ)) * ((x 0)^(2:ℕ)*(x 1)^(2:ℕ)*x 3) + ((a)^(8:ℕ)*(b)^(2:ℕ)+2*(a)^(3:ℕ)*(b)^(7:ℕ)) * ((x 0)^(3:ℕ)*x 2*x 3) + (2*(a)^(7:ℕ)*(b)^(3:ℕ)+-(a)^(2:ℕ)*(b)^(8:ℕ)) * ((x 0)^(3:ℕ)*x 1*x 4) + -(a)^(5:ℕ)*(b)^(5:ℕ) * ((x 0)^(5:ℕ)) := by
  simp only [Work.MotK.kleinSecDual]
  first | refl_ring1 | ring

end Work.MotAS.SDStage
