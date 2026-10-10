import Mathlib
import Submission.Work.MotAS.CensusAS2
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.MotAS

open MvPolynomial

/-! ## The explicit chart form of the target ruling quintic `sdualAS2` -/

theorem sdualAS2_explicit {K : Type*} [CommRing K] (a b g : K) :
    Work.MotAS.sdualAS2 a b g =
      (C a ^(10:ℕ) * C g + -C a ^(5:ℕ) * C b ^(5:ℕ) * C g + -C b ^(10:ℕ) * C g) * X 0 ^(5:ℕ)
      + (-C a ^(10:ℕ) + C a ^(5:ℕ) * C b ^(5:ℕ) + C b ^(10:ℕ)) * X 0 ^(4:ℕ)
      + (-C a ^(9:ℕ) * C b + -C a ^(8:ℕ) * C b ^(2:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C a ^(7:ℕ) * C b ^(3:ℕ) + (2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(7:ℕ) + C a ^(2:ℕ) * C b ^(8:ℕ) + -C a * C b ^(9:ℕ)) * X 0 ^(3:ℕ) * X 1 * X 2
      + ((-2 : MvPolynomial (Fin 3) K) * C a ^(10:ℕ) * C g + (2 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(5:ℕ) * C g + (2 : MvPolynomial (Fin 3) K) * C b ^(10:ℕ) * C g) * X 0 ^(3:ℕ) * X 2 ^(2:ℕ)
      + ((2 : MvPolynomial (Fin 3) K) * C a ^(9:ℕ) * C b + (2 : MvPolynomial (Fin 3) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + -C a ^(7:ℕ) * C b ^(3:ℕ) + C a ^(6:ℕ) * C b ^(4:ℕ) + -C a ^(4:ℕ) * C b ^(6:ℕ) + -C a ^(3:ℕ) * C b ^(7:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + (2 : MvPolynomial (Fin 3) K) * C a * C b ^(9:ℕ)) * X 0 ^(2:ℕ) * X 1 ^(3:ℕ)
      + (-C a ^(10:ℕ) * C g + C a ^(5:ℕ) * C b ^(5:ℕ) * C g + C b ^(10:ℕ) * C g) * X 0 ^(2:ℕ) * X 1 ^(2:ℕ) * X 2
      + (-C a ^(9:ℕ) * C b + (-2 : MvPolynomial (Fin 3) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + -C a ^(7:ℕ) * C b ^(3:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + C a ^(3:ℕ) * C b ^(7:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + C a * C b ^(9:ℕ)) * X 0 ^(2:ℕ) * X 1 * X 2 ^(2:ℕ)
      + (-C a ^(10:ℕ) + C a ^(5:ℕ) * C b ^(5:ℕ) + C b ^(10:ℕ)) * X 0 ^(2:ℕ) * X 1
      + ((2 : MvPolynomial (Fin 3) K) * C a ^(10:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C a ^(9:ℕ) * C b + (-2 : MvPolynomial (Fin 3) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + C a ^(7:ℕ) * C b ^(3:ℕ) + -C a ^(6:ℕ) * C b ^(4:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(5:ℕ) + C a ^(4:ℕ) * C b ^(6:ℕ) + C a ^(3:ℕ) * C b ^(7:ℕ) + (2 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C a * C b ^(9:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C b ^(10:ℕ)) * X 0 ^(2:ℕ) * X 2 ^(2:ℕ)
      + (-C a ^(10:ℕ) * C g + C a ^(5:ℕ) * C b ^(5:ℕ) * C g + C b ^(10:ℕ) * C g) * X 0 * X 1 ^(4:ℕ)
      + (C a ^(10:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C a ^(9:ℕ) * C b + (-2 : MvPolynomial (Fin 3) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + C a ^(7:ℕ) * C b ^(3:ℕ) + -C a ^(6:ℕ) * C b ^(4:ℕ) + -C a ^(5:ℕ) * C b ^(5:ℕ) + C a ^(4:ℕ) * C b ^(6:ℕ) + C a ^(3:ℕ) * C b ^(7:ℕ) + (2 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C a * C b ^(9:ℕ) + -C b ^(10:ℕ)) * X 0 * X 1 ^(2:ℕ) * X 2
      + (C a ^(9:ℕ) * C b + (2 : MvPolynomial (Fin 3) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + -C a ^(7:ℕ) * C b ^(3:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + (2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + -C a ^(3:ℕ) * C b ^(7:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + C a * C b ^(9:ℕ)) * X 0 * X 1 * X 2 ^(3:ℕ)
      + ((-2 : MvPolynomial (Fin 3) K) * C a ^(10:ℕ) * C g + (2 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(5:ℕ) * C g + (2 : MvPolynomial (Fin 3) K) * C b ^(10:ℕ) * C g) * X 0 * X 1 * X 2 ^(2:ℕ)
      + (C a ^(10:ℕ) * C g + (-2 : MvPolynomial (Fin 3) K) * C a ^(9:ℕ) * C b * C g + (-2 : MvPolynomial (Fin 3) K) * C a ^(8:ℕ) * C b ^(2:ℕ) * C g + C a ^(7:ℕ) * C b ^(3:ℕ) * C g + -C a ^(6:ℕ) * C b ^(4:ℕ) * C g + -C a ^(5:ℕ) * C b ^(5:ℕ) * C g + C a ^(4:ℕ) * C b ^(6:ℕ) * C g + C a ^(3:ℕ) * C b ^(7:ℕ) * C g + (2 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(8:ℕ) * C g + (-2 : MvPolynomial (Fin 3) K) * C a * C b ^(9:ℕ) * C g + -C b ^(10:ℕ) * C g) * X 0 * X 2 ^(4:ℕ)
      + ((-2 : MvPolynomial (Fin 3) K) * C a ^(9:ℕ) * C b + C a ^(8:ℕ) * C b ^(2:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C a ^(7:ℕ) * C b ^(3:ℕ) + C a ^(6:ℕ) * C b ^(4:ℕ) + C a ^(4:ℕ) * C b ^(6:ℕ) + (2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(7:ℕ) + C a ^(2:ℕ) * C b ^(8:ℕ) + (2 : MvPolynomial (Fin 3) K) * C a * C b ^(9:ℕ)) * X 0 * X 2 ^(3:ℕ)
      + (C a ^(10:ℕ) + -C a ^(5:ℕ) * C b ^(5:ℕ) + -C b ^(10:ℕ)) * X 0 * X 2
      + (C a ^(10:ℕ) * C g ^(2:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C a ^(9:ℕ) * C b + (2 : MvPolynomial (Fin 3) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + C a ^(7:ℕ) * C b ^(3:ℕ) + C a ^(6:ℕ) * C b ^(4:ℕ) + -C a ^(5:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) + C a ^(4:ℕ) * C b ^(6:ℕ) + -C a ^(3:ℕ) * C b ^(7:ℕ) + (2 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + (2 : MvPolynomial (Fin 3) K) * C a * C b ^(9:ℕ) + -C b ^(10:ℕ) * C g ^(2:ℕ)) * X 1 ^(5:ℕ)
      + (C a ^(10:ℕ) + (2 : MvPolynomial (Fin 3) K) * C a ^(9:ℕ) * C b + (2 : MvPolynomial (Fin 3) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + -C a ^(7:ℕ) * C b ^(3:ℕ) + C a ^(6:ℕ) * C b ^(4:ℕ) + -C a ^(5:ℕ) * C b ^(5:ℕ) + -C a ^(4:ℕ) * C b ^(6:ℕ) + -C a ^(3:ℕ) * C b ^(7:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + (2 : MvPolynomial (Fin 3) K) * C a * C b ^(9:ℕ) + -C b ^(10:ℕ)) * X 1 ^(4:ℕ)
      + (C a ^(9:ℕ) * C b + (-2 : MvPolynomial (Fin 3) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + C a ^(7:ℕ) * C b ^(3:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + (2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + C a ^(3:ℕ) * C b ^(7:ℕ) + (2 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + C a * C b ^(9:ℕ)) * X 1 ^(3:ℕ) * X 2 ^(2:ℕ)
      + (C a ^(10:ℕ) * C g + -C a ^(5:ℕ) * C b ^(5:ℕ) * C g + -C b ^(10:ℕ) * C g) * X 1 ^(3:ℕ) * X 2
      + (-C a ^(9:ℕ) * C b * C g + -C a ^(8:ℕ) * C b ^(2:ℕ) * C g + (-2 : MvPolynomial (Fin 3) K) * C a ^(7:ℕ) * C b ^(3:ℕ) * C g + (2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(4:ℕ) * C g + (-2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(6:ℕ) * C g + (-2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(7:ℕ) * C g + C a ^(2:ℕ) * C b ^(8:ℕ) * C g + -C a * C b ^(9:ℕ) * C g) * X 1 ^(2:ℕ) * X 2 ^(3:ℕ)
      + (-C a ^(9:ℕ) * C b + (-2 : MvPolynomial (Fin 3) K) * C a ^(8:ℕ) * C b ^(2:ℕ) + -C a ^(7:ℕ) * C b ^(3:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + C a ^(3:ℕ) * C b ^(7:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(8:ℕ) + C a * C b ^(9:ℕ)) * X 1 ^(2:ℕ) * X 2 ^(2:ℕ)
      + ((-2 : MvPolynomial (Fin 3) K) * C a ^(10:ℕ) + (2 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(5:ℕ) + (2 : MvPolynomial (Fin 3) K) * C b ^(10:ℕ)) * X 1 ^(2:ℕ)
      + (-C a ^(10:ℕ) * C g ^(2:ℕ) + C a ^(9:ℕ) * C b + C a ^(8:ℕ) * C b ^(2:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C a ^(7:ℕ) * C b ^(3:ℕ) + (2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + C a ^(5:ℕ) * C b ^(5:ℕ) * C g ^(2:ℕ) + (2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + (2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(7:ℕ) + C a ^(2:ℕ) * C b ^(8:ℕ) + -C a * C b ^(9:ℕ) + C b ^(10:ℕ) * C g ^(2:ℕ)) * X 1 * X 2 ^(4:ℕ)
      + (-C a ^(10:ℕ) + C a ^(5:ℕ) * C b ^(5:ℕ) + C b ^(10:ℕ)) * X 1 * X 2 ^(2:ℕ)
      + (C a ^(10:ℕ) * C g ^(3:ℕ) + (2 : MvPolynomial (Fin 3) K) * C a ^(9:ℕ) * C b * C g + (2 : MvPolynomial (Fin 3) K) * C a ^(8:ℕ) * C b ^(2:ℕ) * C g + C a ^(7:ℕ) * C b ^(3:ℕ) * C g + -C a ^(6:ℕ) * C b ^(4:ℕ) * C g + -C a ^(5:ℕ) * C b ^(5:ℕ) * C g ^(3:ℕ) + -C a ^(4:ℕ) * C b ^(6:ℕ) * C g + -C a ^(3:ℕ) * C b ^(7:ℕ) * C g + (2 : MvPolynomial (Fin 3) K) * C a ^(2:ℕ) * C b ^(8:ℕ) * C g + (-2 : MvPolynomial (Fin 3) K) * C a * C b ^(9:ℕ) * C g + -C b ^(10:ℕ) * C g ^(3:ℕ)) * X 2 ^(5:ℕ)
      + (-C a ^(10:ℕ) + -C a ^(9:ℕ) * C b + C a ^(8:ℕ) * C b ^(2:ℕ) + (2 : MvPolynomial (Fin 3) K) * C a ^(7:ℕ) * C b ^(3:ℕ) + (2 : MvPolynomial (Fin 3) K) * C a ^(6:ℕ) * C b ^(4:ℕ) + C a ^(5:ℕ) * C b ^(5:ℕ) + (-2 : MvPolynomial (Fin 3) K) * C a ^(4:ℕ) * C b ^(6:ℕ) + (2 : MvPolynomial (Fin 3) K) * C a ^(3:ℕ) * C b ^(7:ℕ) + -C a ^(2:ℕ) * C b ^(8:ℕ) + -C a * C b ^(9:ℕ) + C b ^(10:ℕ)) * X 2 ^(4:ℕ)
      + ((-2 : MvPolynomial (Fin 3) K) * C a ^(10:ℕ) * C g + (2 : MvPolynomial (Fin 3) K) * C a ^(5:ℕ) * C b ^(5:ℕ) * C g + (2 : MvPolynomial (Fin 3) K) * C b ^(10:ℕ) * C g) * X 2 ^(3:ℕ)
      + (C a ^(10:ℕ) + -C a ^(5:ℕ) * C b ^(5:ℕ) + -C b ^(10:ℕ)) := by
  rw [Work.MotAS.sdualAS2]
  simp only [Work.MotAS.kleinSecDualAS, Work.MotAS.tchart, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  refl_ring1


end Work.MotAS
