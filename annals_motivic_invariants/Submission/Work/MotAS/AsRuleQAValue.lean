import Mathlib
import Submission.Work.MotAS.AsRuleQADecomp
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace Work.MotAS

open MvPolynomial Polynomial

variable {K : Type} [Field K] [CharP K 5]

theorem asPhiP_ne_zero (a b g : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hd : a ^ 2 - a * b - b ^ 2 ≠ 0) : asPhiP a b g ≠ 0 := by
  intro hzero
  have hs0 : asPhiP_cE0 a b g = 0 := by
    have hh := congrArg (fun p : Polynomial K => p.coeff 0) hzero
    rw [asPhiP_coeff0] at hh
    rw [asPhiP_c0_exp] at hh
    simpa using hh
  have hs1 : asPhiP_cE1 a b g = 0 := by
    have hh := congrArg (fun p : Polynomial K => p.coeff 1) hzero
    rw [asPhiP_coeff1] at hh
    rw [asPhiP_c1_exp] at hh
    simpa using hh
  have hs2 : asPhiP_cE2 a b g = 0 := by
    have hh := congrArg (fun p : Polynomial K => p.coeff 2) hzero
    rw [asPhiP_coeff2] at hh
    rw [asPhiP_c2_exp] at hh
    simpa using hh
  have hs3 : asPhiP_cE3 a b g = 0 := by
    have hh := congrArg (fun p : Polynomial K => p.coeff 3) hzero
    rw [asPhiP_coeff3] at hh
    rw [asPhiP_c3_exp] at hh
    simpa using hh
  have hs4 : asPhiP_cE4 a b g = 0 := by
    have hh := congrArg (fun p : Polynomial K => p.coeff 4) hzero
    rw [asPhiP_coeff4] at hh
    rw [asPhiP_c4_exp] at hh
    simpa using hh
  have h5 : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have hab : a - 3 * b ≠ 0 := by
    intro h
    apply hd
    have hsq : (a - 3 * b) ^ 2 = a ^ 2 - a * b - b ^ 2 := by
      linear_combination (norm := first | refl_ring1 | ring1) (-(a * b) + 2 * b ^ 2) * h5
    rw [h] at hsq
    simpa using hsq.symm
  have key : asW1 a b g * asPhiP_cE0 a b g + asW2 a b g * asPhiP_cE1 a b g
      + asW3 a b g * asPhiP_cE2 a b g + asW4 a b g * asPhiP_cE3 a b g
      + asW5 a b g * asPhiP_cE4 a b g ≠ 0 := by
    rw [asBezout]
    exact mul_ne_zero (pow_ne_zero _ hab) (mul_ne_zero (pow_ne_zero _ ha) hb)
  rw [hs0, hs1, hs2, hs3, hs4] at key
  simp only [mul_zero, zero_add, add_zero] at key
  exact key rfl

end Work.MotAS
