import Mathlib
import Submission.Work.BW.zeroest_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem eval_ptTheta_eq {N : ℕ} (P : MvPolynomial (Fin (N + 1)) ℂ) (θ : Fin N → ℂ) (t : ℕ) :
    MvPolynomial.eval (ptTheta θ t) P =
      ∑ a ∈ P.support, (∏ i : Fin N, θ i ^ (a i.succ)) ^ t *
        (P.coeff a * (t : ℂ) ^ (a 0)) := by
  rw [MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Fin.prod_univ_succ]
  simp only [ptTheta, Fin.cons_zero, Fin.cons_succ]
  have h2 : (∏ x : Fin N, (θ x ^ t) ^ d x.succ) = ∏ i : Fin N, θ i ^ (d i.succ * t) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, mul_comm]
  have h1 : (∏ i : Fin N, θ i ^ d i.succ) ^ t = ∏ i : Fin N, θ i ^ (d i.succ * t) := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by rw [pow_mul]
  rw [h1, h2]
  ring

end Work.BW
