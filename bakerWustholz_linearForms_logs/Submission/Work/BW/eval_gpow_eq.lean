import Mathlib
import Submission.Work.BW.eval_ptTheta_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Evaluation of a polynomial at the point `(t·a, y₁^t, …, y_N^t)` of `G = G_a × G_m^N`
(the `t`-th power of the point `(a, y₁, …, y_N)`), expanded along the monomials of `f`.
The proof is the same computation as the existing sibling
`Submission.Work.BW.eval_ptTheta_eq` (the case `a = 1`), i.e. `MvPolynomial.eval_eq'`
followed by `Fin.prod_univ_succ`, `Finset.prod_pow` and `pow_mul`. -/
theorem eval_gpow_eq {N : ℕ} (f : MvPolynomial (Fin (N + 1)) ℂ) (y : Fin N → ℂ) (a : ℂ) (t : ℕ) :
    MvPolynomial.eval (Fin.cons ((t : ℂ) * a) (fun i : Fin N => y i ^ t)) f =
      ∑ m ∈ f.support, (∏ i : Fin N, y i ^ (m i.succ)) ^ t *
        (f.coeff m * a ^ (m 0) * (t : ℂ) ^ (m 0)) := by
  rw [MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have h1 : (∏ i : Fin N, y i ^ d i.succ) ^ t = ∏ i : Fin N, y i ^ (d i.succ * t) := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by rw [pow_mul]
  have h2 : (∏ x : Fin N, (y x ^ t) ^ d x.succ) = ∏ i : Fin N, y i ^ (d i.succ * t) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, mul_comm]
  rw [h1, h2]
  ring

end Work.BW
