import Mathlib
import Submission.Work.HP.BridgeDefs

/-!
# Homogeneity of `formEval`

`formEval d n a` is a sum of monomials of total degree `d`, hence homogeneous of degree `d`.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset

namespace Work.HP

lemma prod_pow_mul_eq {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (c : R)
    (x : ι → R) (e : ι → ℕ) :
    (∏ i, (c * x i) ^ e i) = c ^ (∑ i, e i) * ∏ i, x i ^ e i := by
  rw [show (∏ i, (c * x i) ^ e i) = (∏ i, c ^ e i) * ∏ i, x i ^ e i by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => (mul_pow _ _ _)]
  rw [← Finset.prod_pow_eq_pow_sum]

/-- `formEval d n a` is homogeneous of degree `d`. -/
lemma formEval_mul {R : Type*} [CommRing R] (d n : ℕ) (a : Mon d n → ℤ) (c : R)
    (x : Fin (n + 1) → R) :
    formEval d n a (fun i => c * x i) = c ^ d * formEval d n a x := by
  simp only [formEval, veronese]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [prod_pow_mul_eq, m.2]
  ring

/-- Evaluation of the adelic/exponential map commutes with the homogeneity scaling. -/
lemma aeval_formOf_mul {R : Type*} [CommRing R] [Algebra ℚ R] (d n : ℕ) (a : Mon d n → ℤ)
    (c : R) (x : Fin (n + 1) → R) :
    aeval (fun i => c * x i) (formOf d n a) = c ^ d * aeval x (formOf d n a) := by
  rw [aeval_formOf, aeval_formOf, formEval_mul]

end Work.HP
