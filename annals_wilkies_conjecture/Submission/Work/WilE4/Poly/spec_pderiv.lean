import Mathlib
import Submission.Work.WilE4.Poly

set_option autoImplicit false
noncomputable section

namespace Work.WilE4.Poly

/-- Multiplying a multivariate polynomial on the right by a constant polynomial multiplies its
coefficients by that constant. -/
lemma mv_coeff_mul_C {σ R : Type*} [CommSemiring R] (p : MvPolynomial σ R) (a : R)
    (m : σ →₀ ℕ) :
    (p * MvPolynomial.C a).coeff m = p.coeff m * a := by
  rw [mul_comm p (MvPolynomial.C a), MvPolynomial.coeff_C_mul]
  exact mul_comm a (p.coeff m)

/-- `finSuccEquiv` turns the partial derivative in the first variable of `Fin (n+1)` into the
ordinary derivative of the associated polynomial. -/
lemma finSuccEquiv_pderiv_zero {n : ℕ} (Q : MvPolynomial (Fin (n+1)) ℝ) :
    MvPolynomial.finSuccEquiv ℝ n (MvPolynomial.pderiv 0 Q) =
      (MvPolynomial.finSuccEquiv ℝ n Q).derivative := by
  apply Polynomial.ext
  intro i
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, MvPolynomial.coeff_pderiv,
    Polynomial.coeff_derivative]
  have hcons : Finsupp.cons i m + Finsupp.single (0 : Fin (n+1)) 1 =
      Finsupp.cons (i+1) m := by
    ext j
    induction j using Fin.cases with
    | zero => simp
    | succ k => simp [Finsupp.cons_succ]
  have hcasti : (↑i + 1 : MvPolynomial (Fin n) ℝ) = MvPolynomial.C ((i:ℝ) + 1) := by
    rw [← MvPolynomial.C_eq_coe_nat i, ← MvPolynomial.C_1, ← map_add]
  rw [hcasti, mv_coeff_mul_C, MvPolynomial.finSuccEquiv_coeff_coeff, Finsupp.cons_zero, hcons]

/-- The specialization of the derivative in the last variable is the derivative. -/
theorem spec_pderiv {m : ℕ} (P : MvPolynomial (Fin (m+1)) ℝ) (x : Fin m → ℝ) :
    spec (MvPolynomial.pderiv (Fin.last m) P) x = (spec P x).derivative := by
  unfold spec
  rw [← MvPolynomial.pderiv_rename (rot m).injective (Fin.last m) P, rot_last]
  rw [finSuccEquiv_pderiv_zero]
  rw [Polynomial.derivative_map]

end Work.WilE4.Poly
