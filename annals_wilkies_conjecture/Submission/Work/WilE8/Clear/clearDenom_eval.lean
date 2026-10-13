import Mathlib
import Submission.Work.WilE8.Clear

namespace Work.WilE8.Clear

/-- The elementary clearing identity in a single variable: for `w ≠ 0` and `a ≤ d`,
`w^d * (y/w)^a = y^a * w^(d-a)`. -/
private lemma mul_div_pow_clear {y w : ℝ} {a d : ℕ} (hw : w ≠ 0) (ha : a ≤ d) :
    w ^ d * (y / w) ^ a = y ^ a * w ^ (d - a) := by
  rw [div_pow, pow_sub₀ w hw ha, div_eq_mul_inv]
  ring

/-- Evaluation of a single summand of `clearDenom P` at `(y, w)`. -/
private lemma eval_clearDenom_term {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (y w : Fin n → ℝ)
    (a : Fin n →₀ ℕ) :
    MvPolynomial.eval (Sum.elim y w)
      (MvPolynomial.C (P.coeff a) * (∏ i, MvPolynomial.X (Sum.inl i) ^ a i) *
        (∏ i, MvPolynomial.X (Sum.inr i) ^ (P.totalDegree - a i)))
      = P.coeff a * (∏ i, y i ^ a i) * (∏ i, w i ^ (P.totalDegree - a i)) := by
  simp only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_prod, MvPolynomial.eval_pow,
    MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr]

theorem clearDenom_eval {n : ℕ} (P : MvPolynomial (Fin n) ℝ) (y w : Fin n → ℝ)
    (hw : ∀ i, w i ≠ 0) :
    (∏ i, w i ^ P.totalDegree) * MvPolynomial.eval (fun i => y i / w i) P
      = MvPolynomial.eval (Sum.elim y w) (Work.WilE8.clearDenom P) := by
  have hR : MvPolynomial.eval (Sum.elim y w) (Work.WilE8.clearDenom P)
      = ∑ a ∈ P.support, P.coeff a * (∏ i, y i ^ a i) *
          (∏ i, w i ^ (P.totalDegree - a i)) := by
    rw [Work.WilE8.clearDenom, map_sum]
    exact Finset.sum_congr rfl (fun a _ => eval_clearDenom_term P y w a)
  have hLHS : MvPolynomial.eval (fun i => y i / w i) P
      = ∑ a ∈ P.support, P.coeff a * ∏ i, (y i / w i) ^ a i := by
    rw [MvPolynomial.eval_eq']
  rw [hR, hLHS, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  have hdeg : ∀ i, a i ≤ P.totalDegree := fun i =>
    (MvPolynomial.le_degreeOf_of_mem_support i ha).trans
      (MvPolynomial.degreeOf_le_totalDegree P i)
  have hkey : (∏ i, w i ^ P.totalDegree) * (∏ i, (y i / w i) ^ a i)
      = (∏ i, y i ^ a i) * (∏ i, w i ^ (P.totalDegree - a i)) := by
    calc (∏ i, w i ^ P.totalDegree) * (∏ i, (y i / w i) ^ a i)
        = ∏ i, w i ^ P.totalDegree * (y i / w i) ^ a i :=
          (Finset.prod_mul_distrib).symm
      _ = ∏ i, y i ^ a i * w i ^ (P.totalDegree - a i) :=
          Finset.prod_congr rfl (fun i _ => mul_div_pow_clear (hw i) (hdeg i))
      _ = (∏ i, y i ^ a i) * (∏ i, w i ^ (P.totalDegree - a i)) :=
          Finset.prod_mul_distrib
  calc (∏ i, w i ^ P.totalDegree) * (P.coeff a * ∏ i, (y i / w i) ^ a i)
      = P.coeff a * ((∏ i, w i ^ P.totalDegree) * ∏ i, (y i / w i) ^ a i) := by ring
    _ = P.coeff a * ((∏ i, y i ^ a i) * (∏ i, w i ^ (P.totalDegree - a i))) := by rw [hkey]
    _ = P.coeff a * (∏ i, y i ^ a i) * (∏ i, w i ^ (P.totalDegree - a i)) := by ring

end Work.WilE8.Clear
