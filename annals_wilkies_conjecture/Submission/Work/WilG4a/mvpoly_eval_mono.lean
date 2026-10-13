import Mathlib

namespace Work.WilG4a

/-- A multivariate polynomial with coefficients in `ℕ` is monotone in its evaluation point:
if `a i ≤ b i` for every variable `i`, then `eval a p ≤ eval b p`. -/
lemma mvpoly_eval_mono_nat {σ : Type*} (p : MvPolynomial σ ℕ) {a b : σ → ℕ}
    (hab : ∀ i, a i ≤ b i) :
    MvPolynomial.eval a p ≤ MvPolynomial.eval b p := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      simpa only [MvPolynomial.eval_C] using le_rfl
  | add p q hp hq =>
      simp only [MvPolynomial.eval_add]
      exact Nat.add_le_add hp hq
  | mul_X p n hp =>
      have hn : MvPolynomial.eval a (MvPolynomial.X n) ≤ MvPolynomial.eval b (MvPolynomial.X n) := by
        simpa only [MvPolynomial.eval_X] using hab n
      simp only [MvPolynomial.eval_mul]
      exact Nat.mul_le_mul hp hn

theorem mvpoly_eval_mono (b : MvPolynomial (Fin 2) ℕ) {D j r : ℕ} (h : j ≤ r) :
    MvPolynomial.eval ![D, j] b ≤ MvPolynomial.eval ![D, r] b := by
  refine mvpoly_eval_mono_nat b ?_
  intro i
  fin_cases i <;> simp [h]

end Work.WilG4a
