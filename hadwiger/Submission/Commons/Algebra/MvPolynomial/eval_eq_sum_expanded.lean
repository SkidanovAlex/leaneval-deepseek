import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Real.Basic

namespace Commons.Algebra.MvPolynomial

theorem eval_eq_sum_expanded (n : ℕ) (w : Fin n → ℝ) (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.eval w p = ∑ m ∈ p.support, p.coeff m * (∏ i : Fin n, (w i) ^ (m i)) := by
  exact MvPolynomial.eval_eq' w p

end Commons.Algebra.MvPolynomial