import Mathlib

namespace Work.LinnikBurgess

lemma cftEvalDivX (G : Polynomial ℤ) (x : ℤ) :
    G.eval x = G.eval 0 + x * G.divX.eval x ∧ G.divX.eval 0 = G.derivative.eval 0 := by
  constructor
  · have h := congrArg (fun p : Polynomial ℤ => Polynomial.eval x p) (Polynomial.X_mul_divX_add G)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C] at h
    rw [Polynomial.coeff_zero_eq_eval_zero] at h
    rw [← h]; ring
  · rw [← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coeff_zero_eq_eval_zero]
    simp only [Polynomial.coeff_divX, Polynomial.coeff_derivative, zero_add, Nat.cast_zero, mul_one]

end Work.LinnikBurgess
