import Mathlib

namespace Work.WilC4aP

lemma eval_prod_X_sub_C_eq_zero_iff {m : ℕ} (a : Fin m → ℂ) (w : ℂ) :
    ((∏ j : Fin m, (Polynomial.X - Polynomial.C (a j))).eval w = 0) ↔ ∃ j, w = a j := by
  rw [Polynomial.eval_prod]
  simp only [Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]

end Work.WilC4aP
