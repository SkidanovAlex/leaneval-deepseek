import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.ZMod.Defs
import Submission.Commons.Analysis.Sigma2.sum_sq_eq_sigma1_sq_sub_two

namespace Commons.Analysis.Sigma2

/-! For an eigenvalue tuple in dimension 4 with sigma_2 = 1: `sum_i (sigma_1 - lam i)^2 = 3 * sigma_1^2 - 2`.  This is `|Df|^2 = (n-1) sigma_1^2 - 2` from Step 4 of the proof of the almost-Jacobi inequality (Proposition 2.1 of Shankar--Yuan) specialized to n = 4: expand the square, use `sum_i lam i = sigma_1` and `sum_i (lam i)^2 = sigma_1^2 - 2`. -/
open scoped BigOperators in
theorem linearized_grad_sq (lam : Fin 4 → ℝ)
    (hσ2 : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1) :
    (∑ i : Fin 4, ((∑ j : Fin 4, lam j) - lam i) ^ 2) =
      3 * (∑ i : Fin 4, lam i) ^ 2 - 2 := by
  simp [Fin.sum_univ_four] at *
  nlinarith [hσ2]

end Commons.Analysis.Sigma2