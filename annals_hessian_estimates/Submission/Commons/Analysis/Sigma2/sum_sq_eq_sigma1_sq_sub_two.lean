import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Commons.Analysis.Sigma2.pairSum_sq

namespace Commons.Analysis.Sigma2

open scoped BigOperators in
theorem sum_sq_eq_sigma1_sq_sub_two (lam : Fin 4 → ℝ)
    (hσ2 : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1) :
    (∑ i : Fin 4, (lam i) ^ 2) = (∑ i : Fin 4, lam i) ^ 2 - 2 := by
  have hpair := pairSum_sq (a := lam)
  have hmain : (∑ i : Fin 4, lam i) ^ 2 = (∑ i : Fin 4, (lam i) ^ 2) + 2 := by
    calc
      (∑ i : Fin 4, lam i) ^ 2
          = (∑ i : Fin 4, (lam i) ^ 2) +
            2 * (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) := hpair
      _ = (∑ i : Fin 4, (lam i) ^ 2) + 2 * 1 := by rw [hσ2]
      _ = (∑ i : Fin 4, (lam i) ^ 2) + 2 := by ring
  linarith

end Commons.Analysis.Sigma2