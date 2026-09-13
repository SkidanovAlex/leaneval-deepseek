import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Commons.Analysis.Sigma2

open scoped BigOperators in
theorem largest_ge_average_four (lam : Fin 4 → ℝ)
    (hmono : ∀ ⦃i j : Fin 4⦄, i ≤ j → lam j ≤ lam i) :
    (∑ i : Fin 4, lam i) / 4 ≤ lam 0 := by
  have hle : (∑ i : Fin 4, lam i) ≤ 4 * lam 0 := by
    calc
      (∑ i : Fin 4, lam i) ≤ ∑ _i : Fin 4, lam 0 := by
        exact Finset.sum_le_sum fun i _hi => hmono (Fin.zero_le i)
      _ = 4 * lam 0 := by simp
  have h4 : (0 : ℝ) < 4 := by norm_num
  exact (div_le_iff₀ h4).2 (by simpa [mul_comm] using hle)

end Commons.Analysis.Sigma2