import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Sigma2

/-! Positivity of the eigenvalues `f_i = sigma_1 - lambda_i` of the linearized operator `F = sigma_1 * I - D^2 u` for a sigma_2 = 1, sigma_1 > 0 solution in dimension 4: each `f_i > 0`.  (This makes `F` positive definite.)  `lam : Fin 4 → ℝ` is the decreasingly sorted eigenvalue tuple, so `lam 3` is the minimum.  Use the sharp bound `sigma_1 > 2 * |lam 3|` (which you may prove inside, or better: assume the companion lemma) together with monotonicity of `i ↦ lam i` to reduce to the smallest eigenvalue; then argue `0 < sigma_1 - lam 3` from `|lam 3| < sigma_1/2`. -/
open scoped BigOperators

theorem linearized_pos_four (lam : Fin 4 → ℝ)
    (hmono : ∀ ⦃i j : Fin 4⦄, i ≤ j → lam j ≤ lam i)
    (hσ2 : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1)
    (hσ1 : 0 < ∑ i : Fin 4, lam i) :
    ∀ i : Fin 4, 0 < (∑ j : Fin 4, lam j) - lam i := by
  intro i
  -- Core: the sum of the three entries other than the largest one `lam 0` is positive.
  -- Indeed `sigma_1 = lam 0 + lam 1 + lam 2 + lam 3 > 0` together with
  -- `sigma_2 = lam 0 * (lam 1 + lam 2 + lam 3) + (lam 1 * lam 2 + lam 1 * lam 3 + lam 2 * lam 3) = 1`
  -- forces `lam 1 + lam 2 + lam 3 > 0`: otherwise, writing `B = lam 1 + lam 2 + lam 3 ≤ 0`,
  -- we get `lam 0 > -B ≥ 0` from `sigma_1 > 0`, while
  -- `lam 1 * lam 2 + lam 1 * lam 3 + lam 2 * lam 3 = 1 - lam 0 * B ≥ 1 + B^2`
  -- contradicts the unconditional bound `3 * (lam 1 * lam 2 + lam 1 * lam 3 + lam 2 * lam 3) ≤ B^2`.
  have hpos : 0 < lam 1 + lam 2 + lam 3 := by
    by_contra hnot
    have hB : lam 1 + lam 2 + lam 3 ≤ 0 := le_of_not_gt hnot
    have hσ1e : 0 < lam 0 + lam 1 + lam 2 + lam 3 := by
      simpa [Fin.sum_univ_four] using hσ1
    have hσ2e := hσ2
    simp [Fin.sum_univ_four] at hσ2e
    have h3C : 3 * (lam 1 * lam 2 + lam 1 * lam 3 + lam 2 * lam 3)
        ≤ (lam 1 + lam 2 + lam 3) ^ 2 := by
      nlinarith [sq_nonneg (lam 1 - lam 2), sq_nonneg (lam 1 - lam 3),
        sq_nonneg (lam 2 - lam 3)]
    nlinarith
  -- the values `f_i = sigma_1 - lam i` are smallest at the largest entry `lam 0`
  have hle : lam i ≤ lam 0 := by
    exact hmono (i := (0 : Fin 4)) (j := i) (by exact Fin.zero_le i)
  have hmain : 0 < (∑ j : Fin 4, lam j) - lam 0 := by
    rw [Fin.sum_univ_four]
    nlinarith [hpos]
  have hle2 : (∑ j : Fin 4, lam j) - lam 0 ≤ (∑ j : Fin 4, lam j) - lam i := by
    linarith
  exact lt_of_lt_of_le hmain hle2

end Commons.Analysis.Sigma2