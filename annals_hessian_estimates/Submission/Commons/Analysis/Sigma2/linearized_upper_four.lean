import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Sigma2

/-! Upper bound for the eigenvalues `f_i = sigma_1 - lambda_i` of the linearized operator in dimension 4 (Corollary 1.3 of Shankar--Yuan): with sigma_2(lam) = 1 and sigma_1 > 0, each `f_i ≤ (3/2) * sigma_1`.  This follows from the sharp minimum-eigenvalue bound `sigma_1 > 2 * |lam 3|` (prove it inline if needed): the largest value of `f_i` is attained at the smallest eigenvalue `lam 3`, and `sigma_1 - lam 3 = sigma_1 + |lam 3| < (3/2) * sigma_1` when `lam 3 < 0`, while `lam 3 ≥ 0` makes `sigma_1 - lam 3 ≤ sigma_1`. -/
open scoped BigOperators

private lemma sigma2_four_expand (f : Fin 4 → ℝ) :
    (∑ j : Fin 4, ∑ i : Fin 4, if i < j then f i * f j else 0)
      = f 0 * f 1 + f 0 * f 2 + f 0 * f 3 + f 1 * f 2 + f 1 * f 3 + f 2 * f 3 := by
  simp [Fin.sum_univ_four]
  ring

private lemma sq_sum_three_ge_three_pair (x y z : ℝ) :
    (x + y + z) ^ 2 ≥ 3 * (x * y + x * z + y * z) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z)]

theorem linearized_upper_four (lam : Fin 4 → ℝ)
    (hmono : ∀ ⦃i j : Fin 4⦄, i ≤ j → lam j ≤ lam i)
    (hσ2 : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1)
    (hσ1 : 0 < ∑ i : Fin 4, lam i) :
    ∀ i : Fin 4, (∑ j : Fin 4, lam j) - lam i ≤ (3 / 2 : ℝ) * (∑ j : Fin 4, lam j) := by
  intro i
  let s1 : ℝ := ∑ j : Fin 4, lam j
  change s1 - lam i ≤ (3 / 2 : ℝ) * s1
  have hs1 : 0 < s1 := by simpa [s1] using hσ1
  have hs1exp : s1 = lam 0 + lam 1 + lam 2 + lam 3 := by
    simpa [s1] using (Fin.sum_univ_four lam)
  have hσ2p : lam 0 * lam 1 + lam 0 * lam 2 + lam 0 * lam 3 +
        lam 1 * lam 2 + lam 1 * lam 3 + lam 2 * lam 3 = 1 := by
    simpa [sigma2_four_expand] using hσ2
  -- `lam 3` is the smallest eigenvalue (largest index), so `f_i = s1 - lam i ≤ s1 - lam 3`.
  have hmin : lam 3 ≤ lam i := by
    exact hmono (Fin.le_last i)
  have hm3 : s1 - lam i ≤ s1 - lam 3 := by
    nlinarith
  -- Sharp bound for the smallest eigenvalue: `s1 - lam 3 ≤ (3/2) * s1`.
  have hmain : s1 - lam 3 ≤ (3 / 2 : ℝ) * s1 := by
    by_cases h3neg : lam 3 < 0
    · -- `lam 3 < 0`: writing `s = lam 0 + lam 1 + lam 2 = s1 - lam 3 > 0` and
      -- `t = -lam 3 > 0`, sigma_2 splits as `(pairs among lam 0,1,2) + lam 3 * s = 1`,
      -- so the triple inequality `s^2 ≥ 3 * (pairs)` yields `s^2 ≥ 3 + 3 t s`,
      -- whence `s > 3t` and therefore `s1 - lam 3 = s ≤ (3/2) * s1`.
      have hs0 : 0 < lam 0 + lam 1 + lam 2 := by
        have hx : lam 0 + lam 1 + lam 2 = s1 - lam 3 := by
          rw [hs1exp]
          ring
        nlinarith [hs1]
      have hp : lam 0 * lam 1 + lam 0 * lam 2 + lam 1 * lam 2
          = 1 + (-lam 3) * (lam 0 + lam 1 + lam 2) := by
        nlinarith [hσ2p]
      have htriple : (lam 0 + lam 1 + lam 2) ^ 2 ≥
          3 * (lam 0 * lam 1 + lam 0 * lam 2 + lam 1 * lam 2) := by
        exact sq_sum_three_ge_three_pair (lam 0) (lam 1) (lam 2)
      have hsq : 3 ≤ (lam 0 + lam 1 + lam 2) ^ 2
          - 3 * (-lam 3) * (lam 0 + lam 1 + lam 2) := by
        nlinarith
      have hs_gt : 3 * (-lam 3) < lam 0 + lam 1 + lam 2 := by
        by_contra hnot
        have hle : lam 0 + lam 1 + lam 2 ≤ 3 * (-lam 3) := le_of_not_gt hnot
        have hprod : (lam 0 + lam 1 + lam 2) *
            ((lam 0 + lam 1 + lam 2) - 3 * (-lam 3)) ≤ 0 := by
          exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hs0) (sub_nonpos.mpr hle)
        nlinarith
      nlinarith [hs1exp, hs_gt]
    · -- `lam 3 ≥ 0`: then `s1 - lam 3 ≤ s1 ≤ (3/2) * s1`.
      have h3nn : 0 ≤ lam 3 := le_of_not_gt h3neg
      have h1 : s1 - lam 3 ≤ s1 := by nlinarith
      have h2 : s1 ≤ (3 / 2 : ℝ) * s1 := by nlinarith [hs1]
      exact le_trans h1 h2
  exact le_trans hm3 hmain

end Commons.Analysis.Sigma2