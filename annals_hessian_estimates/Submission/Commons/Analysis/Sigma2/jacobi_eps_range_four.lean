import Mathlib
import Submission.Commons.Analysis.Sigma2.sharp_minEigen_four
import Submission.Commons.Analysis.Sigma2.largest_ge_average_four

namespace Commons.Analysis.Sigma2

/-! Range of the almost-Jacobi coefficient in dimension 4: with a decreasingly sorted eigenvalue tuple satisfying sigma_2 = 1 and sigma_1 > 0, the coefficient `eps := (2/9) * (1/2 + lam 3 / sigma_1)` satisfies `0 < eps` and `eps < 1/2`.  Positivity: `lam 3 > - sigma_1 / 2` by the sharp minimum eigenvalue bound (when `lam 3 < 0`; trivial otherwise), so `1/2 + lam 3 / sigma_1 > 0`.  Upper bound: `lam 3 ≤ sigma_1 / 4` (sigma_1 = sum of all entries ≥ 4 * min), so `eps ≤ (2/9)*(3/4) = 1/6 < 1/2`.  Needed so that with `delta := 1 + eps` the trace condition `delta ≤ 3*n/(2*(n-1)) = 2` holds for n = 4. -/
open scoped BigOperators in
theorem jacobi_eps_range_four (lam : Fin 4 → ℝ)
    (hmono : ∀ ⦃i j : Fin 4⦄, i ≤ j → lam j ≤ lam i)
    (hσ2 : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1)
    (hσ1 : 0 < ∑ i : Fin 4, lam i) :
    0 < (2 / 9 : ℝ) * (1 / 2 + lam 3 / (∑ i : Fin 4, lam i)) ∧
      (2 / 9 : ℝ) * (1 / 2 + lam 3 / (∑ i : Fin 4, lam i)) < 1 / 2 := by
  -- σ₁ > 2·|λ₃| (sharp minimum-eigenvalue bound, needs σ₂ = 1)
  have hmin0 : (∑ i : Fin 4, lam i) > 2 * |lam 3| :=
    sharp_minEigen_four lam hmono hσ2 hσ1
  -- σ₁ = sum of all entries ≥ 4·λ₃, i.e. λ₃ ≤ σ₁ / 4
  have hSge0 : 4 * lam 3 ≤ ∑ i : Fin 4, lam i := by
    have hle : (∑ _i : Fin 4, lam 3) ≤ (∑ i : Fin 4, lam i) := by
      exact Finset.sum_le_sum fun i _hi => hmono (Fin.le_last i)
    simpa [mul_comm] using hle
  set S : ℝ := ∑ i : Fin 4, lam i with hSdef
  have hSpos : 0 < S := by
    simpa using hσ1
  have hSne : S ≠ 0 := ne_of_gt hSpos
  have hmin : S > 2 * |lam 3| := by
    rwa [hSdef] at hmin0
  have hSge4 : 4 * lam 3 ≤ S := by
    simpa [S] using hSge0
  -- Positivity of `eps`.  Since σ₁ > 0, `1/2 + λ₃/σ₁ > 0` iff `σ₁ + 2·λ₃ > 0`.
  have hnum : 0 < S + 2 * lam 3 := by
    by_cases h3nn : 0 ≤ lam 3
    · nlinarith [hSpos, h3nn]
    · have h3neg : lam 3 < 0 := lt_of_not_ge h3nn
      have habs : |lam 3| = -lam 3 := abs_of_neg h3neg
      nlinarith [hmin, habs]
  have hXeq : 1 / 2 + lam 3 / S = (S + 2 * lam 3) / (2 * S) := by
    field_simp [hSne]
  have hXpos : 0 < 1 / 2 + lam 3 / S := by
    rw [hXeq]
    exact div_pos hnum (mul_pos (by norm_num : (0 : ℝ) < 2) hSpos)
  have hprod_pos : 0 < (2 / 9 : ℝ) * (1 / 2 + lam 3 / S) := by
    exact mul_pos (by norm_num : 0 < (2 / 9 : ℝ)) hXpos
  -- Upper bound: λ₃ / σ₁ ≤ 1/4, so 1/2 + λ₃/σ₁ ≤ 3/4 and `eps ≤ 1/6 < 1/2`.
  have hdiv : lam 3 / S ≤ 1 / 4 := by
    rw [div_le_iff₀ hSpos]
    linarith
  have hXle : 1 / 2 + lam 3 / S ≤ 3 / 4 := by linarith
  have hprod_le : (2 / 9 : ℝ) * (1 / 2 + lam 3 / S) ≤ (2 / 9) * (3 / 4) := by
    exact mul_le_mul_of_nonneg_left hXle (by norm_num : (0 : ℝ) ≤ 2 / 9)
  have hsix : (2 / 9 : ℝ) * (3 / 4) < 1 / 2 := by norm_num
  have hprod_lt : (2 / 9 : ℝ) * (1 / 2 + lam 3 / S) < 1 / 2 :=
    lt_of_le_of_lt hprod_le hsix
  constructor
  · simpa using hprod_pos
  · simpa using hprod_lt

end Commons.Analysis.Sigma2
