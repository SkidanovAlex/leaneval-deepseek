import Mathlib
import Submission.Commons.Analysis.Sigma2.linearized_lower_inverse_four
import Submission.Commons.Analysis.Sigma2.largest_ge_average_four

namespace Commons.Analysis.Sigma2

/-! In dimension 4 (decreasingly sorted eigenvalue tuple with sigma_2 = 1, sigma_1 > 0): the linearized coefficient of the largest eigenvalue satisfies `f_0 * lambda_0^2 ≥ sigma_1 / 16`, where `f_0 := sigma_1 - lam 0`.  Combine `f_0 ≥ 1 / sigma_1` (which holds for every index) with `lam 0 ≥ sigma_1 / 4` (largest entry is at least the average). -/
open scoped BigOperators in
theorem f0_lambda0_sq_ge_sigma1_div_sixteen (lam : Fin 4 → ℝ)
    (hmono : ∀ ⦃i j : Fin 4⦄, i ≤ j → lam j ≤ lam i)
    (hσ2 : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1)
    (hσ1 : 0 < ∑ i : Fin 4, lam i) :
    (∑ i : Fin 4, lam i) / 16 ≤
      ((∑ i : Fin 4, lam i) - lam 0) * (lam 0) ^ 2 := by
  let s1 : ℝ := ∑ i : Fin 4, lam i
  have hs1pos : 0 < s1 := by simpa [s1] using hσ1
  -- f_0 := s1 - lam 0 > 1 / s1  (Corollary 1.3, first inequality, applied to index 0)
  have hf0 : 1 / s1 ≤ s1 - lam 0 := by
    have h := linearized_lower_inverse_four lam hmono hσ2 hσ1 (0 : Fin 4)
    simpa [s1] using (le_of_lt h)
  -- lam 0 ≥ s1 / 4 : the largest entry is at least the average
  have hAvg : s1 / 4 ≤ lam 0 := by
    simpa [s1] using largest_ge_average_four lam hmono
  -- nonnegativity of all the factors involved
  have hAvg_nonneg : 0 ≤ s1 / 4 := div_nonneg hs1pos.le (by norm_num)
  have hlam0_nonneg : 0 ≤ lam 0 := le_trans hAvg_nonneg hAvg
  have hf0_nonneg : 0 ≤ s1 - lam 0 := by
    have : 0 < 1 / s1 := one_div_pos.mpr hs1pos
    exact le_of_lt (lt_of_lt_of_le this hf0)
  -- square the average bound (all quantities nonnegative)
  have hAvgSq : (s1 / 4) ^ 2 ≤ (lam 0) ^ 2 :=
    (sq_le_sq₀ hAvg_nonneg hlam0_nonneg).2 hAvg
  -- multiply the two lower bounds
  have hprod : (1 / s1) * (s1 / 4) ^ 2 ≤ (s1 - lam 0) * (lam 0) ^ 2 :=
    mul_le_mul hf0 hAvgSq (sq_nonneg (s1 / 4)) hf0_nonneg
  -- algebra: (1 / s1) * (s1 / 4)^2 = s1 / 16
  have hcalc : (1 / s1) * (s1 / 4) ^ 2 = s1 / 16 := by
    have hs1nz : s1 ≠ 0 := ne_of_gt hs1pos
    field_simp [hs1nz]
    ring
  -- assemble
  calc
    (∑ i : Fin 4, lam i) / 16 = s1 / 16 := by simp [s1]
    _ ≤ (s1 - lam 0) * (lam 0) ^ 2 := by
      rw [← hcalc]
      exact hprod
    _ = ((∑ i : Fin 4, lam i) - lam 0) * (lam 0) ^ 2 := by simp [s1]

end Commons.Analysis.Sigma2
