import Mathlib
import Submission.Commons.Analysis.Sigma2.linearized_lower_large_four

namespace Commons.Analysis.Sigma2

/-! In dimension 4 (decreasingly sorted eigenvalue tuple with sigma_2 = 1, sigma_1 > 0): in the degenerate configuration where the smallest eigenvalue is very negative, `lam 3 ≤ - sigma_1 / 4`, the linearized coefficient of the smallest eigenvalue satisfies `f_3 * lam 3^2 ≥ ((1 - 1/sqrt 2)/16) * sigma_1^3` with `f_3 := sigma_1 - lam 3`.  Combine `f_3 ≥ (1 - 1/sqrt 2) * sigma_1` (valid since index 3 ≠ 0) with `lam 3^2 ≥ sigma_1^2/16`. -/
open scoped BigOperators in
theorem f3_lambda3_sq_lower_in_degenerate_case (lam : Fin 4 → ℝ)
    (hmono : ∀ ⦃i j : Fin 4⦄, i ≤ j → lam j ≤ lam i)
    (hσ2 : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1)
    (hσ1 : 0 < ∑ i : Fin 4, lam i)
    (hdeg : lam 3 ≤ -(∑ i : Fin 4, lam i) / 4) :
    ((1 - 1 / Real.sqrt 2) / 16) * (∑ i : Fin 4, lam i) ^ 3 ≤
      ((∑ i : Fin 4, lam i) - lam 3) * (lam 3) ^ 2 := by
  classical
  let s1 : ℝ := ∑ j : Fin 4, lam j
  let t : ℝ := lam 3
  change ((1 - 1 / Real.sqrt 2) / 16) * s1 ^ 3 ≤ (s1 - t) * t ^ 2
  have hs1 : 0 < s1 := by simpa [s1] using hσ1
  have htdeg : t ≤ -s1 / 4 := by simpa [s1, t] using hdeg
  -- `f_3 = s1 - t ≥ (1 - 1/√2) * s1`, from the non-largest index bound (3 ≠ 0)
  have hf3 : (1 - 1 / Real.sqrt 2) * s1 ≤ s1 - t := by
    simpa [s1, t] using
      (linearized_lower_large_four lam hmono hσ2 hσ1 (3 : Fin 4) (by decide : (3 : Fin 4) ≠ 0))
  -- s1 - t ≥ s1 + s1/4 > 0 : nonnegativity of the first multiplier
  have hf3pos : 0 ≤ s1 - t := by nlinarith [hs1, htdeg]
  -- from `t ≤ -s1 / 4` and `s1 > 0` we get `t ≤ 0` and `s1 ≤ 4 * (-t)`
  have htle0 : t ≤ 0 := by nlinarith [hs1, htdeg]
  have h4nt : 0 ≤ 4 * (-t) := by nlinarith [htle0]
  have hs_le : s1 ≤ 4 * (-t) := by nlinarith [htdeg]
  have hsq16 : s1 ^ 2 ≤ (4 * (-t)) ^ 2 := by
    exact (sq_le_sq₀ (le_of_lt hs1) h4nt).2 hs_le
  -- squaring gives `lam 3 ^ 2 ≥ s1 ^ 2 / 16`
  have ht2 : s1 ^ 2 / 16 ≤ t ^ 2 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 16)]
    nlinarith [hsq16]
  have hsqpos : 0 ≤ s1 ^ 2 / 16 := by positivity
  -- multiply the two lower bounds
  calc
    ((1 - 1 / Real.sqrt 2) / 16) * s1 ^ 3
        = ((1 - 1 / Real.sqrt 2) * s1) * (s1 ^ 2 / 16) := by ring
    _ ≤ (s1 - t) * (s1 ^ 2 / 16) := by
      exact mul_le_mul_of_nonneg_right hf3 hsqpos
    _ ≤ (s1 - t) * t ^ 2 := by
      exact mul_le_mul_of_nonneg_left ht2 hf3pos

end Commons.Analysis.Sigma2
