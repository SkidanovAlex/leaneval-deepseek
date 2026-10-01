import Mathlib

namespace Work.LinnikAreas.Density4.KappaSum

/-- For every real exponent `A > 0` the logarithm is dominated by a fixed multiple of the square
root: `(log (2+z))^A ≤ K·√z` for all `z ≥ 1`.
Route: `Real.log_le_rpow_div` gives `log (2+z) ≤ (2+z)^{1/(2A)}·(2A)`, and raising to the `A`-th power
gives `(log (2+z))^A ≤ (2A)^A·(2+z)^{1/2} ≤ (2A)^A·√3·√z` since `2+z ≤ 3z` for `z ≥ 1`.
(An analogous lemma `log_pow_le_const_mul_rpow` exists in `Submission/Work/ZeroFreeTables/P3/SummableVonMangoldtLogPow.lean`.) -/
theorem log_pow_le_const_mul_sqrt (A : ℝ) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ z : ℝ, 1 ≤ z →
      (Real.log (2 + z)) ^ A ≤ K * Real.sqrt z := by
  refine ⟨(2 * A) ^ A * Real.sqrt 3, ?_, ?_⟩
  · exact mul_pos (Real.rpow_pos_of_pos (by linarith : 0 < 2 * A) A)
      (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))
  · intro z hz
    have h2z : 0 < 2 + z := by linarith
    have hlog : 0 ≤ Real.log (2 + z) := Real.log_nonneg (by linarith)
    have hε : 0 < 1 / (2 * A) := by positivity
    have hb : Real.log (2 + z) ≤ (2 + z) ^ (1 / (2 * A)) * (2 * A) := by
      have h := Real.log_le_rpow_div (x := 2 + z) (le_of_lt h2z) hε
      have heq : (2 + z) ^ (1 / (2 * A)) / (1 / (2 * A))
          = (2 + z) ^ (1 / (2 * A)) * (2 * A) := by
        field_simp
      rwa [heq] at h
    have h1 : (Real.log (2 + z)) ^ A ≤ ((2 + z) ^ (1 / (2 * A)) * (2 * A)) ^ A :=
      Real.rpow_le_rpow hlog hb (le_of_lt hA)
    have h2 : ((2 + z) ^ (1 / (2 * A)) * (2 * A)) ^ A
        = (2 * A) ^ A * Real.sqrt (2 + z) := by
      rw [Real.mul_rpow (Real.rpow_nonneg (le_of_lt h2z) _) (by linarith : (0 : ℝ) ≤ 2 * A)]
      rw [← Real.rpow_mul (le_of_lt h2z) (1 / (2 * A)) A]
      rw [show (1 / (2 * A)) * A = 1 / 2 by field_simp]
      rw [Real.sqrt_eq_rpow]
      ring
    have h3 : Real.sqrt (2 + z) ≤ Real.sqrt (3 * z) := Real.sqrt_le_sqrt (by linarith)
    have h4 : Real.sqrt (3 * z) = Real.sqrt 3 * Real.sqrt z := Real.sqrt_mul (by norm_num) z
    calc (Real.log (2 + z)) ^ A ≤ ((2 + z) ^ (1 / (2 * A)) * (2 * A)) ^ A := h1
      _ = (2 * A) ^ A * Real.sqrt (2 + z) := h2
      _ ≤ (2 * A) ^ A * Real.sqrt (3 * z) :=
          mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 2 * A) A)
      _ = (2 * A) ^ A * (Real.sqrt 3 * Real.sqrt z) := by rw [h4]
      _ = (2 * A) ^ A * Real.sqrt 3 * Real.sqrt z := by ring

end Work.LinnikAreas.Density4.KappaSum
