import Mathlib

namespace Work.PertCrux

/-- Coarse a-priori bound on the perturbed Fatou coordinate factor
`X = ut / (u0 * (1 + t * ut))`: with `1/2 ≤ ‖u0‖`, `‖ut‖ ≤ 3/2 + η` (`η ≤ 1/1000`)
and `‖t‖ ≤ 1/16`, one has `‖X‖ ≤ 7/2`. -/
theorem norm_X_le {ut u0 t : ℂ} {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1 / 1000) (hu0 : 1 / 2 ≤ ‖u0‖) (hut : ‖ut‖ ≤ 3 / 2 + η)
    (ht : ‖t‖ ≤ 1 / 16) :
    ‖ut / (u0 * (1 + t * ut))‖ ≤ 7 / 2 := by
  -- absolute bound on `‖ut‖`
  have hA : ‖ut‖ ≤ (1501 : ℝ) / 1000 := by linarith
  -- lower bound on the denominator factor `‖1 + t * ut‖`
  have hC : (14499 : ℝ) / 16000 ≤ ‖(1 : ℂ) + t * ut‖ := by
    have htu : ‖t * ut‖ ≤ (1501 : ℝ) / 16000 := by
      rw [norm_mul]
      calc ‖t‖ * ‖ut‖ ≤ (1 / 16) * ((1501 : ℝ) / 1000) := by
            apply mul_le_mul ht hA (norm_nonneg _) (by norm_num)
        _ = (1501 : ℝ) / 16000 := by norm_num
    have h1 : (1 : ℝ) ≤ ‖(1 : ℂ) + t * ut‖ + ‖t * ut‖ := by
      have h := norm_sub_le ((1 : ℂ) + t * ut) (t * ut)
      simpa using h
    linarith
  rw [norm_div, norm_mul]
  have hpos : (0 : ℝ) < ‖u0‖ * ‖(1 : ℂ) + t * ut‖ := by
    apply mul_pos <;> linarith [norm_nonneg (1 + t * ut), norm_nonneg u0]
  rw [div_le_iff₀ hpos]
  have hBC : (1 / 2 : ℝ) * ((14499 : ℝ) / 16000) ≤ ‖u0‖ * ‖(1 : ℂ) + t * ut‖ := by
    apply mul_le_mul hu0 hC (by norm_num) (norm_nonneg _)
  nlinarith [hBC, hA]

end Work.PertCrux
