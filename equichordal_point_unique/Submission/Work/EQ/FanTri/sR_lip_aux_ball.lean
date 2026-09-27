import Mathlib
import Submission.Work.EQ.FanTri.SecOrderDefs

namespace Work.EQ.FanTri

open Work.EQ Complex

/-- Pointwise size bounds for the factors `sR a z = (sD a z ^ 2 + z.2 ^ 2) ^ (1/2 : ℂ)`,
`sD a z = (sHat a : ℂ) - z.1`, `sHat a = (1-a)/2`, on the ball `‖z‖ ≤ sHat a / 16`:
`‖sR a z + sD a z‖ ≥ 15/16 * sHat a`, `‖sD a z‖ ≥ 15/16 * sHat a`, and
`‖sR a z - sD a z‖ ≤ sHat a / 240`. -/
theorem sR_lip_aux_ball {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {z : ℂ × ℂ}
    (hz : ‖z‖ ≤ sHat a / 16) :
    15 * sHat a / 16 ≤ ‖sR a z + sD a z‖ ∧ 15 * sHat a / 16 ≤ ‖sD a z‖ ∧
      ‖sR a z - sD a z‖ ≤ sHat a / 240 := by
  obtain ⟨hDne, hDre, hDim, hz2D, hRfac, hR2⟩ := sD_sR_setup ha0 ha1 hz
  have hs0 : 0 < sHat a := sHat_pos ha1
  have hz1 : ‖z.1‖ ≤ sHat a / 16 := le_trans (norm_fst_le z) hz
  have hz2 : ‖z.2‖ ≤ sHat a / 16 := le_trans (norm_snd_le z) hz
  -- The abscissa gap is bounded below.
  have hDlow : 15 * sHat a / 16 ≤ ‖sD a z‖ := by
    have h1 : ((sHat a : ℂ)) = sD a z + z.1 := by rw [sD]; ring
    have h2 : ‖((sHat a : ℂ))‖ ≤ ‖sD a z‖ + ‖z.1‖ := by
      rw [h1]; exact norm_add_le _ _
    have h3 : ‖((sHat a : ℂ))‖ = sHat a := by
      rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs, abs_of_pos hs0]
    linarith
  have hDpos : 0 < ‖sD a z‖ := norm_pos_iff.mpr hDne
  -- The normalised ordinate `z₂/D` is at most `1/2` in modulus.
  have hw_half : ‖z.2 / sD a z‖ ≤ 1 / 2 := by
    rw [norm_div, div_le_iff₀ hDpos]
    nlinarith [hz2D]
  have hwnorm : ‖(z.2 / sD a z) ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg (z.2 / sD a z), hw_half]
  -- First bound: `R + D = D (sqHalf((z₂/D)²) + 1)`, and `‖sqHalf w + 1‖ ≥ 1`.
  have hpart1 : 15 * sHat a / 16 ≤ ‖sR a z + sD a z‖ := by
    have hRplus : sR a z + sD a z = sD a z * (sqHalf ((z.2 / sD a z) ^ 2) + 1) := by
      rw [hRfac]; ring
    rw [hRplus, norm_mul]
    have hge : (1 : ℝ) ≤ ‖sqHalf ((z.2 / sD a z) ^ 2) + 1‖ :=
      norm_sqHalf_add_one_ge_one hwnorm
    calc 15 * sHat a / 16 = (15 * sHat a / 16) * 1 := by ring
      _ ≤ ‖sD a z‖ * ‖sqHalf ((z.2 / sD a z) ^ 2) + 1‖ :=
          mul_le_mul hDlow hge (by norm_num) (norm_nonneg _)
  refine ⟨hpart1, hDlow, ?_⟩
  -- Third bound: `(R - D)(R + D) = z₂²`, so `R - D = z₂²/(R + D)`.
  have hprod : (sR a z - sD a z) * (sR a z + sD a z) = z.2 ^ 2 := by
    linear_combination hR2
  have hRplus_ne : sR a z + sD a z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hpart1
    have : (0 : ℝ) < 15 * sHat a / 16 := by linarith
    linarith
  have hRminus : sR a z - sD a z = z.2 ^ 2 / (sR a z + sD a z) := by
    rw [eq_div_iff hRplus_ne]; exact hprod
  have hnum : ‖z.2‖ ^ 2 ≤ (sHat a / 16) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hz2 2
  rw [hRminus, norm_div, norm_pow]
  have hden : 0 < 15 * sHat a / 16 := by linarith
  calc ‖z.2‖ ^ 2 / ‖sR a z + sD a z‖
      ≤ (sHat a / 16) ^ 2 / (15 * sHat a / 16) :=
        div_le_div₀ (by positivity) hnum hden hpart1
    _ = sHat a / 240 := by field_simp; ring

end Work.EQ.FanTri
