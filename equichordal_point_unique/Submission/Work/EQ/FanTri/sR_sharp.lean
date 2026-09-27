import Mathlib
import Submission.Work.EQ.FanTri.SecOrderDefs

namespace Work.EQ.FanTri

open Work.EQ

noncomputable section

/-! ## Elementary estimates for `sR`

Throughout, `s = sHat a = (1-a)/2 > 0`, `D = sD a z = s - z.1`,
`R = sR a z = (D^2 + z.2^2)^(1/2)` (principal square root), and `‖z‖ ≤ s/16`.

The setup `sD_sR_setup` gives `R = D * sqHalf ((z.2/D)^2)`, `R^2 = D^2 + z.2^2`,
`‖z.2‖ ≤ ‖D‖/2`, and `0 < D.re`.  From `‖z‖ ≤ s/16` we moreover get
`‖z.1‖, ‖z.2‖ ≤ s/16` and `‖D‖ ≥ s - s/16 = 15s/16`. -/

/-- `‖sD a z‖ ≥ 15 * sHat a / 16` on the ball of radius `sHat a / 16`. -/
private lemma sD_norm_lower {a : ℝ} (ha1 : a < 1) {z : ℂ × ℂ} (hz : ‖z‖ ≤ sHat a / 16) :
    15 * sHat a / 16 ≤ ‖sD a z‖ := by
  have hs : 0 < sHat a := sHat_pos ha1
  have hz1 : ‖z.1‖ ≤ sHat a / 16 := le_trans (norm_fst_le z) hz
  have h1 : sD a z - (sHat a : ℂ) = -z.1 := by rw [sD]; ring
  have h2 : ‖(sHat a : ℂ)‖ = sHat a := by simp [abs_of_pos hs]
  have h3 := abs_norm_sub_norm_le (sD a z) ((sHat a : ℂ))
  rw [h2, h1, norm_neg] at h3
  linarith [(abs_le.mp h3).1]

/-- `‖sR a z‖ ≥ sHat a / 2`.  Indeed `‖R‖^2 = ‖R^2‖ = ‖D^2 + z.2^2‖ ≥ ‖D‖^2 - ‖z.2‖^2
≥ (3/4)‖D‖^2 ≥ (3/4)(15s/16)^2 > (s/2)^2`. -/
private lemma sR_norm_lower {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {z : ℂ × ℂ}
    (hz : ‖z‖ ≤ sHat a / 16) : sHat a / 2 ≤ ‖sR a z‖ := by
  have hs : 0 < sHat a := sHat_pos ha1
  obtain ⟨-, -, -, hz2D, -, hRsq⟩ := sD_sR_setup ha0 ha1 hz
  have hDlow := sD_norm_lower ha1 hz
  have h1 : ‖sR a z‖ ^ 2 = ‖sD a z ^ 2 + z.2 ^ 2‖ := by rw [← hRsq, norm_pow]
  have h2 : ‖sD a z ^ 2‖ - ‖z.2 ^ 2‖ ≤ ‖sD a z ^ 2 + z.2 ^ 2‖ := by
    have h := norm_sub_le (sD a z ^ 2 + z.2 ^ 2) (z.2 ^ 2)
    rw [add_sub_cancel_right] at h
    linarith
  have h3 : ‖sD a z ^ 2‖ = ‖sD a z‖ ^ 2 := norm_pow _ 2
  have h4 : ‖z.2 ^ 2‖ = ‖z.2‖ ^ 2 := norm_pow _ 2
  rw [h3, h4] at h2
  have hz22 : ‖z.2‖ ^ 2 ≤ (‖sD a z‖ / 2) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hz2D 2
  have hD2 : (15 * sHat a / 16) ^ 2 ≤ ‖sD a z‖ ^ 2 :=
    pow_le_pow_left₀ (by linarith [hs]) hDlow 2
  have hkey : (sHat a / 2) ^ 2 ≤ ‖sR a z‖ ^ 2 := by
    nlinarith [h1, h2, hz22, hD2, hs]
  have := sq_le_sq.mp hkey
  rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ sHat a / 2), abs_of_nonneg (norm_nonneg _)] at this

/-- `‖sR a z + sD a z‖ ≥ 15 * sHat a / 16`.  Indeed `R + D = D * (sqHalf ((z.2/D)^2) + 1)`
and `‖sqHalf w + 1‖ ≥ 1` for `‖w‖ < 1`. -/
private lemma sR_add_sD_norm_lower {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {z : ℂ × ℂ}
    (hz : ‖z‖ ≤ sHat a / 16) : 15 * sHat a / 16 ≤ ‖sR a z + sD a z‖ := by
  obtain ⟨hDne, -, -, hz2D, hRfac, -⟩ := sD_sR_setup ha0 ha1 hz
  have hDlow := sD_norm_lower ha1 hz
  have hDpos : 0 < ‖sD a z‖ := norm_pos_iff.mpr hDne
  have hw : ‖z.2 / sD a z‖ ≤ 1 / 2 := by
    rw [norm_div, div_le_iff₀ hDpos]
    linarith
  have hlt : ‖(z.2 / sD a z) ^ 2‖ < 1 := by
    rw [norm_pow]
    nlinarith [hw, norm_nonneg (z.2 / sD a z)]
  have hone : 1 ≤ ‖sqHalf ((z.2 / sD a z) ^ 2) + 1‖ := norm_sqHalf_add_one_ge_one hlt
  have heq : sR a z + sD a z = sD a z * (sqHalf ((z.2 / sD a z) ^ 2) + 1) := by
    rw [hRfac]; ring
  rw [heq, norm_mul]
  nlinarith [hDlow, hone]

/-- `‖sR a z + sHat a‖ ≥ sHat a / 2`.  Indeed `R + s = (R + D) + z.1`, so
`‖R + s‖ ≥ ‖R + D‖ - ‖z.1‖ ≥ 15s/16 - s/16 = 7s/8`. -/
private lemma sR_add_sHat_norm_lower {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {z : ℂ × ℂ}
    (hz : ‖z‖ ≤ sHat a / 16) : sHat a / 2 ≤ ‖sR a z + (sHat a : ℂ)‖ := by
  have hs : 0 < sHat a := sHat_pos ha1
  have hz1 : ‖z.1‖ ≤ sHat a / 16 := le_trans (norm_fst_le z) hz
  have hC := sR_add_sD_norm_lower ha0 ha1 hz
  have heq : sR a z + (sHat a : ℂ) = (sR a z + sD a z) + z.1 := by rw [sD]; ring
  have hkey : ‖sR a z + sD a z‖ - ‖z.1‖ ≤ ‖sR a z + (sHat a : ℂ)‖ := by
    have h := norm_sub_le (sR a z + sD a z + z.1) z.1
    rw [add_sub_cancel_right] at h
    rw [← heq] at h
    linarith
  linarith

/-- Deviation of `sR a z` from the constant `sHat a`: since
`R - s = -z.1 + D * (sqHalf ((z.2/D)^2) - 1)` and `‖sqHalf w - 1‖ ≤ ‖w‖` for `‖w‖ < 1`,
`‖R - s‖ ≤ ‖z.1‖ + ‖D‖ * ‖z.2/D‖^2 = ‖z.1‖ + ‖z.2‖^2/‖D‖ ≤ ‖z.1‖ + ‖z.2‖/2`. -/
private lemma sR_dev {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {z : ℂ × ℂ}
    (hz : ‖z‖ ≤ sHat a / 16) : ‖sR a z - (sHat a : ℂ)‖ ≤ 3 / 2 * ‖z‖ := by
  obtain ⟨hDne, -, -, hz2D, hRfac, -⟩ := sD_sR_setup ha0 ha1 hz
  have hDpos : 0 < ‖sD a z‖ := norm_pos_iff.mpr hDne
  have hz1 : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
  have hz2 : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
  have hlt : ‖(z.2 / sD a z) ^ 2‖ < 1 := by
    have hw : ‖z.2 / sD a z‖ ≤ 1 / 2 := by
      rw [norm_div, div_le_iff₀ hDpos]; linarith
    rw [norm_pow]; nlinarith [hw, norm_nonneg (z.2 / sD a z)]
  have hS : ‖sqHalf ((z.2 / sD a z) ^ 2) - 1‖ ≤ ‖(z.2 / sD a z) ^ 2‖ :=
    norm_sqHalf_sub_one_le hlt
  have ht : ‖z.2‖ / ‖sD a z‖ ≤ 1 / 2 := by rw [div_le_iff₀ hDpos]; linarith
  have ht2 : ‖sD a z‖ * (‖z.2‖ / ‖sD a z‖) = ‖z.2‖ := by
    rw [← mul_div_assoc]; exact mul_div_cancel_left₀ _ (ne_of_gt hDpos)
  have hbd : ‖sD a z‖ * ‖(z.2 / sD a z) ^ 2‖ ≤ ‖z.2‖ / 2 := by
    rw [norm_pow, norm_div]
    calc ‖sD a z‖ * (‖z.2‖ / ‖sD a z‖) ^ 2
        = (‖sD a z‖ * (‖z.2‖ / ‖sD a z‖)) * (‖z.2‖ / ‖sD a z‖) := by ring
      _ = ‖z.2‖ * (‖z.2‖ / ‖sD a z‖) := by rw [ht2]
      _ ≤ ‖z.2‖ * (1 / 2) := mul_le_mul_of_nonneg_left ht (norm_nonneg _)
      _ = ‖z.2‖ / 2 := by ring
  have hdec : sR a z - (sHat a : ℂ)
      = -z.1 + sD a z * (sqHalf ((z.2 / sD a z) ^ 2) - 1) := by
    rw [hRfac, sD]; ring
  calc ‖sR a z - (sHat a : ℂ)‖
      = ‖-z.1 + sD a z * (sqHalf ((z.2 / sD a z) ^ 2) - 1)‖ := by rw [hdec]
    _ ≤ ‖z.1‖ + ‖sD a z * (sqHalf ((z.2 / sD a z) ^ 2) - 1)‖ := by
        simpa using norm_add_le (-z.1) (sD a z * (sqHalf ((z.2 / sD a z) ^ 2) - 1))
    _ ≤ ‖z.1‖ + ‖z.2‖ / 2 := by
        have h := norm_mul_le (sD a z) (sqHalf ((z.2 / sD a z) ^ 2) - 1)
        have hmul : ‖sD a z‖ * ‖sqHalf ((z.2 / sD a z) ^ 2) - 1‖
            ≤ ‖sD a z‖ * ‖(z.2 / sD a z) ^ 2‖ :=
          mul_le_mul_of_nonneg_left hS (norm_nonneg _)
        linarith [h, hmul, hbd]
    _ ≤ 3 / 2 * ‖z‖ := by linarith

/-- Quantitative first-order facts about `sR a z = (sD a z ^ 2 + z.2 ^ 2) ^ (1/2 : ℂ)`
(`sD a z = (sHat a : ℂ) - z.1`, `sHat a = (1-a)/2`, principal square root) on the ball
`‖z‖ ≤ sHat a / 16`: the deviation of `sR` from the constant `sHat a` is controlled by
`(3/2)‖z‖`, and the three factors `sR a z`, `sR a z + sD a z`, `sR a z + sHat a` stay at
distance at least `sHat a / 2` from `0`.  The already-proved `sD_sR_setup` supplies
`sR a z = sD a z * sqHalf ((z.2/sD a z)^2)` and `sR a z ^ 2 = sD a z ^ 2 + z.2 ^ 2` on that
ball. -/
theorem sR_sharp {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {z : ℂ × ℂ} (hz : ‖z‖ ≤ sHat a / 16) :
    ‖sR a z - (sHat a : ℂ)‖ ≤ 3 / 2 * ‖z‖ ∧
      sHat a / 2 ≤ ‖sR a z‖ ∧ sHat a / 2 ≤ ‖sR a z + sD a z‖ ∧
      sHat a / 2 ≤ ‖sR a z + (sHat a : ℂ)‖ := by
  have hs : 0 < sHat a := sHat_pos ha1
  refine ⟨sR_dev ha0 ha1 hz, sR_norm_lower ha0 ha1 hz, ?_, sR_add_sHat_norm_lower ha0 ha1 hz⟩
  have := sR_add_sD_norm_lower ha0 ha1 hz
  linarith

end

end Work.EQ.FanTri
