import Mathlib
import Submission.Work.EQ.FanTri.SecOrderDefs
import Submission.Work.EQ.FanTri.sR_lip_aux_ball
import Submission.Work.EQ.FanTri.sR_sq_diff_factor

namespace Work.EQ.FanTri

open Work.EQ Complex

noncomputable section

/-- Lipschitz estimate for `sR a z = (sD a z ^ 2 + z.2 ^ 2) ^ (1/2 : ℂ)`
(`sD a z = (sHat a : ℂ) - z.1`, `sHat a = (1-a)/2`) on the ball `‖z‖ ≤ sHat a / 16`.
The already-proved `sD_sR_setup` gives `sR a z ^ 2 = sD a z ^ 2 + z.2 ^ 2`, so
`sR a z - sR a w = (sR a z ^ 2 - sR a w ^ 2)/(sR a z + sR a w)` whose numerator is the
polynomial `-(z.1 - w.1)(sD a z + sD a w) + (z.2 - w.2)(z.2 + w.2)` and whose denominator
has norm at least `28/15 * sHat a`. -/
theorem sR_lipschitz {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {z w : ℂ × ℂ}
    (hz : ‖z‖ ≤ sHat a / 16) (hw : ‖w‖ ≤ sHat a / 16) :
    ‖sR a z - sR a w‖ ≤ 3 / 2 * ‖z - w‖ := by
  have hs0 : 0 < sHat a := sHat_pos ha1
  -- exact factorisation of the difference of the squares
  have hfact := sR_sq_diff_factor ha0 ha1 hz hw
  -- the two small remainders `R - D`
  have hRDz : ‖sR a z - sD a z‖ ≤ sHat a / 240 := (sR_lip_aux_ball ha0 ha1 hz).2.2
  have hRDw : ‖sR a w - sD a w‖ ≤ sHat a / 240 := (sR_lip_aux_ball ha0 ha1 hw).2.2
  have hz1 : ‖z.1‖ ≤ sHat a / 16 := le_trans (norm_fst_le z) hz
  have hz2 : ‖z.2‖ ≤ sHat a / 16 := le_trans (norm_snd_le z) hz
  have hw1 : ‖w.1‖ ≤ sHat a / 16 := le_trans (norm_fst_le w) hw
  have hw2 : ‖w.2‖ ≤ sHat a / 16 := le_trans (norm_snd_le w) hw
  have hzuw1 : ‖z.1 - w.1‖ ≤ ‖z - w‖ := by
    have h := norm_fst_le (z - w); rwa [Prod.fst_sub] at h
  have hzuw2 : ‖z.2 - w.2‖ ≤ ‖z - w‖ := by
    have h := norm_snd_le (z - w); rwa [Prod.snd_sub] at h
  have h2s : ‖(2 * (sHat a : ℂ))‖ = 2 * sHat a := by simp [abs_of_pos hs0]
  -- upper bound for `‖D_z + D_w‖`
  have hDsum_le : ‖sD a z + sD a w‖ ≤ 17 * sHat a / 8 := by
    have h : sD a z + sD a w = 2 * (sHat a : ℂ) - (z.1 + w.1) := by
      simp only [sD]; ring
    rw [h]
    calc ‖2 * (sHat a : ℂ) - (z.1 + w.1)‖ ≤ ‖2 * (sHat a : ℂ)‖ + ‖z.1 + w.1‖ :=
          norm_sub_le _ _
      _ ≤ 2 * sHat a + (sHat a / 16 + sHat a / 16) := by
          rw [h2s]
          exact add_le_add le_rfl (le_trans (norm_add_le _ _) (add_le_add hz1 hw1))
      _ = 17 * sHat a / 8 := by ring
  -- lower bound for `‖D_z + D_w‖`
  have hDsum_ge : 15 * sHat a / 8 ≤ ‖sD a z + sD a w‖ := by
    have h : sD a z + sD a w = 2 * (sHat a : ℂ) - (z.1 + w.1) := by
      simp only [sD]; ring
    have h6 := (abs_le.mp (abs_norm_sub_norm_le (2 * (sHat a : ℂ)) (z.1 + w.1))).2
    rw [h2s] at h6
    rw [h]
    have h7 : ‖z.1 + w.1‖ ≤ sHat a / 16 + sHat a / 16 :=
      le_trans (norm_add_le _ _) (add_le_add hz1 hw1)
    linarith
  -- `‖z₂ + w₂‖ ≤ s/8`
  have hzw2 : ‖z.2 + w.2‖ ≤ sHat a / 8 := by
    have h := le_trans (norm_add_le z.2 w.2) (add_le_add hz2 hw2)
    linarith
  -- lower bound for `‖R_z + R_w‖`, using `R = D + (R - D)`
  have hY : ‖(sR a z - sD a z) + (sR a w - sD a w)‖ ≤ 2 * (sHat a / 240) := by
    calc ‖(sR a z - sD a z) + (sR a w - sD a w)‖
        ≤ ‖sR a z - sD a z‖ + ‖sR a w - sD a w‖ := norm_add_le _ _
      _ ≤ sHat a / 240 + sHat a / 240 := add_le_add hRDz hRDw
      _ = 2 * (sHat a / 240) := by ring
  have hP : 28 * sHat a / 15 ≤ ‖sR a z + sR a w‖ := by
    have hsub : (sD a z + sD a w) - (-((sR a z - sD a z) + (sR a w - sD a w)))
        = sR a z + sR a w := by ring
    have h6 := (abs_le.mp (abs_norm_sub_norm_le (sD a z + sD a w)
      (-((sR a z - sD a z) + (sR a w - sD a w))))).2
    rw [norm_neg, hsub] at h6
    linarith
  have hPpos : 0 < ‖sR a z + sR a w‖ := by linarith
  have hPne : sR a z + sR a w ≠ 0 := norm_pos_iff.mp hPpos
  -- divide the exact identity by `R_z + R_w`
  have hdiv : sR a z - sR a w =
      (-(z.1 - w.1) * (sD a z + sD a w) + (z.2 - w.2) * (z.2 + w.2)) /
        (sR a z + sR a w) := by
    rw [eq_div_iff hPne]
    exact hfact
  have hnum : ‖-(z.1 - w.1) * (sD a z + sD a w) + (z.2 - w.2) * (z.2 + w.2)‖
      ≤ ‖z - w‖ * (17 * sHat a / 8) + ‖z - w‖ * (sHat a / 8) := by
    have hstep : ‖-(z.1 - w.1) * (sD a z + sD a w) + (z.2 - w.2) * (z.2 + w.2)‖
        = ‖-((z.1 - w.1) * (sD a z + sD a w)) + (z.2 - w.2) * (z.2 + w.2)‖ := by
      rw [neg_mul]
    rw [hstep]
    calc ‖-((z.1 - w.1) * (sD a z + sD a w)) + (z.2 - w.2) * (z.2 + w.2)‖
        ≤ ‖(z.1 - w.1) * (sD a z + sD a w)‖ + ‖(z.2 - w.2) * (z.2 + w.2)‖ := by
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_neg]
      _ = ‖z.1 - w.1‖ * ‖sD a z + sD a w‖ + ‖z.2 - w.2‖ * ‖z.2 + w.2‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ ‖z - w‖ * (17 * sHat a / 8) + ‖z - w‖ * (sHat a / 8) := by
          apply add_le_add
          · exact mul_le_mul hzuw1 hDsum_le (norm_nonneg _) (norm_nonneg _)
          · exact mul_le_mul hzuw2 hzw2 (norm_nonneg _) (norm_nonneg _)
  rw [hdiv, norm_div]
  have h1 : ‖-(z.1 - w.1) * (sD a z + sD a w) + (z.2 - w.2) * (z.2 + w.2)‖ / ‖sR a z + sR a w‖
      ≤ (‖z - w‖ * (17 * sHat a / 8) + ‖z - w‖ * (sHat a / 8)) / ‖sR a z + sR a w‖ :=
    div_le_div_of_nonneg_right hnum (norm_nonneg _)
  have h2 : (‖z - w‖ * (17 * sHat a / 8) + ‖z - w‖ * (sHat a / 8)) / ‖sR a z + sR a w‖
      ≤ (‖z - w‖ * (17 * sHat a / 8) + ‖z - w‖ * (sHat a / 8)) / (28 * sHat a / 15) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith) hP
  have h3 : (‖z - w‖ * (17 * sHat a / 8) + ‖z - w‖ * (sHat a / 8)) / (28 * sHat a / 15)
      ≤ 3 / 2 * ‖z - w‖ := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 28 * sHat a / 15)]
    nlinarith [norm_nonneg (z - w), hs0]
  linarith

end

end Work.EQ.FanTri
