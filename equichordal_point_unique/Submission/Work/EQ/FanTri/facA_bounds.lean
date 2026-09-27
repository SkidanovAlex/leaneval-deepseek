import Mathlib
import Submission.Work.EQ.FanTri.SecOrderDefs

namespace Work.EQ.FanTri

open Work.EQ Complex

noncomputable section

set_option maxHeartbeats 1000000

/-- Lower bound for the abscissa gap `sD a z = sHat a - z.1` on the ball `‖z‖ ≤ sHat a/16`. -/
lemma sD_norm_lower {a : ℝ} (ha1 : a < 1) {z : ℂ × ℂ} (hz : ‖z‖ ≤ sHat a / 16) :
    15 / 16 * sHat a ≤ ‖sD a z‖ := by
  have hs0 : 0 < sHat a := sHat_pos ha1
  have h1 : sD a z - (sHat a : ℂ) = -z.1 := by rw [sD]; ring
  have h2 : ‖(sHat a : ℂ)‖ = sHat a := by simp [abs_of_pos hs0]
  have h3 := abs_norm_sub_norm_le (sD a z) (sHat a : ℂ)
  rw [h2, h1, norm_neg] at h3
  have hz1 : ‖z.1‖ ≤ sHat a / 16 := le_trans (norm_fst_le z) hz
  linarith [(abs_le.mp h3).1]

/-- The principal square root `sR a z` is within `(3/2)‖z‖` of the constant `sHat a` on
`‖z‖ ≤ sHat a/16`. -/
lemma sR_sub_sHat_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {z : ℂ × ℂ}
    (hz : ‖z‖ ≤ sHat a / 16) :
    ‖sR a z - (sHat a : ℂ)‖ ≤ 3 / 2 * ‖z‖ := by
  obtain ⟨hDne, hDre, hDim, hz2D, hRfac, hRsq⟩ := sD_sR_setup ha0 ha1 hz
  have hs0 : 0 < sHat a := sHat_pos ha1
  have hDpos : 0 < ‖sD a z‖ := norm_pos_iff.mpr hDne
  set u := (z.2 / sD a z) ^ 2 with hu
  have hnn : 0 ≤ ‖z.2‖ / ‖sD a z‖ := div_nonneg (norm_nonneg _) (le_of_lt hDpos)
  have hle2 : ‖z.2‖ / ‖sD a z‖ ≤ 1 / 2 := by
    rw [div_le_iff₀ hDpos]; linarith [hz2D]
  have hu_lt : ‖u‖ < 1 := by
    rw [hu, norm_pow, norm_div]
    nlinarith [norm_nonneg z.2, hle2, hnn]
  have hsq_bound : ‖sqHalf u - 1‖ ≤ ‖u‖ := norm_sqHalf_sub_one_le hu_lt
  have hdecomp : sR a z - (sHat a : ℂ) = sD a z * (sqHalf u - 1) - z.1 := by
    rw [hRfac]; simp only [sD]; ring
  have h1 : ‖sD a z * (sqHalf u - 1)‖ ≤ ‖z.2‖ / 2 := by
    rw [norm_mul]
    have hle : ‖sD a z‖ * ‖sqHalf u - 1‖ ≤ ‖sD a z‖ * ‖u‖ :=
      mul_le_mul_of_nonneg_left hsq_bound (norm_nonneg _)
    have h2 : ‖sD a z‖ * ‖u‖ = ‖z.2‖ ^ 2 / ‖sD a z‖ := by
      rw [hu, norm_pow, norm_div]
      field_simp
    have h3 : ‖z.2‖ ^ 2 / ‖sD a z‖ ≤ ‖z.2‖ / 2 := by
      rw [div_le_iff₀ hDpos]
      nlinarith [norm_nonneg z.2, hle2, hDpos]
    linarith [hle, h2 ▸ h3]
  rw [hdecomp]
  calc ‖sD a z * (sqHalf u - 1) - z.1‖
      ≤ ‖sD a z * (sqHalf u - 1)‖ + ‖z.1‖ := norm_sub_le _ _
    _ ≤ ‖z.2‖ / 2 + ‖z‖ := by linarith [h1, norm_fst_le z]
    _ ≤ 3 / 2 * ‖z‖ := by linarith [norm_snd_le z, norm_nonneg z]

/-- Pointwise bounds for `sR a z` (and `sD a z`) on the ball `‖z‖ ≤ sHat a/16`. -/
lemma sR_pointwise {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {z : ℂ × ℂ}
    (hz : ‖z‖ ≤ sHat a / 16) :
    ‖sR a z - (sHat a : ℂ)‖ ≤ 3 / 2 * ‖z‖ ∧
    ‖sR a z‖ ≤ 35 / 32 * sHat a ∧
    sHat a / 2 ≤ ‖sR a z‖ ∧
    sHat a / 2 ≤ ‖sR a z + sD a z‖ ∧
    ‖sD a z‖ ≤ 17 / 16 * sHat a ∧
    (29 / 32) * sHat a ≤ (sR a z).re := by
  obtain ⟨hDne, hDre, hDim, hz2D, hRfac, hRsq⟩ := sD_sR_setup ha0 ha1 hz
  have hs0 : 0 < sHat a := sHat_pos ha1
  have hDpos : 0 < ‖sD a z‖ := norm_pos_iff.mpr hDne
  have hz1 : ‖z.1‖ ≤ sHat a / 16 := le_trans (norm_fst_le z) hz
  have hz2 : ‖z.2‖ ≤ sHat a / 16 := le_trans (norm_snd_le z) hz
  have hzle : ‖z‖ ≤ sHat a / 16 := hz
  set u := (z.2 / sD a z) ^ 2 with hu
  have hnn : 0 ≤ ‖z.2‖ / ‖sD a z‖ := div_nonneg (norm_nonneg _) (le_of_lt hDpos)
  have hle2 : ‖z.2‖ / ‖sD a z‖ ≤ 1 / 2 := by
    rw [div_le_iff₀ hDpos]; linarith [hz2D]
  have hu_lt : ‖u‖ < 1 := by
    rw [hu, norm_pow, norm_div]
    nlinarith [norm_nonneg z.2, hle2, hnn]
  have hnormHat : ‖(sHat a : ℂ)‖ = sHat a := by simp [abs_of_pos hs0]
  have hRsub : ‖sR a z - (sHat a : ℂ)‖ ≤ 3 / 2 * ‖z‖ :=
    sR_sub_sHat_le ha0 ha1 hz
  have hRup : ‖sR a z‖ ≤ 35 / 32 * sHat a := by
    have h := norm_add_le (sR a z - (sHat a : ℂ)) (sHat a : ℂ)
    rw [sub_add_cancel] at h
    calc ‖sR a z‖ ≤ ‖sR a z - (sHat a : ℂ)‖ + ‖(sHat a : ℂ)‖ := h
      _ ≤ 3 / 2 * ‖z‖ + sHat a := by rw [hnormHat]; linarith [hRsub]
      _ ≤ 35 / 32 * sHat a := by linarith [hzle, hs0]
  have hRre : (29 / 32) * sHat a ≤ (sR a z).re := by
    have h1 : (sR a z).re - sHat a = (sR a z - (sHat a : ℂ)).re := by simp
    have h2 : |(sR a z - (sHat a : ℂ)).re| ≤ ‖sR a z - (sHat a : ℂ)‖ :=
      Complex.abs_re_le_norm _
    have h3 : -(3 / 2 * ‖z‖) ≤ (sR a z).re - sHat a := by
      rw [h1]; linarith [(abs_le.mp h2).1, hRsub]
    linarith [h3, hzle, hs0]
  have hRlow : sHat a / 2 ≤ ‖sR a z‖ := by
    have h : (sR a z).re ≤ ‖sR a z‖ := Complex.re_le_norm _
    linarith [hRre, h, hs0]
  have hRD : sHat a / 2 ≤ ‖sR a z + sD a z‖ := by
    have heq : sR a z + sD a z = sD a z * (sqHalf u + 1) := by rw [hRfac]; ring
    rw [heq, norm_mul]
    have h1 : 1 ≤ ‖sqHalf u + 1‖ := norm_sqHalf_add_one_ge_one hu_lt
    have h2 : 15 / 16 * sHat a ≤ ‖sD a z‖ := sD_norm_lower ha1 hz
    nlinarith [h1, h2, norm_nonneg (sqHalf u + 1), hs0]
  have hDle : ‖sD a z‖ ≤ 17 / 16 * sHat a := by
    have h1 : sD a z - (sHat a : ℂ) = -z.1 := by rw [sD]; ring
    have h := norm_add_le (sD a z - (sHat a : ℂ)) (sHat a : ℂ)
    rw [sub_add_cancel] at h
    calc ‖sD a z‖ ≤ ‖sD a z - (sHat a : ℂ)‖ + ‖(sHat a : ℂ)‖ := h
      _ = ‖z.1‖ + sHat a := by rw [h1, norm_neg, hnormHat]
      _ ≤ 17 / 16 * sHat a := by linarith [hz1, hs0]
  exact ⟨hRsub, hRup, hRlow, hRD, hDle, hRre⟩

/-- Lipschitz estimate for `sR a z = (sD a z ^ 2 + z.2 ^ 2) ^ (1/2 : ℂ)`
(`sD a z = (sHat a : ℂ) - z.1`, `sHat a = (1-a)/2`) on the ball `‖z‖ ≤ sHat a / 16`.
The already-proved `sD_sR_setup` gives `sR a z ^ 2 = sD a z ^ 2 + z.2 ^ 2`, so
`sR a z - sR a w = (sR a z ^ 2 - sR a w ^ 2)/(sR a z + sR a w)` whose numerator is the
polynomial `(z.1 - w.1)(2*sHat a - z.1 - w.1) + (z.2 - w.2)(z.2 + w.2)` and whose denominator
has norm at least `sHat a / 2`. -/
lemma sR_dist_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {z w : ℂ × ℂ}
    (hz : ‖z‖ ≤ sHat a / 16) (hw : ‖w‖ ≤ sHat a / 16) :
    ‖sR a z - sR a w‖ ≤ 3 / 2 * ‖z - w‖ := by
  obtain ⟨-, -, -, -, -, hzsq⟩ := sD_sR_setup ha0 ha1 hz
  obtain ⟨-, -, -, -, -, hwsq⟩ := sD_sR_setup ha0 ha1 hw
  obtain ⟨-, -, -, -, -, hzre⟩ := sR_pointwise ha0 ha1 hz
  obtain ⟨-, -, -, -, -, hwre⟩ := sR_pointwise ha0 ha1 hw
  have hs0 : 0 < sHat a := sHat_pos ha1
  have hden : 29 / 16 * sHat a ≤ ‖sR a z + sR a w‖ := by
    have h : (sR a z + sR a w).re = (sR a z).re + (sR a w).re := by simp
    have h2 : (sR a z + sR a w).re ≤ ‖sR a z + sR a w‖ := Complex.re_le_norm _
    rw [h] at h2
    linarith [hzre, hwre, h2]
  have hDsub : ‖sD a z - sD a w‖ ≤ ‖z - w‖ := by
    have heq : sD a z - sD a w = -(z.1 - w.1) := by rw [sD, sD]; ring
    calc ‖sD a z - sD a w‖ = ‖z.1 - w.1‖ := by rw [heq, norm_neg]
      _ ≤ ‖z - w‖ := by have := norm_fst_le (z - w); simpa using this
  have hDadd : ‖sD a z + sD a w‖ ≤ 17 / 8 * sHat a := by
    have heq : sD a z + sD a w = 2 * (sHat a : ℂ) - z.1 - w.1 := by rw [sD, sD]; ring
    have h1 : ‖z.1‖ ≤ sHat a / 16 := le_trans (norm_fst_le z) hz
    have h2 : ‖w.1‖ ≤ sHat a / 16 := le_trans (norm_fst_le w) hw
    have hn : ‖(2 : ℂ) * (sHat a : ℂ)‖ = 2 * sHat a := by
      rw [norm_mul]; simp [abs_of_pos hs0]
    calc ‖sD a z + sD a w‖ = ‖2 * (sHat a : ℂ) - z.1 - w.1‖ := by rw [heq]
      _ ≤ ‖2 * (sHat a : ℂ) - z.1‖ + ‖w.1‖ := norm_sub_le _ _
      _ ≤ (‖2 * (sHat a : ℂ)‖ + ‖z.1‖) + ‖w.1‖ := by
            have := norm_sub_le (2 * (sHat a : ℂ)) z.1; linarith [this]
      _ ≤ 17 / 8 * sHat a := by rw [hn]; linarith [h1, h2]
  have hnum : ‖sR a z ^ 2 - sR a w ^ 2‖ ≤ 9 / 4 * sHat a * ‖z - w‖ := by
    have heq : sR a z ^ 2 - sR a w ^ 2 =
        (sD a z - sD a w) * (sD a z + sD a w) + (z.2 - w.2) * (z.2 + w.2) := by
      rw [hzsq, hwsq]; ring
    rw [heq]
    have hA : ‖(sD a z - sD a w) * (sD a z + sD a w)‖ ≤ ‖z - w‖ * (17 / 8 * sHat a) := by
      rw [norm_mul]; exact mul_le_mul hDsub hDadd (norm_nonneg _) (norm_nonneg _)
    have hB : ‖(z.2 - w.2) * (z.2 + w.2)‖ ≤ ‖z - w‖ * (sHat a / 8) := by
      rw [norm_mul]
      have h1 : ‖z.2 - w.2‖ ≤ ‖z - w‖ := by
        have := norm_snd_le (z - w); simpa using this
      have h2 : ‖z.2 + w.2‖ ≤ sHat a / 8 := by
        have hz2 : ‖z.2‖ ≤ sHat a / 16 := le_trans (norm_snd_le z) hz
        have hw2 : ‖w.2‖ ≤ sHat a / 16 := le_trans (norm_snd_le w) hw
        calc ‖z.2 + w.2‖ ≤ ‖z.2‖ + ‖w.2‖ := norm_add_le _ _
          _ ≤ sHat a / 8 := by linarith
      exact mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
    calc ‖(sD a z - sD a w) * (sD a z + sD a w) + (z.2 - w.2) * (z.2 + w.2)‖
        ≤ ‖(sD a z - sD a w) * (sD a z + sD a w)‖ + ‖(z.2 - w.2) * (z.2 + w.2)‖ :=
          norm_add_le _ _
      _ ≤ ‖z - w‖ * (17 / 8 * sHat a) + ‖z - w‖ * (sHat a / 8) := by linarith [hA, hB]
      _ ≤ 9 / 4 * sHat a * ‖z - w‖ := by nlinarith [norm_nonneg (z - w)]
  have hkey : (sR a z - sR a w) * (sR a z + sR a w) = sR a z ^ 2 - sR a w ^ 2 := by ring
  have hprod : ‖sR a z - sR a w‖ * ‖sR a z + sR a w‖ ≤ 9 / 4 * sHat a * ‖z - w‖ := by
    rw [← norm_mul, hkey]; exact hnum
  have hdenpos : 0 < 29 / 16 * sHat a := by linarith
  have hfinal : ‖sR a z - sR a w‖ ≤ (9 / 4 * sHat a * ‖z - w‖) / (29 / 16 * sHat a) := by
    rw [le_div_iff₀ hdenpos]
    calc ‖sR a z - sR a w‖ * (29 / 16 * sHat a)
        ≤ ‖sR a z - sR a w‖ * ‖sR a z + sR a w‖ :=
          mul_le_mul_of_nonneg_left hden (norm_nonneg _)
      _ ≤ 9 / 4 * sHat a * ‖z - w‖ := hprod
  calc ‖sR a z - sR a w‖ ≤ (9 / 4 * sHat a * ‖z - w‖) / (29 / 16 * sHat a) := hfinal
    _ = 36 / 29 * ‖z - w‖ := by field_simp; ring
    _ ≤ 3 / 2 * ‖z - w‖ := by nlinarith [norm_nonneg (z - w)]

/-- Boundedness and Lipschitz estimate for `facA a z = (sR a z * (sR a z + sD a z))⁻¹` on the
ball `‖z‖ ≤ sHat a / 16` (`sD a z = (sHat a : ℂ) - z.1`, `sR a z = (sD a z ^ 2 + z.2 ^ 2)^(1/2)`,
`sHat a = (1-a)/2`).  The already-proved `sD_sR_setup` gives `sR a z ^ 2 = sD a z ^ 2 + z.2 ^ 2`,
whence `‖sR a z - sHat a‖ ≤ (3/2)‖z‖`, `‖sR a z‖ ≥ sHat a/2`, `‖sR a z + sD a z‖ ≥ sHat a/2`.
The constants `4` and `100` are deliberately generous. -/
theorem facA_bounds {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {z w : ℂ × ℂ}
    (hz : ‖z‖ ≤ sHat a / 16) (hw : ‖w‖ ≤ sHat a / 16) :
    ‖facA a z‖ ≤ 4 / sHat a ^ 2 ∧ ‖facA a z - facA a w‖ ≤ 100 / sHat a ^ 3 * ‖z - w‖ := by
  have hs0 : 0 < sHat a := sHat_pos ha1
  have hs2pos : 0 < sHat a ^ 2 / 4 := by positivity
  obtain ⟨-, hRupz, hRlowz, hRDz, hDlez, -⟩ := sR_pointwise ha0 ha1 hz
  obtain ⟨-, hRupw, hRloww, hRDw, hDlew, -⟩ := sR_pointwise ha0 ha1 hw
  set Pz := sR a z * (sR a z + sD a z) with hPzdef
  set Pw := sR a w * (sR a w + sD a w) with hPwdef
  have hPz_low : sHat a ^ 2 / 4 ≤ ‖Pz‖ := by
    rw [hPzdef, norm_mul]
    nlinarith [hRlowz, hRDz, norm_nonneg (sR a z), norm_nonneg (sR a z + sD a z), hs0]
  have hPw_low : sHat a ^ 2 / 4 ≤ ‖Pw‖ := by
    rw [hPwdef, norm_mul]
    nlinarith [hRloww, hRDw, norm_nonneg (sR a w), norm_nonneg (sR a w + sD a w), hs0]
  have hPzpos : 0 < ‖Pz‖ := lt_of_lt_of_le hs2pos hPz_low
  have hPwpos : 0 < ‖Pw‖ := lt_of_lt_of_le hs2pos hPw_low
  have hPz_ne : Pz ≠ 0 := by
    intro h; rw [h, norm_zero] at hPzpos; exact lt_irrefl _ hPzpos
  have hPw_ne : Pw ≠ 0 := by
    intro h; rw [h, norm_zero] at hPwpos; exact lt_irrefl _ hPwpos
  constructor
  · have hfac : ‖facA a z‖ = ‖Pz‖⁻¹ := by rw [facA, ← hPzdef, norm_inv]
    rw [hfac]
    calc ‖Pz‖⁻¹ ≤ (sHat a ^ 2 / 4)⁻¹ := (inv_le_inv₀ hPzpos hs2pos).mpr hPz_low
      _ = 4 / sHat a ^ 2 := by rw [inv_div]
  · have hRlip : ‖sR a z - sR a w‖ ≤ 3 / 2 * ‖z - w‖ := sR_dist_le ha0 ha1 hz hw
    have hDsub : ‖sD a z - sD a w‖ ≤ ‖z - w‖ := by
      have heq : sD a z - sD a w = -(z.1 - w.1) := by rw [sD, sD]; ring
      calc ‖sD a z - sD a w‖ = ‖z.1 - w.1‖ := by rw [heq, norm_neg]
        _ ≤ ‖z - w‖ := by have := norm_fst_le (z - w); simpa using this
    have hnum : ‖Pz - Pw‖ ≤ 191 / 32 * sHat a * ‖z - w‖ := by
      have hdecomp : Pz - Pw = (sR a z - sR a w) * (sR a z + sD a z + sR a w) + sR a w * (sD a z - sD a w) := by
        rw [hPzdef, hPwdef]; ring
      rw [hdecomp]
      have hA : ‖(sR a z - sR a w) * (sR a z + sD a z + sR a w)‖ ≤ (3/2 * ‖z-w‖) * (13/4 * sHat a) := by
        rw [norm_mul]
        apply mul_le_mul hRlip _ (norm_nonneg _) (by nlinarith [norm_nonneg (z - w)])
        calc ‖sR a z + sD a z + sR a w‖ ≤ ‖sR a z + sD a z‖ + ‖sR a w‖ := norm_add_le _ _
          _ ≤ 13/4 * sHat a := by
              have h1 : ‖sR a z + sD a z‖ ≤ ‖sR a z‖ + ‖sD a z‖ := norm_add_le _ _
              linarith [h1, hRupz, hDlez, hRupw, hs0]
      have hB : ‖sR a w * (sD a z - sD a w)‖ ≤ (35/32 * sHat a) * ‖z - w‖ := by
        rw [norm_mul]
        exact mul_le_mul hRupw hDsub (norm_nonneg _) (by nlinarith [hs0])
      calc ‖(sR a z - sR a w) * (sR a z + sD a z + sR a w) + sR a w * (sD a z - sD a w)‖
          ≤ ‖(sR a z - sR a w) * (sR a z + sD a z + sR a w)‖ + ‖sR a w * (sD a z - sD a w)‖ := norm_add_le _ _
        _ ≤ (3/2 * ‖z-w‖)*(13/4 * sHat a) + (35/32 * sHat a)*‖z-w‖ := by linarith [hA, hB]
        _ ≤ 191/32 * sHat a * ‖z - w‖ := by nlinarith [norm_nonneg (z-w), hs0]
    have heq : facA a z - facA a w = (Pw - Pz) * (Pz⁻¹ * Pw⁻¹) := by
      rw [facA, facA, ← hPzdef, ← hPwdef]
      field_simp [hPz_ne, hPw_ne]
    have hinv : ‖Pz‖⁻¹ * ‖Pw‖⁻¹ ≤ (4/sHat a^2) * (4/sHat a^2) := by
      have h1 : ‖Pz‖⁻¹ ≤ 4/sHat a^2 :=
        calc ‖Pz‖⁻¹ ≤ (sHat a^2/4)⁻¹ := (inv_le_inv₀ hPzpos hs2pos).mpr hPz_low
          _ = 4/sHat a^2 := by rw [inv_div]
      have h2 : ‖Pw‖⁻¹ ≤ 4/sHat a^2 :=
        calc ‖Pw‖⁻¹ ≤ (sHat a^2/4)⁻¹ := (inv_le_inv₀ hPwpos hs2pos).mpr hPw_low
          _ = 4/sHat a^2 := by rw [inv_div]
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    calc ‖facA a z - facA a w‖
        = ‖Pw - Pz‖ * (‖Pz‖⁻¹ * ‖Pw‖⁻¹) := by
          rw [heq, norm_mul, norm_mul, norm_inv, norm_inv]
      _ ≤ (191/32 * sHat a * ‖z - w‖) * ((4/sHat a^2) * (4/sHat a^2)) := by
          apply mul_le_mul _ hinv (by positivity) (by nlinarith [norm_nonneg (z - w), hs0])
          rw [norm_sub_rev]; exact hnum
      _ ≤ 100 / sHat a ^ 3 * ‖z - w‖ := by
          have hs3 : 0 < sHat a ^ 3 := by positivity
          have h191 : (191/32 * sHat a * ‖z - w‖) * ((4/sHat a^2) * (4/sHat a^2)) = 191/2/sHat a^3 * ‖z - w‖ := by
            field_simp; ring
          rw [h191]
          have hkey : (191:ℝ)/2/sHat a^3 ≤ 100/sHat a^3 :=
            div_le_div_of_nonneg_right (by norm_num) (le_of_lt hs3)
          exact mul_le_mul_of_nonneg_right hkey (norm_nonneg _)

end

end Work.EQ.FanTri
