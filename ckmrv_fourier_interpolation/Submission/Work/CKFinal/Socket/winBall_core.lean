import Mathlib

namespace Work.CKFinal.Socket

/-- Core real-arithmetic estimate for the "winning ball" perturbation used in the
Fourier interpolation argument.  Given `0 < s`, `0 < y`, `0 ≤ d`,
`d < min s s⁻¹ / 16` and the two quadratic bounds
`(x-1)^2 ≤ 4 y s d^2`, `(y-s)^2 ≤ 4 y s d^2`, we deduce that `x` stays close to
`1` (within `min (y^2) 1 / 4`) and that `y` stays within a factor `(16/15)^2` of `s`. -/
theorem winBall_core (s x y d : ℝ) (hs : 0 < s) (hy : 0 < y) (hd0 : 0 ≤ d)
    (hd : d < min s s⁻¹ / 16)
    (hx : (x - 1) ^ 2 ≤ 4 * y * s * d ^ 2)
    (hyy : (y - s) ^ 2 ≤ 4 * y * s * d ^ 2) :
    |x - 1| < min (y ^ 2) 1 / 4 ∧ (15 / 16) ^ 2 * s ≤ y ∧ y ≤ (16 / 15) ^ 2 * s := by
  have hsne : s ≠ 0 := ne_of_gt hs
  -- `min s s⁻¹ ≤ 1`
  have hmin_le_one : min s s⁻¹ ≤ 1 := by
    rcases le_total s 1 with h | h
    · exact le_trans (min_le_left _ _) h
    · exact le_trans (min_le_right _ _) (inv_le_one_of_one_le₀ h)
  -- hence `d < 1/16` and `d^2 < 1/256`
  have hd1 : d < 1 / 16 := lt_of_lt_of_le hd (div_le_div_of_nonneg_right hmin_le_one (by norm_num))
  have hd2 : d ^ 2 < 1 / 256 := by
    have h := pow_lt_pow_left₀ hd1 hd0 (by norm_num : (2 : ℕ) ≠ 0)
    norm_num at h; exact h
  -- the quadratic relation for `y`
  have hys : 64 * (y - s) ^ 2 < y * s := by
    have h4 : 4 * y * s * d ^ 2 < 4 * y * s * (1 / 256) :=
      mul_lt_mul_of_pos_left hd2 (by positivity)
    have e : 4 * y * s * (1 / 256) = y * s / 64 := by ring
    linarith [hyy, h4, e]
  have hy_lower : (225 : ℝ) / 256 * s ≤ y := by
    by_contra hlt
    have hlt' : y < 225 / 256 * s := not_le.mp hlt
    nlinarith [sq_nonneg s]
  have hy_upper : y ≤ (256 : ℝ) / 225 * s := by
    by_contra hlt
    have hlt' : 256 / 225 * s < y := not_le.mp hlt
    nlinarith [sq_nonneg s]
  have hmu : (1 : ℝ) ≤ 4 * ((225 : ℝ) / 256) ^ 3 := by norm_num
  refine ⟨?_, ?_, ?_⟩
  · -- the `x`-estimate
    have hkey : (x - 1) ^ 2 < (min (y ^ 2) 1) ^ 2 / 16 := by
      rcases le_total s 1 with hs1 | hs1
      · -- case `s ≤ 1`
        have hdm : d < s / 16 :=
          lt_of_lt_of_le hd (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
        have hd2m : d ^ 2 < s ^ 2 / 256 := by
          have h := pow_lt_pow_left₀ hdm hd0 (by norm_num : (2 : ℕ) ≠ 0)
          have e : (s / 16 : ℝ) ^ 2 = s ^ 2 / 256 := by ring
          rwa [e] at h
        have hbnd : (x - 1) ^ 2 < y * s ^ 3 / 64 := by
          have h4 : 4 * y * s * d ^ 2 < 4 * y * s * (s ^ 2 / 256) :=
            mul_lt_mul_of_pos_left hd2m (by positivity)
          have e : 4 * y * s * (s ^ 2 / 256) = y * s ^ 3 / 64 := by ring
          linarith [hx, h4, e]
        rcases le_total y 1 with hy1 | hy1
        · have hy2le : y ^ 2 ≤ 1 := by nlinarith [hy1, hy]
          rw [min_eq_left hy2le]
          have hs3 : s ^ 3 ≤ 4 * y ^ 3 := by
            have h1 : ((225 : ℝ) / 256 * s) ^ 3 ≤ y ^ 3 :=
              pow_le_pow_left₀ (by positivity) hy_lower 3
            have e : ((225 : ℝ) / 256 * s) ^ 3 = ((225 : ℝ) / 256) ^ 3 * s ^ 3 := by ring
            rw [e] at h1
            nlinarith [h1, hmu, pow_nonneg hs.le 3]
          have hmul : y * s ^ 3 ≤ y * (4 * y ^ 3) := mul_le_mul_of_nonneg_left hs3 hy.le
          have hcmp : y * s ^ 3 / 64 ≤ (y ^ 2) ^ 2 / 16 := by linarith [hmul]
          linarith [hbnd, hcmp]
        · have h1le : 1 ≤ y ^ 2 := by nlinarith [hy1, hy]
          rw [min_eq_right h1le]
          have hs4 : s ^ 4 ≤ 1 := pow_le_one₀ hs.le hs1
          have h2 : (256 : ℝ) / 225 * s * s ^ 3 ≤ 4 := by
            have e : (256 : ℝ) / 225 * s * s ^ 3 = (256 : ℝ) / 225 * s ^ 4 := by ring
            rw [e]; nlinarith [hs4]
          have hmul : y * s ^ 3 ≤ (256 : ℝ) / 225 * s * s ^ 3 :=
            mul_le_mul_of_nonneg_right hy_upper (by positivity)
          have hys3 : y * s ^ 3 ≤ 4 := le_trans hmul h2
          have hcmp : y * s ^ 3 / 64 ≤ 1 / 16 := by
            rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 64)]
            linarith [hys3]
          linarith [hbnd, hcmp]
      · -- case `1 ≤ s`
        have hdm : d < s⁻¹ / 16 :=
          lt_of_lt_of_le hd (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
        have hsd : s * d < 1 / 16 := by
          have h := mul_lt_mul_of_pos_left hdm hs
          rwa [show s * (s⁻¹ / 16) = 1 / 16 by rw [← mul_div_assoc, mul_inv_cancel₀ hsne]] at h
        have hsd2 : (s * d) ^ 2 < 1 / 256 := by
          have h := pow_lt_pow_left₀ hsd (by positivity : (0 : ℝ) ≤ s * d)
            (by norm_num : (2 : ℕ) ≠ 0)
          norm_num at h; exact h
        have hbnd : (x - 1) ^ 2 < y / (64 * s) := by
          rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 64 * s)]
          have h1 : (x - 1) ^ 2 * (64 * s) ≤ 256 * y * (s * d) ^ 2 := by
            calc (x - 1) ^ 2 * (64 * s) ≤ (4 * y * s * d ^ 2) * (64 * s) :=
                  mul_le_mul_of_nonneg_right hx (by positivity)
              _ = 256 * y * (s * d) ^ 2 := by ring
          have h2 : 256 * y * (s * d) ^ 2 < y := by
            have := mul_lt_mul_of_pos_left hsd2 (by positivity : (0 : ℝ) < 256 * y)
            have e2 : 256 * y * (1 / 256) = y := by ring
            linarith [this, e2]
          linarith [h1, h2]
        rcases le_total y 1 with hy1 | hy1
        · have hy2le : y ^ 2 ≤ 1 := by nlinarith [hy1, hy]
          rw [min_eq_left hy2le]
          have h1 : (225 : ℝ) / 256 ≤ y := by nlinarith [hy_lower, hs1]
          have h1p : ((225 : ℝ) / 256) ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
          have hkey1 : (1 : ℝ) ≤ 4 * s * y ^ 3 := by
            nlinarith [h1p, hmu, hs1, pow_nonneg hy.le 3]
          have hcmp : y / (64 * s) ≤ (y ^ 2) ^ 2 / 16 := by
            rw [div_le_iff₀ (by positivity : (0 : ℝ) < 64 * s)]
            have hm : (1 : ℝ) * y ≤ (4 * s * y ^ 3) * y :=
              mul_le_mul_of_nonneg_right hkey1 hy.le
            linarith [hm]
          linarith [hbnd, hcmp]
        · have h1le : 1 ≤ y ^ 2 := by nlinarith [hy1, hy]
          rw [min_eq_right h1le]
          have hcmp : y / (64 * s) ≤ 1 / 16 := by
            rw [div_le_iff₀ (by positivity : (0 : ℝ) < 64 * s)]
            have : y ≤ 4 * s := by nlinarith [hy_upper]
            linarith [this]
          linarith [hbnd, hcmp]
    have hmin_nonneg : 0 ≤ min (y ^ 2) 1 := le_min (by positivity) (by norm_num)
    have hc_nn : 0 ≤ min (y ^ 2) 1 / 4 := div_nonneg hmin_nonneg (by norm_num)
    have hsq : (min (y ^ 2) 1 / 4) ^ 2 = (min (y ^ 2) 1) ^ 2 / 16 := by ring
    have hfin : |x - 1| < |min (y ^ 2) 1 / 4| := by
      rw [← sq_lt_sq, hsq]; exact hkey
    rw [abs_of_nonneg hc_nn] at hfin
    exact hfin
  · have e : (15 / 16 : ℝ) ^ 2 = 225 / 256 := by norm_num
    rw [e]; exact hy_lower
  · have e : (16 / 15 : ℝ) ^ 2 = 256 / 225 := by norm_num
    rw [e]; exact hy_upper

end Work.CKFinal.Socket
