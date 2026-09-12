import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

namespace Commons.Analysis.Complex

/-- For unit complex numbers `u`, `z`, the squared distance from `z` to `r • u` is
`(1 - r)^2 + r * ‖u - z‖^2`. -/
lemma log_norm_dist_ratio_bound_normSq {u z : ℂ} {r : ℝ} (hu : Complex.normSq u = 1)
    (hz : Complex.normSq z = 1) :
    Complex.normSq ((r : ℂ) * u - z) = (1 - r) ^ 2 + r * Complex.normSq (u - z) := by
  rw [Complex.normSq_sub, Complex.normSq_sub, Complex.normSq_mul, hu, hz, Complex.normSq_ofReal]
  have hre : (((r : ℂ) * u) * (starRingEnd ℂ) z).re = r * (u * (starRingEnd ℂ) z).re := by
    rw [mul_assoc, Complex.re_ofReal_mul]
  rw [hre]
  ring

/-- `circleMap 0 r θ` is the scalar multiple of `circleMap 0 1 θ` by `r`. -/
lemma log_norm_dist_ratio_bound_circleMap_smul (r θ : ℝ) :
    circleMap 0 r θ = (r : ℂ) * circleMap 0 1 θ := by
  rw [circleMap_zero r θ, circleMap_zero 1 θ]
  simp

/-- The point `circleMap 0 1 θ` always has norm `1`. -/
lemma log_norm_dist_ratio_bound_norm_circleMap (θ : ℝ) : ‖circleMap 0 1 θ‖ = 1 := by
  rw [norm_circleMap_zero]
  norm_num

/-- Purely real analytic core: if `b^2 = (1-r)^2 + r a^2` with `a, b > 0` and
`1/2 ≤ r ≤ 1`, then `|log b| ≤ |log a| + log 2`. -/
lemma log_norm_dist_ratio_bound_real {a b r : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr1 : 1 / 2 ≤ r) (hr2 : r ≤ 1)
    (hkey : b ^ 2 = (1 - r) ^ 2 + r * a ^ 2) :
    |Real.log b| ≤ |Real.log a| + Real.log 2 := by
  have hsub : (1 - r) ^ 2 ≤ 1 / 4 := by nlinarith [hr1, hr2]
  have hra : r * a ^ 2 ≤ a ^ 2 := by nlinarith [hr2, sq_nonneg a]
  have hb2u : b ^ 2 ≤ 1 / 4 + a ^ 2 := by nlinarith [hkey, hsub, hra]
  have hb2l : a ^ 2 / 2 ≤ b ^ 2 := by nlinarith [hkey, hr1, sq_nonneg a]
  by_cases ha1 : 1 ≤ a
  · have hle : b ≤ 2 * a := by
      have h : b ^ 2 ≤ (2 * a) ^ 2 := by nlinarith [hb2u, ha1, sq_nonneg a]
      have h2 := (sq_le_sq (a := b) (b := 2 * a)).mp h
      rwa [abs_of_nonneg (le_of_lt hb), abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * a)] at h2
    have h2ab : (1 : ℝ) ≤ 2 * a * b := by
      have ha4 : (1 : ℝ) ≤ a ^ 2 * a ^ 2 := by
        have ha2 : (1 : ℝ) ≤ a ^ 2 := one_le_pow₀ ha1
        nlinarith [ha2, sq_nonneg a]
      have hprod : a ^ 2 * (a ^ 2 / 2) ≤ a ^ 2 * b ^ 2 :=
        mul_le_mul_of_nonneg_left hb2l (sq_nonneg a)
      have he : (2 * a * b) ^ 2 = 4 * (a ^ 2 * b ^ 2) := by ring
      have h : (1 : ℝ) ≤ (2 * a * b) ^ 2 := by rw [he]; nlinarith [hprod, ha4]
      have h2 := (one_le_sq_iff_one_le_abs (2 * a * b)).mp h
      rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * a * b)] at h2
    rw [abs_of_nonneg (Real.log_nonneg ha1)]
    by_cases hb1 : 1 ≤ b
    · rw [abs_of_nonneg (Real.log_nonneg hb1)]
      calc Real.log b ≤ Real.log (2 * a) := Real.log_le_log hb hle
        _ = Real.log a + Real.log 2 := by rw [Real.log_mul (by norm_num) (ne_of_gt ha)]; ring
    · have hb1' : b ≤ 1 := le_of_not_ge hb1
      have hlogb : Real.log b ≤ 0 := Real.log_nonpos (le_of_lt hb) hb1'
      rw [abs_of_nonpos hlogb]
      have hinv : b⁻¹ ≤ 2 * a := by
        rw [inv_le_iff_one_le_mul₀ hb]
        linarith [h2ab]
      calc -Real.log b = Real.log b⁻¹ := (Real.log_inv b).symm
        _ ≤ Real.log (2 * a) := Real.log_le_log (inv_pos.mpr hb) hinv
        _ = Real.log a + Real.log 2 := by rw [Real.log_mul (by norm_num) (ne_of_gt ha)]; ring
  · have ha1' : a ≤ 1 := le_of_not_ge ha1
    have ha2 : a ^ 2 ≤ 1 := by nlinarith [ha1', ha]
    have hle : b ≤ 2 / a := by
      have hb2 : b ≤ 2 := by
        have h : b ^ 2 ≤ (2 : ℝ) ^ 2 := by nlinarith [hb2u, ha2]
        have h2 := (sq_le_sq (a := b) (b := 2)).mp h
        rwa [abs_of_nonneg (le_of_lt hb), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h2
      rw [le_div_iff₀ ha]
      nlinarith [hb2, ha1', ha]
    have ha2b : a ≤ 2 * b := by
      have h : a ^ 2 ≤ (2 * b) ^ 2 := by nlinarith [hb2l, sq_nonneg b]
      have h2 := (sq_le_sq (a := a) (b := 2 * b)).mp h
      rwa [abs_of_nonneg (le_of_lt ha), abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * b)] at h2
    rw [abs_of_nonpos (Real.log_nonpos (le_of_lt ha) ha1')]
    by_cases hb1 : 1 ≤ b
    · rw [abs_of_nonneg (Real.log_nonneg hb1)]
      calc Real.log b ≤ Real.log (2 / a) := Real.log_le_log hb hle
        _ = -Real.log a + Real.log 2 := by rw [Real.log_div (by norm_num) (ne_of_gt ha)]; ring
    · have hb1' : b ≤ 1 := le_of_not_ge hb1
      have hlogb : Real.log b ≤ 0 := Real.log_nonpos (le_of_lt hb) hb1'
      rw [abs_of_nonpos hlogb]
      have hinv : b⁻¹ ≤ 2 / a := by
        rw [inv_le_iff_one_le_mul₀ hb]
        have hprod : 2 / a * b = 2 * b / a := by ring
        rw [hprod, le_div_iff₀ ha]
        linarith [ha2b]
      calc -Real.log b = Real.log b⁻¹ := (Real.log_inv b).symm
        _ ≤ Real.log (2 / a) := Real.log_le_log (inv_pos.mpr hb) hinv
        _ = -Real.log a + Real.log 2 := by rw [Real.log_div (by norm_num) (ne_of_gt ha)]; ring

theorem log_norm_dist_ratio_bound {z : ℂ} (hz : ‖z‖ = 1) {θ r : ℝ}
    (hr1 : 1/2 ≤ r) (hr2 : r ≤ 1) (ha : circleMap 0 1 θ ≠ z) :
    |Real.log ‖circleMap 0 r θ - z‖| ≤ |Real.log ‖circleMap 0 1 θ - z‖| + Real.log 2 := by
  set a := ‖circleMap 0 1 θ - z‖ with ha_def
  set b := ‖circleMap 0 r θ - z‖ with hb_def
  have ha_pos : 0 < a := by
    rw [ha_def]
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr ha
  have hne : circleMap 0 r θ ≠ z := by
    rcases eq_or_lt_of_le hr2 with h | h
    · rw [h]; exact ha
    · intro hc
      have hnorm : ‖circleMap 0 r θ‖ = ‖z‖ := by rw [hc]
      rw [norm_circleMap_zero, hz, abs_of_nonneg (by linarith : (0 : ℝ) ≤ r)] at hnorm
      linarith
  have hb_pos : 0 < b := by
    rw [hb_def]
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr hne
  have hkey : b ^ 2 = (1 - r) ^ 2 + r * a ^ 2 := by
    have h1 : Complex.normSq (circleMap 0 1 θ) = 1 := by
      rw [Complex.normSq_eq_norm_sq, log_norm_dist_ratio_bound_norm_circleMap]
      norm_num
    have h2 : Complex.normSq z = 1 := by
      rw [Complex.normSq_eq_norm_sq, hz]
      norm_num
    have key := log_norm_dist_ratio_bound_normSq (u := circleMap 0 1 θ) (z := z) (r := r) h1 h2
    rw [ha_def, hb_def, log_norm_dist_ratio_bound_circleMap_smul]
    simp only [Complex.sq_norm]
    exact key
  exact log_norm_dist_ratio_bound_real ha_pos hb_pos hr1 hr2 hkey

end Commons.Analysis.Complex