import Mathlib

namespace Work.OddVolterra.Free

/-- **The chord upper bound** for a strictly concave profile with `f 0 = 1` and `f (∓1) = 0`:
`f t ≤ 1 + |t|` for `|t| < 1`.

The two cases are the secant-slope monotonicity of a strictly concave function:
for `0 < t < 1` compare the secant slopes on `[-1, 0]` (which is `1`) and on `[0, t]`;
for `-1 < t < 0` compare the secant slopes on `[t, 0]` and on `[0, 1]` (which is `-1`). -/
theorem profileLeOneAddAbs {f : ℝ → ℝ}
    (h : StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) f) (h0 : f 0 = 1) (h1 : f 1 = 0)
    (hm : f (-1) = 0) {t : ℝ} (ht : |t| < 1) : f t ≤ 1 + |t| := by
  have hmem1 : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  have hmemm1 : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  rcases lt_trichotomy t 0 with ht0 | ht0 | ht0
  · -- `t < 0`: compare the secant slopes on `[t, 0]` and on `[0, 1]`.
    have ht_lo : -1 < t := (abs_lt.mp ht).1
    have hmemt : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_of_lt ht_lo, by linarith⟩
    have hkey := h.slope_anti_adjacent hmemt hmem1 ht0 (by norm_num : (0 : ℝ) < 1)
    rw [h1, h0, show (0 : ℝ) - 1 = -1 by norm_num, show (1 : ℝ) - 0 = 1 by norm_num,
      div_one, show (0 : ℝ) - t = -t by ring] at hkey
    -- hkey : -1 < (1 - f t) / (-t)
    rw [abs_of_neg ht0]
    have htpos : (0 : ℝ) < -t := by linarith
    have h2 := mul_lt_mul_of_pos_right hkey htpos
    rw [div_mul_cancel₀ (1 - f t) (ne_of_gt htpos)] at h2
    linarith
  · -- `t = 0`
    rw [ht0, abs_zero, add_zero]
    exact h0.le
  · -- `t > 0`: compare the secant slopes on `[-1, 0]` and on `[0, t]`.
    have ht_hi : t < 1 := (abs_lt.mp ht).2
    have hmemt : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, le_of_lt ht_hi⟩
    have hkey := h.slope_anti_adjacent hmemm1 hmemt (by norm_num : (-1 : ℝ) < 0) ht0
    rw [h0, hm, show (t : ℝ) - 0 = t by ring, show (1 : ℝ) - 0 = 1 by norm_num,
      show (0 : ℝ) - (-1) = 1 by norm_num, div_one] at hkey
    -- hkey : (f t - 1) / t < 1
    rw [abs_of_pos ht0]
    have h2 := mul_lt_mul_of_pos_right hkey ht0
    rw [div_mul_cancel₀ (f t - 1) (ne_of_gt ht0)] at h2
    linarith

end Work.OddVolterra.Free
