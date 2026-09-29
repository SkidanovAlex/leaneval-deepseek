import Mathlib

namespace Work.TMC13

theorem ref_scale_div_norm (a b w : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hw : w ≠ 0) (hn : ‖w‖ = 1) :
    w * (a / (↑‖a‖ : ℂ)) * (b / (↑‖b‖ : ℂ)) = (a * w * b) / (↑‖a * w * b‖ : ℂ) := by
  have hnorm : ‖a * w * b‖ = ‖a‖ * ‖b‖ := by
    rw [norm_mul, norm_mul, hn, mul_one]
  have hna : (↑‖a‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr ha
  have hnb : (↑‖b‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hb
  rw [hnorm]
  push_cast
  field_simp

end Work.TMC13
