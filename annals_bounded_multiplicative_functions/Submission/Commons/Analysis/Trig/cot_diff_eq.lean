import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Trig

theorem cot_diff_eq {a b : ℝ} (ha : 0 < a) (ha' : a < Real.pi) (hb : 0 < b) (hb' : b < Real.pi) :
    Real.cot a - Real.cot b = Real.sin (b - a) / (Real.sin a * Real.sin b) := by
  have hsa : Real.sin a ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ha ha')
  have hsb : Real.sin b ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hb hb')
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin, Real.sin_sub]
  field_simp

end Commons.Analysis.Trig