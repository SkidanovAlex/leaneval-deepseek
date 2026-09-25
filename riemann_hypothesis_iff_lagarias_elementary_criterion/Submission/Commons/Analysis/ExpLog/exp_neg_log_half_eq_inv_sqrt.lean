import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.Analysis.ExpLog

lemma exp_neg_log_half_eq_inv_sqrt {x : ℝ} (hx : 0 < x) :
    Real.exp (-(Real.log x) / 2) = 1 / Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hlog : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt hx.le
  calc
    Real.exp (-(Real.log x) / 2) = Real.exp (-Real.log (Real.sqrt x)) := by
      congr 1
      rw [hlog]
      ring
    _ = 1 / Real.sqrt x := by
      rw [Real.exp_neg, Real.exp_log hs]
      field_simp [ne_of_gt hs]

end Commons.Analysis.ExpLog