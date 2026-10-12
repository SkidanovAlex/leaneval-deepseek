import Mathlib.Analysis.Complex.ExponentialBounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- `D ≤ 2^{-10·1292}` whenever `D^{1/1292} ≤ 2^{-10}`, hence `log (1/D) ≥ 12920 log 2 ≥ 231`.
The constant `231` is far from sharp: `1 ≤ log 1024` alone suffices, since then
`(1/1292)·log D ≤ log (1/1024) = -log 1024 ≤ -1`, so `log (1/D) = -log D ≥ 1292 ≥ 231`. -/
theorem bogL_ge {D : ℝ} (hD0 : 0 < D) (hDs : D ^ ((1 : ℝ) / 1292) ≤ 1 / 1024) : 231 ≤ Real.log (1 / D) := by
  -- take logarithms of `D ^ (1/1292) ≤ 1/1024`
  have hlog : Real.log (D ^ ((1 : ℝ) / 1292)) ≤ Real.log (1 / 1024) :=
    Real.log_le_log (Real.rpow_pos_of_pos hD0 _) hDs
  rw [Real.log_rpow hD0] at hlog
  -- `log (1/1024) ≤ -1` because `exp 1 < 3 ≤ 1024`
  have h1024 : Real.log (1 / 1024) ≤ -1 := by
    have h : Real.log ((1 : ℝ) / 1024) = -Real.log 1024 := by
      rw [one_div, Real.log_inv]
    rw [h]
    have h1 : (1 : ℝ) ≤ Real.log 1024 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 1024)]
      linarith [Real.exp_one_lt_three]
    linarith
  have hDle : Real.log D ≤ -1292 := by linarith [hlog, h1024]
  have hfin : Real.log (1 / D) = -Real.log D := by
    rw [one_div, Real.log_inv]
  rw [hfin]
  linarith

end Work.BoseBogFS
