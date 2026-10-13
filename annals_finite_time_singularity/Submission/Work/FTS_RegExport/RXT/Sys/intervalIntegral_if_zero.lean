import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys

theorem intervalIntegral_if_zero {f : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) :
    (∫ σ in a..b, (if σ = 0 then 0 else f σ)) = ∫ σ in a..b, f σ := by
  -- The two integrands differ only on the null set `{0}`, so their interval
  -- integrals agree (the hypothesis `ha` is not needed).
  have _ : 0 ≤ a := ha
  apply intervalIntegral.integral_congr_ae
  filter_upwards [MeasureTheory.Measure.ae_ne (MeasureTheory.volume : MeasureTheory.Measure ℝ) 0]
    with x hx _
  simp [hx]

end Work.FTS_RegExport.RXT.Sys
