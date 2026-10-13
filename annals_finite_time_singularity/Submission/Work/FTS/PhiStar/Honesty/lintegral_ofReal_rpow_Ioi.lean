import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

theorem lintegral_ofReal_rpow_Ioi {p z : ℝ} (hp : p < -1) (hz : 0 < z) :
    ∫⁻ t in Set.Ioi z, ENNReal.ofReal (t ^ p)
      = ENNReal.ofReal (-z ^ (p + 1) / (p + 1)) := by
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    exact integral_Ioi_rpow_of_lt hp hz
  · exact integrableOn_Ioi_rpow_of_lt hp hz
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    exact Real.rpow_nonneg (hz.trans hx).le p

end Work.FTS.PhiStar.Honesty
