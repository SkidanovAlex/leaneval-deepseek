import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

theorem lintegral_ofReal_rpow_Ioo (p t : ℝ) (hp : 0 < p) (ht : 1 ≤ t) :
    ∫⁻ z in Set.Ioo (1 : ℝ) t, ENNReal.ofReal (z ^ p)
      = ENNReal.ofReal ((t ^ (p + 1) - 1) / (p + 1)) := by
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [MeasureTheory.restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le ht]
    rw [integral_rpow (Or.inl (by linarith))]
    simp
  · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ht).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    exact Real.rpow_nonneg (le_trans zero_le_one hx.1.le) p

end Work.FTS.PhiStar.Honesty
