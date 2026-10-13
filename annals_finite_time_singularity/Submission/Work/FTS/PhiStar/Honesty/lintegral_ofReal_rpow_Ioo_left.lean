import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

theorem lintegral_ofReal_rpow_Ioo_left {r t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hr : r < -1) :
    (∫⁻ z in Set.Ioo t 1, ENNReal.ofReal (z ^ r))
      = ENNReal.ofReal ((1 - t ^ (r + 1)) / (r + 1)) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc t 1 := by
    rw [Set.uIcc_of_le ht1]
    exact fun h => absurd h.1 (not_le.mpr ht)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [MeasureTheory.restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le ht1]
    rw [integral_rpow (Or.inr ⟨ne_of_lt hr, h0⟩), Real.one_rpow]
  · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le ht1).mp
      (intervalIntegral.intervalIntegrable_rpow (μ := MeasureTheory.volume) (Or.inr h0))
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
    exact Real.rpow_nonneg (le_trans ht.le hx.1.le) r

end Work.FTS.PhiStar.Honesty
