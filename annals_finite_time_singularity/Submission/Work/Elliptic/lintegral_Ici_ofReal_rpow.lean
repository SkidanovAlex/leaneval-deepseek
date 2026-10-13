import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open MeasureTheory Set

theorem lintegral_Ici_ofReal_rpow {c s : ℝ} (hc : 1 < c) (hs : 0 < s) :
    ∫⁻ z in Set.Ici s, ENNReal.ofReal (z ^ (-c)) = ENNReal.ofReal (s ^ (1 - c) / (c - 1)) := by
  have ha : -c < (-1 : ℝ) := by linarith
  rw [← MeasureTheory.restrict_Ioi_eq_restrict_Ici (μ := volume) (a := s)]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (integrableOn_Ioi_rpow_of_lt (a := -c) (c := s) ha hs) ?_]
  · rw [integral_Ioi_rpow_of_lt (a := -c) (c := s) ha hs]
    congr 1
    rw [show (-c) + 1 = 1 - c by ring, show (1 : ℝ) - c = -(c - 1) by ring]
    simp only [div_neg, neg_div, neg_neg]
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (le_of_lt (hs.trans ht)) _

end Work.Elliptic
