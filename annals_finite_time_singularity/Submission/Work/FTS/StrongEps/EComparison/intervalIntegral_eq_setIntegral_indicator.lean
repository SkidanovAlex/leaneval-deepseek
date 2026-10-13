import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

theorem intervalIntegral_eq_setIntegral_indicator {a b t : ℝ} (hat : a ≤ t) (htb : t ≤ b)
    (g : ℝ → ℝ) :
    (∫ z in t..b, g z) = ∫ z in Set.Icc a b, (if t ≤ z then g z else 0) := by
  -- the interval integral is the set integral over `Ioc t b`
  rw [intervalIntegral.integral_of_le htb,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc (x := t) (y := b)]
  -- convert both sides to integrals of indicators over `ℝ`
  rw [← MeasureTheory.integral_indicator (s := Set.Icc t b) (f := g) measurableSet_Icc,
    ← MeasureTheory.integral_indicator (s := Set.Icc a b)
      (f := fun z => if t ≤ z then g z else 0) measurableSet_Icc]
  -- the two indicators agree everywhere (both `a ≤ t` and `t ∈ Icc a b` are used)
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ Set.Icc t b
  · have hza : z ∈ Set.Icc a b := ⟨le_trans hat hz.1, hz.2⟩
    rw [Set.indicator_of_mem hz, Set.indicator_of_mem hza, ite_eq_left hz.1]
  · rw [Set.indicator_of_notMem hz]
    by_cases hzt : t ≤ z
    · have hza : z ∉ Set.Icc a b := fun h => hz ⟨hzt, h.2⟩
      rw [Set.indicator_of_notMem hza]
    · by_cases hza : z ∈ Set.Icc a b
      · rw [Set.indicator_of_mem hza, ite_eq_right hzt]
      · rw [Set.indicator_of_notMem hza]

end Work.FTS.StrongEps.EComparison
