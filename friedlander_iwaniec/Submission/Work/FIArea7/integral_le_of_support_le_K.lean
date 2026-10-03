import Mathlib

namespace Work.FIArea7

/-- If `g` is continuous, supported on `[a, b]`, and bounded above by `K ≥ 0`,
then its integral over any interval `[x, y]` is at most `K * (b - a)`. -/
theorem integral_le_of_support_le_K {g : ℝ → ℝ} {a b K x y : ℝ} (hg : Continuous g)
    (hab : a ≤ b) (hK : 0 ≤ K) (hsupp : ∀ u, u ∉ Set.Icc a b → g u = 0)
    (hbd : ∀ u, g u ≤ K) (hxy : x ≤ y) :
    ∫ t in x..y, g t ≤ K * (b - a) := by
  -- `g` is pointwise dominated by `K` times the indicator of `[a, b]`.
  have hbound : ∀ t, g t ≤ (Set.Icc a b).indicator (fun _ => K) t := by
    intro t
    by_cases ht : t ∈ Set.Icc a b
    · rw [Set.indicator_of_mem ht]; exact hbd t
    · rw [Set.indicator_of_notMem ht]; exact le_of_eq (hsupp t ht)
  -- The dominating function is integrable: it is bounded and supported on `[a, b]`.
  have hint : MeasureTheory.Integrable (fun t => (Set.Icc a b).indicator (fun _ => K) t) := by
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Icc]
    refine MeasureTheory.integrableOn_const ?_ ?_
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    · exact enorm_ne_top
  -- Monotonicity of the interval integral.
  have h2 : ∫ t in x..y, g t ≤ ∫ t in x..y, (Set.Icc a b).indicator (fun _ => K) t := by
    apply intervalIntegral.integral_mono hxy
    · exact hg.intervalIntegrable x y
    · exact hint.intervalIntegrable
    · exact hbound
  -- Bound the integral of the indicator by `K * (b - a)`.
  have h3 : ∫ t in x..y, (Set.Icc a b).indicator (fun _ => K) t ≤ K * (b - a) := by
    rw [intervalIntegral.integral_of_le hxy]
    calc ∫ t in Set.Ioc x y, (Set.Icc a b).indicator (fun _ => K) t
        ≤ ∫ t, (Set.Icc a b).indicator (fun _ => K) t := by
          apply MeasureTheory.setIntegral_le_integral hint
          exact Filter.Eventually.of_forall (Set.indicator_nonneg (fun _ _ => hK))
      _ = K * (b - a) := by
          rw [MeasureTheory.integral_indicator_const K measurableSet_Icc, Real.volume_real_Icc,
              max_eq_left (sub_nonneg.mpr hab), smul_eq_mul, mul_comm]
  exact le_trans h2 h3

end Work.FIArea7
