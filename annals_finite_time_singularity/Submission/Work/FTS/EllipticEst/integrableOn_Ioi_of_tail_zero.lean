import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

/-- A function on `(0, ∞)` which is a.e. strongly measurable, bounded by `M`, and which
vanishes past a finite point `b` is integrable on `(0, ∞)`: it is dominated (a.e.) by the
constant `M` on the finite-measure interval `(0, b]` and by `0` beyond it. -/
theorem integrableOn_Ioi_of_tail_zero {f : ℝ → ℝ} {b M : ℝ}
    (hmeas : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hbdd : ∀ z ∈ Set.Ioi (0 : ℝ), ‖f z‖ ≤ M)
    (hzero : ∀ z ∈ Set.Ioi (0 : ℝ), b < z → f z = 0) :
    MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
  have hM : 0 ≤ M := by
    have h1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by simp
    have hb := hbdd 1 h1
    have hn := norm_nonneg (f 1)
    linarith
  -- Dominating function: the constant `M` on `(0, b]`, zero elsewhere.
  set g : ℝ → ℝ := (Set.Ioc 0 b).indicator (fun _ => M) with hg_def
  have hg_int : MeasureTheory.Integrable g (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    rw [hg_def]
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Ioc]
    rw [MeasureTheory.IntegrableOn]
    rw [MeasureTheory.Measure.restrict_restrict_of_subset
      (Set.Ioc_subset_Ioi_self (a := b) (b := (0 : ℝ)))]
    exact MeasureTheory.integrableOn_const
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  refine hg_int.mono' hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
  rw [hg_def]
  by_cases hzb : z ∈ Set.Ioc 0 b
  · rw [Set.indicator_of_mem hzb]
    exact hbdd z hz
  · rw [Set.indicator_of_notMem hzb]
    have hb_lt : b < z := by
      have h := hzb
      rw [Set.mem_Ioc, not_and] at h
      exact not_le.mp (h hz)
    rw [hzero z hz hb_lt]
    simp

end Work.FTS.EllipticEst
