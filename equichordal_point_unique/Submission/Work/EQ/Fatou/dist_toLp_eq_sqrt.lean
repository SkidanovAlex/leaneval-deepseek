import Mathlib

namespace Work.EQ.Fatou

open MeasureTheory

theorem dist_toLp_eq_sqrt {μ : MeasureTheory.Measure ℝ} [MeasureTheory.IsFiniteMeasure μ]
    {f h : ℝ → ℂ} (hf : MeasureTheory.MemLp f 2 μ) (hh : MeasureTheory.MemLp h 2 μ) :
    dist (hf.toLp f) (hh.toLp h) = Real.sqrt (∫ x, ‖f x - h x‖ ^ 2 ∂μ) := by
  have hInt : (∫ x, ‖f x - h x‖ ^ (ENNReal.toReal 2) ∂μ) = ∫ x, ‖f x - h x‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofNat]
    exact Real.rpow_natCast _ 2
  rw [dist_eq_norm, ← MemLp.toLp_sub hf hh, Lp.norm_toLp, MeasureTheory.toReal_eLpNorm,
    MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal (p := 2) (by norm_num) (by norm_num)
      (hf.aestronglyMeasurable.sub hh.aestronglyMeasurable)]
  simp only [Pi.sub_apply]
  rw [hInt, ENNReal.toReal_ofNat, inv_eq_one_div, Real.sqrt_eq_rpow]

end Work.EQ.Fatou
