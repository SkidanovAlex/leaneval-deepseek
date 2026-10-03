import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Normed.Module.Connected

namespace Commons.Analysis.Complex.Analytic

theorem eventually_eq_of_re_eq_zero {F : ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F z)
    (h : ∀ᶠ w in nhds z, (F w).re = 0) : ∀ᶠ w in nhds z, F w = F z := by
  have hmem : {w | (F w).re = 0} ∩ {w | AnalyticAt ℂ F w} ∈ nhds z :=
    Filter.inter_mem h ((isOpen_analyticAt ℂ F).mem_nhds hF)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hmem
  have hAnalytic : AnalyticOnNhd ℂ F (Metric.ball z r) := fun w hw => (hball hw).2
  have hre : ∀ w ∈ Metric.ball z r, (F w).re = 0 := fun w hw => (hball hw).1
  obtain ⟨c, hc⟩ := AnalyticOnNhd.eq_const_of_re_eq_const hAnalytic hre Metric.isOpen_ball
    (Metric.isConnected_ball hr)
  refine Filter.eventually_of_mem (Metric.ball_mem_nhds z hr) fun w hw => ?_
  rw [hc w hw, hc z (Metric.mem_ball_self hr)]

end Commons.Analysis.Complex.Analytic