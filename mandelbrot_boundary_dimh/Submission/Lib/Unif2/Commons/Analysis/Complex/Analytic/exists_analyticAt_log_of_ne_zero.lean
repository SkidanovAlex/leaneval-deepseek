import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

namespace Commons.Analysis.Complex.Analytic

theorem exists_analyticAt_log_of_ne_zero {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hz : f z ≠ 0) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ ∀ᶠ w in nhds z, f w = Complex.exp (g w) := by
  refine ⟨fun w => Complex.log (f z) + Complex.log (f w / f z), ?_, ?_⟩
  · have hdiv : AnalyticAt ℂ (fun w => f w / f z) z := hf.div_const
    have hlog : AnalyticAt ℂ (fun w => Complex.log (f w / f z)) z := by
      refine hdiv.clog ?_
      rw [div_self hz]
      exact Complex.one_mem_slitPlane
    exact (analyticAt_const (v := Complex.log (f z))).add hlog
  · filter_upwards [hf.continuousAt.eventually_ne hz] with w hw
    rw [Complex.exp_add, Complex.exp_log hz, Complex.exp_log (div_ne_zero hw hz)]
    rw [mul_div_cancel₀ _ hz]

end Commons.Analysis.Complex.Analytic