import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

namespace Commons.Analysis.Complex

/-- The circle average of `log ‖z - a‖` over the unit circle equals `log⁺ ‖a‖ = max (log ‖a‖) 0`.

This is the logarithmic potential of a point mass: since `Mathlib` provides
`circleAverage_log_norm_sub_const_eq_posLog`, it suffices to rewrite `log⁺` as
`max · 0` and commute the maximum. -/
theorem circleAverage_log_norm_sub (a : ℂ) :
    Real.circleAverage (fun z : ℂ => Real.log ‖z - a‖) 0 1 = max (Real.log ‖a‖) 0 := by
  rw [circleAverage_log_norm_sub_const_eq_posLog, Real.posLog_apply, max_comm]

end Commons.Analysis.Complex
