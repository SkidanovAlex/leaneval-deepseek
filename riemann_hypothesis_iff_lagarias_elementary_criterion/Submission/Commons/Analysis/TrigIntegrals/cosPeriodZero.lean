import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Commons.Analysis.TrigIntegrals

theorem cosPeriodZero :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos θ) = 0 := by
  rw [integral_cos]
  simp

end Commons.Analysis.TrigIntegrals