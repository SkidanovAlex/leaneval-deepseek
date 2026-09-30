import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.TrigIntegrals

theorem cosPeriodZero :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos θ) = 0 := by
  rw [integral_cos]
  simp

end Commons.Analysis.TrigIntegrals