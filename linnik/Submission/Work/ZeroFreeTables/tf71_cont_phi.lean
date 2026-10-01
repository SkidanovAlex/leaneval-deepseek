import Mathlib

namespace Work.ZeroFreeTables

theorem tf71_cont_phi (θ : ℝ) :
    Continuous (fun c : ℝ => ∫ u in (0:ℝ)..(2*θ), Real.cos (c*u) *
        ((θ - u/2 - Real.sin θ * Real.cos θ) * Real.cos u + Real.cos θ ^ 2 * (2*θ - u)
          + (Real.cos θ ^ 2 + 1/2) * Real.sin u - 2 * Real.sin θ * Real.cos θ)) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  fun_prop

end Work.ZeroFreeTables
