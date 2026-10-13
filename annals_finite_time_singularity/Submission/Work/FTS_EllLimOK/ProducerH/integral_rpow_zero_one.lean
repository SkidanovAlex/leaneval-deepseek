import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH

/-- `∫₀¹ v^β dv = 1/(β+1)` for `β > -1` (immediate from `integral_rpow`). -/
theorem integral_rpow_zero_one {β : ℝ} (hβ : -1 < β) :
    ∫ v in (0 : ℝ)..1, v ^ β = 1 / (β + 1) := by
  rw [integral_rpow (Or.inl hβ), Real.one_rpow, Real.zero_rpow (by linarith : (β + 1) ≠ 0)]
  ring

end Work.FTS_EllLimOK.ProducerH
