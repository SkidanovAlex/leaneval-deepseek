import Mathlib.Analysis.SpecialFunctions.Arsinh

namespace Commons.Analysis.Real

/-- `arsinh x ≤ x` for `x ≥ 0` (arsinh is concave, tangent at `0`). -/
theorem arsinh_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.arsinh x ≤ x := by
  have h : Real.arsinh x ≤ Real.sinh (Real.arsinh x) :=
    Real.self_le_sinh_iff.mpr (Real.arsinh_nonneg_iff.mpr hx)
  rwa [Real.sinh_arsinh] at h

end Commons.Analysis.Real