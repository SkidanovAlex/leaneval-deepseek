import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Commons.Analysis.Real

theorem poisson_hilbert_integrand_eq {s y t : ℝ} (hs : 0 < s) (ht : t ≠ 0) :
    ((1 / Real.pi) * (s / (s ^ 2 + (y - t) ^ 2)) - (1 / Real.pi) * (s / (s ^ 2 + (y + t) ^ 2))) / t
      = (1 / Real.pi) * (4 * s * y / ((s ^ 2 + (y - t) ^ 2) * (s ^ 2 + (y + t) ^ 2))) := by
  have hA : s ^ 2 + (y - t) ^ 2 ≠ 0 := by positivity
  have hB : s ^ 2 + (y + t) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

end Commons.Analysis.Real