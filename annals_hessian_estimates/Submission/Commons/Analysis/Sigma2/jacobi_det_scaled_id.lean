import Mathlib

namespace Commons.Analysis.Sigma2

theorem jacobi_det_scaled_id (S f δ : ℝ) (hS : S ≠ 0) (hD : 3 * S ^ 2 - 2 ≠ 0) :
    (9 - 6 * (1 - f ^ 2 / (3 * S ^ 2 - 2)) -
        3 * (1 + δ * f / S) * (1 - 6 / (3 * S ^ 2 - 2)) +
        2 * (1 + δ * f / S) *
          ((1 - f ^ 2 / (3 * S ^ 2 - 2)) * (1 - 6 / (3 * S ^ 2 - 2)) -
            (1 - 3 * S * f / (3 * S ^ 2 - 2)) ^ 2)) *
          (3 * S ^ 2 - 2) * S =
      f * ((12 - 9 * δ) * S ^ 2 + (12 * δ - 2) * S * f - 8 * δ * f ^ 2) + 6 * S + 12 * δ * f := by
  field_simp [hS, hD]
  ring

end Commons.Analysis.Sigma2
