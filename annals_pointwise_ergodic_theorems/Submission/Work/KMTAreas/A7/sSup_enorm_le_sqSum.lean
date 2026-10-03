import Mathlib

namespace Work.KMTAreas.A7

open ENNReal

/-- The `ℓ²`-norm controls the `ℓ^∞`-norm: the supremum of the extended norms `‖a n‖ₑ`
is at most the square root of the sum of the squares of the extended norms.  This is the
elementary pointwise bound used to extract a maximal (i.e. `ℓ^∞`) estimate from a
square-function (i.e. `ℓ²`) estimate. -/
theorem sSup_enorm_le_sqSum (a : ℕ → ℂ) :
    (⨆ n, ‖a n‖ₑ) ≤ (∑' n : ℕ, ‖a n‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  apply iSup_le
  intro n
  have h2 : ‖a n‖ₑ ^ (2:ℝ) ≤ ∑' k : ℕ, ‖a k‖ₑ ^ (2:ℝ) := by
    exact ENNReal.le_tsum (f := fun k : ℕ => ‖a k‖ₑ ^ (2:ℝ)) n
  calc ‖a n‖ₑ = (‖a n‖ₑ ^ (2:ℝ)) ^ (1/2:ℝ) := by
        rw [← ENNReal.rpow_mul]; norm_num
    _ ≤ (∑' k : ℕ, ‖a k‖ₑ ^ (2:ℝ)) ^ (1/2:ℝ) :=
        ENNReal.rpow_le_rpow h2 (by norm_num)

end Work.KMTAreas.A7
