import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

/-- For `1 ≤ c` and `κ < c · δ^{1/2}` with `κ, δ > 0`, raising to the power `3/4`
gives `κ^{3/4} < c · δ^{3/8}`: the extra factor `c^{3/4} ≤ c` is absorbed by `1 ≤ c`. -/
theorem step8_delta_bound {κ c δ : ℝ} (hκ0 : 0 < κ) (hδ0 : 0 < δ) (hc : 1 ≤ c)
    (hκ : κ < c * δ ^ (1 / 2 : ℝ)) : κ ^ (3 / 4 : ℝ) < c * δ ^ (3 / 8 : ℝ) := by
  -- Monotonicity of `x ↦ x^(3/4)` on `[0,∞)` applied to the hypothesis.
  have h1 : κ ^ (3 / 4 : ℝ) < (c * δ ^ (1 / 2 : ℝ)) ^ (3 / 4 : ℝ) :=
    Real.rpow_lt_rpow hκ0.le hκ (by norm_num)
  -- Distribute the power over the product: `(c * δ^{1/2})^{3/4} = c^{3/4} * δ^{3/8}`.
  have h2 : (c * δ ^ (1 / 2 : ℝ)) ^ (3 / 4 : ℝ) = c ^ (3 / 4 : ℝ) * δ ^ (3 / 8 : ℝ) := by
    rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg hδ0.le _)]
    congr 1
    rw [← Real.rpow_mul hδ0.le]
    norm_num
  -- The leftover factor `c^{3/4}` is at most `c` because `1 ≤ c`.
  have h3 : c ^ (3 / 4 : ℝ) * δ ^ (3 / 8 : ℝ) ≤ c * δ ^ (3 / 8 : ℝ) :=
    mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le hc (by norm_num))
      (Real.rpow_nonneg hδ0.le _)
  linarith

end Work.EKLC8Core
