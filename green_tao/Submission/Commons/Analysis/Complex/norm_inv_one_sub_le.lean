import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Basic

namespace Commons.Analysis.Complex

/-- For a complex number `w` of norm `< 1`, the norm of the inverse of `1 - w` is at most
`(1 - ‖w‖)⁻¹`.  This follows from the reverse triangle inequality
`1 - ‖w‖ ≤ ‖1 - w‖` together with antimonotonicity of `x ↦ x⁻¹` on positive reals. -/
theorem norm_inv_one_sub_le {w : ℂ} (hw : ‖w‖ < 1) :
    ‖(1 - w)⁻¹‖ ≤ (1 - ‖w‖)⁻¹ := by
  -- `1 - ‖w‖` is positive
  have hpos : 0 < 1 - ‖w‖ := by linarith
  -- reverse triangle inequality: `‖1‖ ≤ ‖1 - w‖ + ‖w‖`, hence `1 - ‖w‖ ≤ ‖1 - w‖`
  have hmain : 1 - ‖w‖ ≤ ‖1 - w‖ := by
    have htri : ‖(1 : ℂ) - w + w‖ ≤ ‖1 - w‖ + ‖w‖ := norm_add_le (1 - w) w
    have hsum : ‖(1 : ℂ) - w + w‖ = 1 := by
      have : (1 : ℂ) - w + w = 1 := by ring
      rw [this, norm_one]
    linarith
  -- `norm_inv` identifies `‖(1 - w)⁻¹‖` with `‖1 - w‖⁻¹`, then invert the inequality
  rw [norm_inv]
  exact inv_anti₀ hpos hmain

end Commons.Analysis.Complex
