import Mathlib.Analysis.RCLike.Sqrt

namespace Commons.Analysis.Complex

/-- In the slit plane (or in fact for every nonzero complex `z`, by the
`z ^ 0 = 1` / `0 ^ y = 0` conventions of `Complex.cpow`), raising `z` to the
power `-1 / 2` equals the inverse of the principal square root of `z`.

Here `Complex.sqrt z = z ^ (2⁻¹ : ℂ)`, and `Complex.cpow_neg` gives
`z ^ (-y) = (z ^ y)⁻¹`. -/
lemma cpow_neg_half_eq_inv_sqrt {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    z ^ (-1 / 2 : ℂ) = (Complex.sqrt z)⁻¹ := by
  rw [show Complex.sqrt z = z ^ (2⁻¹ : ℂ) by rfl]
  rw [show (-1 / 2 : ℂ) = -((2 : ℂ)⁻¹) by norm_num]
  exact Complex.cpow_neg z (2⁻¹ : ℂ)

end Commons.Analysis.Complex