import Mathlib

namespace Work.Mostow

/-- The squared chord / cosine identity on the circle `ℝ/2πℤ`:
`(2 sin(‖t‖/2))^2 = 2 - 2 cos t`, where `‖t‖` is the distance of `t` to the nearest
multiple of `2π`.  The point is that `cos` and `sin(·/2)^2` only depend on `t` through
its class in `AddCircle (2π)`. -/
theorem chordCoeSq (t : ℝ) :
    (2 * Real.sin (‖(t : AddCircle (2 * Real.pi))‖ / 2)) ^ 2 = 2 - 2 * Real.cos t := by
  set s : ℝ := (2 * Real.pi)⁻¹ * t with hs
  set k : ℤ := round s with hk
  have ht_eq : t = 2 * Real.pi * s := by
    rw [hs, ← mul_assoc, mul_inv_cancel₀ (by positivity : (2 * Real.pi) ≠ 0), one_mul]
  have hq_abs : ‖(t : AddCircle (2 * Real.pi))‖ = |t - (k : ℝ) * (2 * Real.pi)| := by
    rw [AddCircle.norm_eq (2 * Real.pi)]
  have hcos : Real.cos ‖(t : AddCircle (2 * Real.pi))‖ = Real.cos t := by
    rw [hq_abs, Real.cos_abs, Real.cos_sub_int_mul_two_pi]
  have hgen : ∀ x : ℝ, (2 * Real.sin x) ^ 2 = 2 - 2 * Real.cos (2 * x) := by
    intro x
    rw [Real.cos_two_mul', Real.cos_sq']
    ring
  rw [hgen (‖(t : AddCircle (2 * Real.pi))‖ / 2)]
  rw [show 2 * (‖(t : AddCircle (2 * Real.pi))‖ / 2) = ‖(t : AddCircle (2 * Real.pi))‖ by ring,
    hcos]

end Work.Mostow
