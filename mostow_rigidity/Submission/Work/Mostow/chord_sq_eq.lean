import Mathlib

namespace Work.Mostow

/-- The squared chord length of an angle equals `2 - 2 cos`: writing `x` as a real number
`t = Real.Angle.toReal x` with `|t| ≤ π`, the norm on the circle is `|t|`, and the identity
reduces to `(2 sin(|t|/2))^2 = 4 sin(t/2)^2 = 2 - 2 cos t`. -/
theorem chord_sq_eq (x : AddCircle (2 * Real.pi)) :
    (2 * Real.sin (‖x‖ / 2)) ^ 2 = 2 - 2 * Real.Angle.cos x := by
  -- The norm of an angle is the absolute value of its canonical representative in `(-π, π]`.
  have hnorm : ‖x‖ = |Real.Angle.toReal x| := by
    have h2pi : (2 * Real.pi) ≠ 0 := by positivity
    have hle : |Real.Angle.toReal x| ≤ |2 * Real.pi| / 2 := by
      have h : |2 * Real.pi| / 2 = Real.pi := by
        rw [abs_of_pos Real.two_pi_pos]; ring
      rw [h]; exact Real.Angle.abs_toReal_le_pi x
    have h :=
      (AddCircle.norm_coe_eq_abs_iff (p := 2 * Real.pi) (x := Real.Angle.toReal x) h2pi).mpr hle
    have h2 : ((Real.Angle.toReal x : ℝ) : AddCircle (2 * Real.pi)) = x :=
      Real.Angle.coe_toReal x
    rw [h2] at h
    exact h
  rw [hnorm]
  have hcos : Real.Angle.cos x = Real.cos (Real.Angle.toReal x) :=
    (Real.Angle.cos_toReal x).symm
  rw [hcos]
  -- `(2 sin(t/2))^2 = 4 sin(t/2)^2 = 4 (1/2 - cos t/2) = 2 - 2 cos t`.
  have hkey :
      Real.sin (|Real.Angle.toReal x| / 2) ^ 2 =
        1 / 2 - Real.cos (Real.Angle.toReal x) / 2 := by
    rw [Real.sin_sq_eq_half_sub]
    have : (2 : ℝ) * (|Real.Angle.toReal x| / 2) = |Real.Angle.toReal x| := by ring
    rw [this, Real.cos_abs]
  rw [mul_pow, hkey]
  ring

end Work.Mostow
