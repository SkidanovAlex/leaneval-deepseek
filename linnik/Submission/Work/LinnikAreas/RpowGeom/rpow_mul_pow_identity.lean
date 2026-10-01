import Mathlib

namespace Work.LinnikAreas.RpowGeom

/-- A rewriting identity for the geometric factor used in the Linnik argument:
for `Q > 0`, real `u` and natural `j`,
`((4)^j)⁻¹ * (Q * 2^(j+1))^u = Q^u * 2^u * (2^(u-2))^j`. -/
theorem rpow_mul_pow_identity (Q : ℝ) (hQ : 0 < Q) (u : ℝ) (j : ℕ) :
    ((4:ℝ)^j)⁻¹ * (Q * (2:ℝ)^(j+1))^u = Q^u * (2:ℝ)^u * ((2:ℝ)^(u-2))^j := by
  have h2 : (0:ℝ) < 2 := by norm_num
  have h2le : (0:ℝ) ≤ 2 := le_of_lt h2
  -- pull the product out of the `u`-th power
  have hmul : (Q * (2:ℝ)^(j+1))^u = Q^u * ((2:ℝ)^(j+1))^u :=
    Real.mul_rpow hQ.le (by positivity)
  -- turn the natural power `2^(j+1)` inside the power into a real exponent
  have h2j : ((2:ℝ)^(j+1))^u = (2:ℝ)^(((j+1:ℕ):ℝ) * u) :=
    (Real.rpow_natCast_mul h2le (j+1) u).symm
  -- `(4^j)⁻¹` is `2` raised to the real exponent `-(2j)`
  have h4 : ((4:ℝ)^j)⁻¹ = (2:ℝ)^(-((2*j:ℕ):ℝ)) := by
    have e : (4:ℝ)^j = (2:ℝ)^((2*j:ℕ):ℝ) := by
      rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, ← pow_mul, Real.rpow_natCast]
    rw [e, ← Real.rpow_neg h2le]
  -- the natural power `(2^(u-2))^j` becomes `2^((u-2)*j)`
  have hu2 : ((2:ℝ)^(u-2))^j = (2:ℝ)^((u-2)*(j:ℝ)) :=
    (Real.rpow_mul_natCast h2le (u-2) j).symm
  -- the two exponents agree
  have hexp : -((2*j:ℕ):ℝ) + ((j+1:ℕ):ℝ)*u = u + (u-2)*(j:ℝ) := by
    push_cast
    ring
  have hL : ((4:ℝ)^j)⁻¹ * (Q * (2:ℝ)^(j+1))^u
      = Q^u * (2:ℝ)^(-((2*j:ℕ):ℝ) + ((j+1:ℕ):ℝ)*u) := by
    rw [h4, hmul, h2j]
    conv_lhs =>
      rw [← mul_assoc, mul_comm ((2:ℝ)^(-((2*j:ℕ):ℝ))) (Q^u), mul_assoc,
        ← Real.rpow_add h2]
  have hR : Q^u * (2:ℝ)^u * ((2:ℝ)^(u-2))^j
      = Q^u * (2:ℝ)^(u + (u-2)*(j:ℝ)) := by
    rw [hu2, mul_assoc, ← Real.rpow_add h2]
  rw [hL, hR, hexp]

end Work.LinnikAreas.RpowGeom
