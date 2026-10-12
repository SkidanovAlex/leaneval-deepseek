import Mathlib.Analysis.CStarAlgebra.Classes
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- Gauge bookkeeping: if `u * conj u = 1`, i.e. `u` is a unit-modulus complex number,
then the gauge factors carried by the `p` creation / `q` annihilation powers cancel,
leaving only the radial factor `r^(p+q)`. -/
theorem gaugeCoeff (u : ℂ) (hu : u * starRingEnd ℂ u = 1) (r : ℝ) (p q : ℕ) :
    ((r : ℂ) * u) ^ p * (starRingEnd ℂ ((r : ℂ) * u)) ^ q * u ^ ((q : ℤ) - (p : ℤ))
      = (r : ℂ) ^ (p + q) := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h] at hu
    simp at hu
  -- `u` has unit modulus, so its conjugate is its inverse
  have hsu : starRingEnd ℂ u = u⁻¹ := eq_inv_of_mul_eq_one_right hu
  rw [map_mul, Complex.conj_ofReal, hsu]
  rw [mul_pow, mul_pow, inv_pow]
  -- convert the integer power to a ratio of natural powers
  have hz : u ^ ((q : ℤ) - (p : ℤ)) = u ^ q * (u ^ p)⁻¹ := by
    rw [zpow_sub₀ hu0, div_eq_mul_inv, zpow_natCast, zpow_natCast]
  rw [hz, pow_add]
  field_simp

end Work.BoseBoxFock
