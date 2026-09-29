import Mathlib

namespace Commons.RingTheory.Derivation

/-- The quotient rule for a derivation of a field: `D (a / b) = (D a * b - a * D b) / b ^ 2`. -/
theorem map_div {K L : Type*} [Field K] [Field L] [Algebra K L]
    (D : Derivation K L L) (a b : L) (hb : b ≠ 0) :
    D (a / b) = (D a * b - a * D b) / b ^ 2 := by
  rw [Derivation.leibniz_div, smul_eq_mul, smul_eq_mul, div_eq_mul_inv, inv_pow]
  field_simp
  ring

end Commons.RingTheory.Derivation
