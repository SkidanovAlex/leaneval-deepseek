import Mathlib
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

open scoped Classical

/-- A nonzero rational number `q` is the product of the integer `q.num * q.den` and the square
`(1 / q.den) ^ 2`. -/
private theorem rat_eq_int_mul_sq (q : ℚ) (hq : q ≠ 0) :
    q = ((q.num * (q.den : ℤ) : ℤ) : ℚ) * (((q.den : ℤ) : ℚ))⁻¹ ^ 2 := by
  have hn : ((q.den : ℤ) : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  nth_rewrite 1 [← Rat.num_div_den q]
  push_cast
  field_simp

/-- Every nonzero rational number is the product of a nonzero integer and a square: its square
class is represented by an integer. -/
theorem exists_intUnit_mul_sq (a : ℚˣ) :
    ∃ (A : ℤ) (hA : A ≠ 0) (c : ℚˣ), a = intUnit A hA * c ^ 2 := by
  refine ⟨(a : ℚ).num * ((a : ℚ).den : ℤ), ?_,
    (intUnit ((a : ℚ).den : ℤ) ?_)⁻¹, ?_⟩
  · exact mul_ne_zero (Rat.num_ne_zero.mpr a.ne_zero)
      (by exact_mod_cast Rat.den_ne_zero (a : ℚ))
  · exact_mod_cast Rat.den_ne_zero (a : ℚ)
  · apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
      intUnit_coe]
    exact rat_eq_int_mul_sq (a : ℚ) a.ne_zero

end Work.HilbertSymbol
