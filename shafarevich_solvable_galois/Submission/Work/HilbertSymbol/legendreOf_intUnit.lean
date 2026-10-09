import Mathlib
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

open scoped Classical

/-- For a nonzero integer `m` not divisible by the prime `p`, the `p`-adic valuation of
`m`, viewed in `ℚˣ`, vanishes. -/
theorem padicVal_intUnit {p : ℕ} [Fact p.Prime] {m : ℤ} (hm : m ≠ 0)
    (h : ¬ (p : ℤ) ∣ m) : padicVal p (intUnit m hm) = 0 := by
  rw [padicVal, intUnit_coe, padicValRat.of_int]
  exact_mod_cast padicValInt.eq_zero_of_not_dvd h

/-- The `p`-adic unit part of a nonzero integer `m` not divisible by `p` is the image of `m`
in `ℤ_[p]`. -/
theorem unitPart_intUnit_eq {p : ℕ} [Fact p.Prime] {m : ℤ} (hm : m ≠ 0)
    (h : ¬ (p : ℤ) ∣ m) : (unitPart p (intUnit m hm) : ℤ_[p]) = (m : ℤ_[p]) := by
  refine PadicInt.ext ?_
  rw [unitPart_of_padicVal_eq_zero (padicVal_intUnit hm h),
    show ((intUnit m hm : ℚˣ) : ℚ) = (m : ℚ) from intUnit_coe m hm]
  norm_cast

/-- The reduction modulo `p` of the `p`-adic unit part of a nonzero integer `m` not divisible
by `p` is `m` itself. -/
theorem legendreUnit_intUnit {p : ℕ} [Fact p.Prime] {m : ℤ} (hm : m ≠ 0)
    (h : ¬ (p : ℤ) ∣ m) :
    ((Units.map (PadicInt.toZMod (p := p)) (unitPart p (intUnit m hm)) : (ZMod p)ˣ) : ZMod p)
      = (m : ZMod p) := by
  conv_lhs => rw [Units.coe_map]
  rw [show ((unitPart p (intUnit m hm) : ℤ_[p])) = (m : ℤ_[p]) from unitPart_intUnit_eq hm h]
  exact map_intCast (PadicInt.toZMod (p := p)) m

/-- The Legendre symbol of a nonzero integer `m` not divisible by the prime `p`, computed on the
`p`-adic unit part of `m`, is the ordinary Legendre symbol of `m`. -/
theorem legendreOf_intUnit {p : ℕ} [Fact p.Prime] {m : ℤ} (hm : m ≠ 0)
    (h : ¬ (p : ℤ) ∣ m) :
    legendreOf p (intUnit m hm) = intUnitOf (legendreSym p m) := by
  rw [legendreOf, legendreUnit, quadCharUnit, legendreUnit_intUnit hm h]
  rfl

end Work.HilbertSymbol
