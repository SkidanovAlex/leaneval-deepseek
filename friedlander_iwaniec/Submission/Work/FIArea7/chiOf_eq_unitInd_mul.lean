import Mathlib
import Submission.Work.FIArea7.addChar_extends_charMod4d
import Submission.Work.FIArea7.Section16Expansion

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

/-- `chiOf` written with the class map `unitClassD` and the unit indicator `unitInd`:
for `z` coprime to `n` the reduction `phiCoord n z` is a unit, `unitInd n z = 1`,
`unitClassD n z` is exactly that unit, and both sides are `χ` at it; for `z` not coprime
to `n` both `chiOf n χ z` and `unitInd n z` vanish. -/
theorem chiOf_eq_unitInd_mul (n : ℕ) [NeZero n]
    (χ : AddChar (Additive (Work.FIArea7.GaussUnit n)) ℂ) (z : GaussianInt) :
    Work.FIArea7.chiOf n χ z
      = Work.FIArea7.unitInd n z * χ (Additive.ofMul (Work.FIArea7.unitClassD n z)) := by
  classical
  rw [chiOf, unitInd]
  by_cases h : Nat.Coprime (Work.FIPlan.gnorm z) n
  · have hu : IsUnit (gaussNorm (phiCoord n z)) := by
      rw [gaussNorm_phiCoord]
      exact (ZMod.isUnit_iff_coprime (Work.FIPlan.gnorm z) n).mpr h
    rw [dif_pos hu, if_pos h, one_mul, unitClassD, dif_pos h]
    congr 1
  · have hu : ¬ IsUnit (gaussNorm (phiCoord n z)) := by
      rw [gaussNorm_phiCoord, ZMod.isUnit_iff_coprime]
      exact h
    rw [dif_neg hu, if_neg h, zero_mul]

end Work.FIArea7
