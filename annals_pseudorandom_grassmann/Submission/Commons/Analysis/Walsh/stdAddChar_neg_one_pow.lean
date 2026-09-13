import Mathlib

namespace Commons.Analysis.Walsh

/-- For `a : ZMod 2`, the standard additive character `ZMod.stdAddChar a = exp (π * I * a.val)`
equals `(-1) ^ a.val`. -/
theorem stdAddChar_neg_one_pow (a : ZMod 2) :
    ZMod.stdAddChar a = (-1 : ℂ) ^ a.val := by
  have ha : a = ((a.val : ℤ) : ZMod 2) := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  conv_lhs => rw [ha]
  rw [ZMod.stdAddChar_coe, Int.cast_natCast]
  rw [show (-1 : ℂ) = Complex.exp (Real.pi * Complex.I) from Complex.exp_pi_mul_I.symm]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

end Commons.Analysis.Walsh
