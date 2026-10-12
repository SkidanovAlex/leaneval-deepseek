import Mathlib.Analysis.SpecialFunctions.PolarCoord
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

theorem polarPow (A B : ℕ) (p : ℝ × ℝ) :
    (Complex.polarCoord.symm p) ^ A * (starRingEnd ℂ (Complex.polarCoord.symm p)) ^ B
      = (p.1 : ℂ) ^ (A + B) * Complex.exp (((A : ℂ) - (B : ℂ)) * (p.2 : ℂ) * Complex.I) := by
  -- Write `Complex.polarCoord.symm p = p.1 * exp (p.2 * I)`.
  have hz : Complex.polarCoord.symm p
      = (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I) := by
    rw [Complex.polarCoord_symm_apply, ← Complex.exp_ofReal_mul_I]
  -- The complex conjugate of that is `p.1 * exp (-(p.2 * I))`, as `p.1` is real.
  have hstar : starRingEnd ℂ (Complex.polarCoord.symm p)
      = (p.1 : ℂ) * Complex.exp (-((p.2 : ℂ) * Complex.I)) := by
    rw [hz, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 1
    simp [map_mul]
  rw [hstar, hz, mul_pow, mul_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    mul_mul_mul_comm, ← pow_add, ← Complex.exp_add]
  congr 1
  congr 1
  ring

end Work.BoseB4
