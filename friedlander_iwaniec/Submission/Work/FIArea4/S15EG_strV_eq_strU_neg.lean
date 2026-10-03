import Mathlib
import Submission.Work.FIArea4.S15stratumDefs

namespace Work.FIArea4

/-- `S15zfV u t ℓ w = S15zf u (-t) ℓ w`, since the only `t`-dependence is the exponent
`I * t` versus `-(I * t) = I * (-t)`. -/
theorem S15zfV_eq_S15zf_neg (u t : ℝ) (ℓ : ℤ) (z : GaussianInt) :
    S15zfV u t ℓ z = S15zf u (-t) ℓ z := by
  simp only [S15zfV, S15zf]
  have h : Complex.I * ((-t : ℝ) : ℂ) = -(Complex.I * (t : ℂ)) := by push_cast; ring
  rw [h]

theorem S15EG_strV_eq_strU_neg (β : GaussianInt → ℂ) (u t : ℝ) (ℓ : ℤ) (e : ℕ) :
    Work.FIArea4.S15strV β u t ℓ e = Work.FIArea4.S15strU β u (-t) ℓ e := by
  funext z
  simp only [S15strV, S15strU, S15zfV_eq_S15zf_neg]

end Work.FIArea4
