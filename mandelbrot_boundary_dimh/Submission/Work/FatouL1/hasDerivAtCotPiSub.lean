import Mathlib

namespace Work.FatouL1

theorem hasDerivAtCotPiSub {w z : ℂ} (hsin : Complex.sin (Real.pi * (w - z)) ≠ 0) :
    HasDerivAt (fun z : ℂ => Complex.cot (Real.pi * (w - z)))
      ((Real.pi : ℂ) / (Complex.sin (Real.pi * (w - z))) ^ 2) z := by
  have h1 : HasDerivAt (fun y : ℂ => w - y) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub w
  have hlin : HasDerivAt (fun y : ℂ => (Real.pi : ℂ) * (w - y)) ((Real.pi : ℂ) * (-1)) z :=
    h1.const_mul _
  simp only [mul_neg, mul_one] at hlin
  have hquot := (hlin.ccos).div (hlin.csin) hsin
  have hfun : ((fun x => Complex.cos (↑Real.pi * (w - x))) / fun x => Complex.sin (↑Real.pi * (w - x)))
      = (fun y : ℂ => Complex.cot (Real.pi * (w - y))) := by
    funext y; rw [Complex.cot]; rfl
  rw [hfun] at hquot
  have hval : (-Complex.sin (Real.pi * (w - z)) * (-(Real.pi : ℂ)) * Complex.sin (Real.pi * (w - z))
        - Complex.cos (Real.pi * (w - z)) * (Complex.cos (Real.pi * (w - z)) * (-(Real.pi : ℂ))))
        / Complex.sin (Real.pi * (w - z)) ^ 2
      = (Real.pi : ℂ) / Complex.sin (Real.pi * (w - z)) ^ 2 := by
    have hnum : (-Complex.sin (Real.pi * (w - z)) * (-(Real.pi : ℂ)) * Complex.sin (Real.pi * (w - z))
        - Complex.cos (Real.pi * (w - z)) * (Complex.cos (Real.pi * (w - z)) * (-(Real.pi : ℂ))))
        = (Real.pi : ℂ) := by
      rw [show (-Complex.sin (Real.pi * (w - z)) * (-(Real.pi : ℂ)) * Complex.sin (Real.pi * (w - z))
          - Complex.cos (Real.pi * (w - z)) * (Complex.cos (Real.pi * (w - z)) * (-(Real.pi : ℂ))))
          = (Real.pi : ℂ) * (Complex.sin (Real.pi * (w - z)) ^ 2 + Complex.cos (Real.pi * (w - z)) ^ 2) by ring]
      rw [Complex.sin_sq_add_cos_sq, mul_one]
    rw [hnum]
  rwa [hval] at hquot

end Work.FatouL1
