import Mathlib
import Submission.Work.BMF.tent_fourier_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- The `r`-th Fourier coefficient of the tent of width `B` (`r ≠ 0`) equals the
exponential expression `(2 - e(rB) - e(-rB)) / (4π² r² B)`.

Indeed `2 - e^{2πi rB} - e^{-2πi rB} = 2 - 2cos(2π rB) = 4 sin²(π rB)`, so the right-hand
side is `4 sin²(π rB) / (4π² r² B) = sin²(π rB)/(π² r² B)`, which is `tentCoeff B r`. -/
theorem tentCoeff_eq (B : ℝ) (hB : 0 < B) (r : ℤ) (hr : r ≠ 0) :
    (tentCoeff B r : ℂ) =
      (2 - eZ ((r : ℝ) * B) - eZ (-((r : ℝ) * B))) /
        ((4 * Real.pi ^ 2 * (r : ℝ) ^ 2 * B : ℝ) : ℂ) := by
  have hval : tentCoeff B r
      = Real.sin (Real.pi * (r : ℝ) * B) ^ 2 / (Real.pi ^ 2 * (r : ℝ) ^ 2 * B) := by
    simp [tentCoeff, hr]
  -- Euler's formula: `2 - eZ x - eZ (-x) = 4 sin²(π x)` for `x = r B`.
  have hnum : 2 - eZ ((r : ℝ) * B) - eZ (-((r : ℝ) * B))
      = ((4 * Real.sin (Real.pi * (r : ℝ) * B) ^ 2 : ℝ) : ℂ) := by
    have harg : 2 * Real.pi * Complex.I * (((r : ℝ) * B : ℝ) : ℂ)
        = (((2 * Real.pi * ((r : ℝ) * B) : ℝ)) : ℂ) * Complex.I := by push_cast; ring
    have harg' : 2 * Real.pi * Complex.I * ((-((r : ℝ) * B) : ℝ) : ℂ)
        = ((-(2 * Real.pi * ((r : ℝ) * B)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have h1 : eZ ((r : ℝ) * B)
        = ((Real.cos (2 * Real.pi * ((r : ℝ) * B)) : ℂ))
            + (Real.sin (2 * Real.pi * ((r : ℝ) * B)) : ℂ) * Complex.I := by
      unfold eZ
      rw [harg, Complex.exp_ofReal_mul_I]
    have h2 : eZ (-((r : ℝ) * B))
        = ((Real.cos (2 * Real.pi * ((r : ℝ) * B)) : ℂ))
            - (Real.sin (2 * Real.pi * ((r : ℝ) * B)) : ℂ) * Complex.I := by
      unfold eZ
      rw [harg', Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
      push_cast; ring
    rw [h1, h2]
    have hc : Real.cos (2 * Real.pi * ((r : ℝ) * B))
        = 1 - 2 * Real.sin (Real.pi * ((r : ℝ) * B)) ^ 2 := by
      rw [show 2 * Real.pi * ((r : ℝ) * B) = 2 * (Real.pi * ((r : ℝ) * B)) by ring,
        Real.cos_two_mul, Real.cos_sq']
      ring
    rw [hc]
    rw [show Real.pi * ((r : ℝ) * B) = Real.pi * (r : ℝ) * B by ring]
    push_cast; ring
  rw [hval, hnum]
  rw [← Complex.ofReal_div, Complex.ofReal_inj]
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  have hD : Real.pi ^ 2 * (r : ℝ) ^ 2 * B ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 Real.pi_ne_zero) (pow_ne_zero 2 hr'))
      (ne_of_gt hB)
  field_simp

end Work.BMF
