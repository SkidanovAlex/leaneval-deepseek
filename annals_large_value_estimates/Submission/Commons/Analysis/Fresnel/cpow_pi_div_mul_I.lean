import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Fresnel

open Complex

set_option autoImplicit false

/-- Principal square root of `π / (l * I)` for `l > 0`: it is `√(π/l) · exp(-iπ/4)`. -/
theorem cpow_pi_div_mul_I (l : ℝ) (hl : 0 < l) :
    ((Real.pi : ℂ) / ((l : ℂ) * Complex.I)) ^ (1 / 2 : ℂ) / 2
      = ((Real.sqrt (Real.pi / l) / 2 : ℝ) : ℂ) * Complex.exp (-(Real.pi / 4) * Complex.I) := by
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hr : 0 < Real.pi / l := div_pos Real.pi_pos hl
  -- Express the base as `(π/l) * (-I)`.
  have hz : (Real.pi : ℂ) / ((l : ℂ) * Complex.I) = ((Real.pi / l : ℝ) : ℂ) * (-Complex.I) := by
    rw [ofReal_div]
    field_simp
    rw [Complex.I_sq]
    ring
  have hne : ((Real.pi / l : ℝ) : ℂ) * (-Complex.I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (ne_of_gt hr)) (neg_ne_zero.mpr hI)
  have hlog : Complex.log (((Real.pi / l : ℝ) : ℂ) * (-Complex.I))
      = ((Real.log (Real.pi / l) : ℝ) : ℂ) + (-(Real.pi / 2)) * Complex.I := by
    rw [Complex.log_ofReal_mul hr (neg_ne_zero.mpr hI), Complex.log_neg_I]
  have hexp : (((Real.log (Real.pi / l) : ℝ) : ℂ) + (-(Real.pi / 2)) * Complex.I) * (1 / 2 : ℂ)
      = ((Real.log (Real.pi / l) / 2 : ℝ) : ℂ) + (-(Real.pi / 4)) * Complex.I := by
    push_cast
    ring
  have hexp2 : Complex.exp (((Real.log (Real.pi / l) / 2 : ℝ) : ℂ))
      = ((Real.sqrt (Real.pi / l) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp,
      show Real.exp (Real.log (Real.pi / l) / 2) = Real.sqrt (Real.pi / l) from by
        rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr]
        ring_nf]
  have hpow : (((Real.pi / l : ℝ) : ℂ) * (-Complex.I)) ^ (1 / 2 : ℂ)
      = ((Real.sqrt (Real.pi / l) : ℝ) : ℂ) * Complex.exp (-(Real.pi / 4) * Complex.I) := by
    rw [Complex.cpow_def_of_ne_zero hne, hlog, hexp, Complex.exp_add, hexp2]
  rw [hz, hpow]
  push_cast
  ring

end Commons.Analysis.Fresnel