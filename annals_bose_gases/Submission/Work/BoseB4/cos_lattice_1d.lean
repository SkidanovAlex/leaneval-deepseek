import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

open MeasureTheory

theorem cos_lattice_1d (m : ℤ) :
    ∫ t in Set.Icc (-(1/2) : ℝ) (1/2),
        Complex.exp (Complex.I * ((2 * Real.pi * (m : ℝ)) * t))
      = (if m = 0 then (1 : ℂ) else 0) := by
  -- Write the phase as `c * t` with `c = 2 * pi * m * I`.
  set c : ℂ := Complex.I * ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) with hc
  have hstep : (∫ t in Set.Icc (-(1/2) : ℝ) (1/2),
        Complex.exp (Complex.I * ((2 * Real.pi * (m : ℝ)) * t)))
      = ∫ t in (-(1/2) : ℝ)..(1/2), Complex.exp (c * (t : ℂ)) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (by norm_num : (-(1/2) : ℝ) ≤ 1/2)]
    apply intervalIntegral.integral_congr
    intro t _
    rw [hc]
    push_cast
    ring_nf
  rw [hstep]
  by_cases hm : m = 0
  · -- vanishing frequency: the integrand is identically `1`
    subst hm
    rw [if_pos rfl, hc]
    simp
    norm_num
  · rw [if_neg hm]
    have hc0 : c ≠ 0 := by
      rw [hc]
      refine mul_ne_zero Complex.I_ne_zero ?_
      rw [Complex.ofReal_ne_zero]
      exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)
        (by exact_mod_cast hm)
    rw [integral_exp_mul_complex hc0]
    -- the two boundary exponentials agree because the arguments differ by `2 * pi * m * I`
    have hexp : Complex.exp (c * (1/2 : ℝ)) = Complex.exp (c * (-(1/2) : ℝ)) := by
      have hd : c * (1/2 : ℝ) - c * (-(1/2) : ℝ)
          = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        rw [hc]; push_cast; ring
      have : c * (1/2 : ℝ)
          = c * (-(1/2) : ℝ) + (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        rw [← hd]; ring
      rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hexp, sub_self, zero_div]

end Work.BoseB4
