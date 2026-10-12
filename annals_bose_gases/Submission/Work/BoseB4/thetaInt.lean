import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

theorem thetaInt (k : ℤ) :
    ∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi,
        Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I) =
      if k = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  have key : (∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi,
        Complex.exp ((k : ℂ) * (θ : ℂ) * Complex.I))
      = ∫ θ in (-Real.pi)..Real.pi,
          Complex.exp (((k : ℂ) * Complex.I) * (θ : ℂ)) := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (neg_le_self (le_of_lt Real.pi_pos))]
    apply intervalIntegral.integral_congr
    intro θ _
    ring_nf
  rw [key]
  by_cases hk : k = 0
  · subst hk
    simp
    ring
  · rw [if_neg hk]
    have hc : ((k : ℂ) * Complex.I) ≠ 0 := by simp [hk]
    rw [integral_exp_mul_complex hc]
    have h2 : Complex.exp (2 * (Real.pi : ℂ) * ((k : ℂ) * Complex.I)) = 1 := by
      have heq : 2 * (Real.pi : ℂ) * ((k : ℂ) * Complex.I)
          = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
      rw [heq, Complex.exp_int_mul_two_pi_mul_I]
    have h3 : Complex.exp (((k : ℂ) * Complex.I) * (Real.pi : ℂ))
        = Complex.exp (((k : ℂ) * Complex.I) * (-(Real.pi : ℂ))) := by
      have : Complex.exp (((k : ℂ) * Complex.I) * (Real.pi : ℂ))
          = Complex.exp (((k : ℂ) * Complex.I) * (-(Real.pi : ℂ)))
            * Complex.exp (2 * (Real.pi : ℂ) * ((k : ℂ) * Complex.I)) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      rw [this, h2, mul_one]
    simp only [Complex.ofReal_neg]
    rw [h3, sub_self, zero_div]

end Work.BoseB4
