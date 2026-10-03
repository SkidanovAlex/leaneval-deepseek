import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.norm_Gamma_lower_strip
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay
import Submission.Commons.Analysis.SpecialFunctions.Gamma.norm_gammaR_le_norm_gammaR_re

open Complex
open scoped Real

set_option autoImplicit false

namespace Commons.Analysis.SpecialFunctions.Gamma

/-- Modulus of Deligne's real Gamma factor at `a + i·t`, expanded in terms of `Γ` at
half the argument:
`‖Gammaℝ (a + i t)‖ = π^(-a/2) · ‖Γ (a/2 + i·t/2)‖`. -/
lemma norm_gammaR_vertical_eq (a t : ℝ) :
    ‖Complex.Gammaℝ ((a : ℂ) + I * (t : ℂ))‖ =
      (Real.pi : ℝ) ^ (-(a / 2)) *
        ‖Complex.Gamma (((a / 2 : ℝ) : ℂ) + I * ((t / 2 : ℝ) : ℂ))‖ := by
  have hsre : (((a : ℂ) + I * (t : ℂ))).re = a := by simp
  have hpi : ‖(Real.pi : ℂ) ^ (-((a : ℂ) + I * (t : ℂ)) / 2)‖ =
      (Real.pi : ℝ) ^ (-(a / 2)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    rw [re_of_half]
    simp
    ring
  have hs2 : (((a : ℂ) + I * (t : ℂ)) / 2) =
      (((a / 2 : ℝ) : ℂ) + I * ((t / 2 : ℝ) : ℂ)) := by
    apply Complex.ext <;> simp
  rw [Complex.Gammaℝ_def, norm_mul, hpi]
  exact congrArg (fun w : ℝ => (Real.pi : ℝ) ^ (-(a / 2)) * w) (by rw [hs2])

/-- Since the exponent `a/2 - 1` is negative (for `a < 2`), the power is antitone in the
base, giving `(1 + |t|)^(a/2-1) ≤ (1 + |t|/2)^(a/2-1)`. -/
lemma pow_half_ge (a t : ℝ) (ha2 : a < 2) :
    (1 + |t|) ^ (a / 2 - 1) ≤ (1 + |t| / 2) ^ (a / 2 - 1) := by
  have hP0 : 0 ≤ 1 + |t| := by positivity
  have hQ0 : 0 ≤ 1 + |t| / 2 := by positivity
  have hPpos : 0 < 1 + |t| := by positivity
  have hQpos : 0 < 1 + |t| / 2 := by positivity
  have hPQ : 1 + |t| / 2 ≤ 1 + |t| := by
    have ht0 : 0 ≤ |t| := abs_nonneg t
    nlinarith
  have hr : 0 < 1 - a / 2 := by nlinarith
  rw [show a / 2 - 1 = -(1 - a / 2) by ring]
  rw [Real.rpow_neg hP0, Real.rpow_neg hQ0]
  rw [inv_le_inv₀ (Real.rpow_pos_of_pos hPpos (1 - a / 2))
    (Real.rpow_pos_of_pos hQpos (1 - a / 2))]
  exact Real.rpow_le_rpow hQ0 hPQ (le_of_lt hr)

end Commons.Analysis.SpecialFunctions.Gamma
