import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.norm_sinh_ofReal
import Submission.Commons.Analysis.SpecialFunctions.Trigonometric.norm_sin_le_exp_im

namespace Commons.Analysis.SpecialFunctions.Gamma

open Complex
open scoped Real

set_option autoImplicit false

/-- `sin (π * (I * τ)) = sinh (π * τ) * I`, as complex numbers. -/
private lemma sin_pi_mul_I_mul_ofReal (τ : ℝ) :
    Complex.sin ((Real.pi : ℂ) * (I * (τ : ℂ))) =
      (Real.sinh (Real.pi * τ) : ℂ) * I := by
  have h1 : (Real.pi : ℂ) * (I * (τ : ℂ)) = I * ((Real.pi * τ : ℝ) : ℂ) := by
    calc
      (Real.pi : ℂ) * (I * (τ : ℂ)) = I * ((Real.pi : ℂ) * (τ : ℂ)) := by ring
      _ = I * ((Real.pi * τ : ℝ) : ℂ) := by rw [← ofReal_mul]
  rw [h1]
  rw [show I * ((Real.pi * τ : ℝ) : ℂ) = ((Real.pi * τ : ℝ) : ℂ) * I by ring]
  rw [Complex.sin_mul_I]
  rw [ofReal_sinh]

/-- For real `τ ≠ 0`, `Γ(1 + iτ) * Γ(1 - iτ) = π * τ / sinh (π * τ)` as complex numbers. -/
private lemma gamma_one_add_mul_I_prod (τ : ℝ) (hτ : τ ≠ 0) :
    Complex.Gamma ((1 : ℂ) + I * (τ : ℂ)) *
        Complex.Gamma ((1 : ℂ) - I * (τ : ℂ)) =
      ((Real.pi * τ / Real.sinh (Real.pi * τ) : ℝ) : ℂ) := by
  let w : ℂ := I * (τ : ℂ)
  have hw_ne : w ≠ 0 := by
    dsimp [w]
    exact mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hτ)
  have hz1 : (1 : ℂ) + I * (τ : ℂ) = w + 1 := by
    dsimp [w]
    ring
  have hz2 : (1 : ℂ) - I * (τ : ℂ) = 1 - w := by
    dsimp [w]
  have hfeq : Complex.Gamma ((1 : ℂ) + I * (τ : ℂ)) = w * Complex.Gamma w := by
    rw [hz1, Complex.Gamma_add_one w hw_ne]
  have hnum : w * (Real.pi : ℂ) = I * ((Real.pi * τ : ℝ) : ℂ) := by
    calc
      w * (Real.pi : ℂ) = (I * (τ : ℂ)) * (Real.pi : ℂ) := by rfl
      _ = I * ((τ : ℂ) * (Real.pi : ℂ)) := by ring
      _ = I * ((Real.pi : ℂ) * (τ : ℂ)) := by ring
      _ = I * ((Real.pi * τ : ℝ) : ℂ) := by rw [← ofReal_mul]
  calc
    Complex.Gamma ((1 : ℂ) + I * (τ : ℂ)) * Complex.Gamma ((1 : ℂ) - I * (τ : ℂ))
        = (w * Complex.Gamma w) * Complex.Gamma (1 - w) := by rw [hfeq, hz2]
    _ = w * (Complex.Gamma w * Complex.Gamma (1 - w)) := by ring
    _ = w * ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w)) := by
        rw [Complex.Gamma_mul_Gamma_one_sub w]
    _ = w * ((Real.pi : ℂ) / ((Real.sinh (Real.pi * τ) : ℂ) * I)) := by
        congr 1
        rw [sin_pi_mul_I_mul_ofReal τ]
    _ = (w * (Real.pi : ℂ)) / ((Real.sinh (Real.pi * τ) : ℂ) * I) := by
        rw [mul_div_assoc]
    _ = (I * ((Real.pi * τ : ℝ) : ℂ)) / ((Real.sinh (Real.pi * τ) : ℂ) * I) := by
        rw [hnum]
    _ = ((Real.pi * τ / Real.sinh (Real.pi * τ) : ℝ) : ℂ) := by
        field_simp [I_ne_zero]
        rw [ofReal_div]

/-- `|π * τ / sinh (π * τ)| = π * |τ| / sinh (π * |τ|)` for real `τ`. -/
private lemma abs_pi_mul_div_sinh (τ : ℝ) :
    |Real.pi * τ / Real.sinh (Real.pi * τ)| =
      Real.pi * |τ| / Real.sinh (Real.pi * |τ|) := by
  have hnum : |Real.pi * τ| = Real.pi * |τ| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  have hden : |Real.sinh (Real.pi * τ)| = Real.sinh (Real.pi * |τ|) := by
    rw [Real.abs_sinh, hnum]
  rw [abs_div, hnum, hden]

/-- The product of the moduli of `Γ` at the conjugate points `1 ± iτ`:
`‖Γ(1+iτ)‖ * ‖Γ(1-iτ)‖ = π * |τ| / sinh (π * |τ|)` for real `τ ≠ 0`. -/
theorem gamma_one_add_mul_I_prod_norm (τ : ℝ) (hτ : τ ≠ 0) :
    ‖Complex.Gamma ((1 : ℂ) + Complex.I * (τ : ℂ))‖ *
        ‖Complex.Gamma ((1 : ℂ) - Complex.I * (τ : ℂ))‖ =
      Real.pi * |τ| / Real.sinh (Real.pi * |τ|) := by
  calc
    ‖Complex.Gamma ((1 : ℂ) + I * (τ : ℂ))‖ * ‖Complex.Gamma ((1 : ℂ) - I * (τ : ℂ))‖
        = ‖Complex.Gamma ((1 : ℂ) + I * (τ : ℂ)) * Complex.Gamma ((1 : ℂ) - I * (τ : ℂ))‖ := by
            rw [norm_mul]
    _ = ‖(((Real.pi * τ / Real.sinh (Real.pi * τ) : ℝ) : ℂ))‖ := by
            rw [gamma_one_add_mul_I_prod τ hτ]
    _ = |Real.pi * τ / Real.sinh (Real.pi * τ)| := by
            exact Complex.norm_real _
    _ = Real.pi * |τ| / Real.sinh (Real.pi * |τ|) := by
            exact abs_pi_mul_div_sinh τ

end Commons.Analysis.SpecialFunctions.Gamma