/-
# The crude bound for the Fourier coefficients of a continuous symbol

For a continuous `τ : ℝ → ℝ → ℂ` the `(p₁,p₂)`-th Fourier coefficient
`coeff2 τ p₁ p₂ = ∫₀¹ ∫₀¹ τ(x,y) e(-p₁x - p₂y) dx dy` (see `SymToolbox`) is bounded in
modulus by the `L¹`-norm of `τ` over `[0,1]²`:

  `‖coeff2 τ p₁ p₂‖ ≤ ∫₀¹∫₀¹ ‖τ(x,y)‖ dx dy`.

This is the `j₁ = j₂ = 0` case of the paper's crude multiplier bound: it is the elementary
estimate that needs no derivatives at all.  It is stated in `ENNReal`/`lintegral` form, ready to
be combined with the derivative bounds `∫⁻∫⁻ ‖dp j₁ j₂ τ‖` used by `SymToolbox_tsum_coeff2_le`.

The proof is a two-fold application of `‖∫ f‖ₑ ≤ ∫⁻ ‖f‖ₑ` (`enorm_integral_le_lintegral_enorm`,
which needs no integrability hypothesis), together with `‖e(z)‖ = 1` for real `z` and the fact
that the interval `(0,1]` differs from `[0,1]` by a null set.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.SymToolbox

set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

open MeasureTheory intervalIntegral
open scoped ENNReal

theorem coeff2_ofReal_norm_le_lintegral (τ : ℝ → ℝ → ℂ)
    (hcont : Continuous (fun p : ℝ × ℝ => τ p.1 p.2)) (p₁ p₂ : ℤ) :
    ENNReal.ofReal ‖Work.KMTPlan.A6.coeff2 τ p₁ p₂‖
      ≤ ∫⁻ x in Set.Icc (0 : ℝ) 1, ∫⁻ y in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ‖τ x y‖ := by
  -- the character `e(z) = exp (2πiz)` has modulus `1` for real `z`
  have hnorm_eeC : ∀ z : ℝ, ‖eeC z‖ = 1 := by
    intro z
    rw [eeC]
    have hz : (2 * (Real.pi : ℂ) * Complex.I * (z : ℂ))
        = (((2 * Real.pi * z : ℝ)) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hz, Complex.norm_exp_ofReal_mul_I]
  have hnorm_eeC' : ∀ z : ℝ, ‖eeC z‖ₑ = 1 := by
    intro z
    rw [show ‖eeC z‖ₑ = ENNReal.ofReal ‖eeC z‖ from by simp [enorm_eq_nnnorm], hnorm_eeC z]
    simp
  -- one-dimensional bound: the norm of the inner interval integral
  have hstep : ∀ a : ℝ,
      ‖∫ y in (0 : ℝ)..1, τ a y * eeC (-(p₁ : ℝ) * a - (p₂ : ℝ) * y)‖ₑ
        ≤ ∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ‖τ a y‖ := by
    intro a
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    exact lintegral_congr (fun y => by
      rw [enorm_mul, hnorm_eeC', mul_one,
        show ‖τ a y‖ₑ = ENNReal.ofReal ‖τ a y‖ from by simp [enorm_eq_nnnorm]])
  rw [show ENNReal.ofReal ‖coeff2 τ p₁ p₂‖ = ‖coeff2 τ p₁ p₂‖ₑ from by
      simp [enorm_eq_nnnorm]]
  rw [coeff2]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  calc ‖∫ a in Set.Ioc (0 : ℝ) 1,
          (∫ y in (0 : ℝ)..1, τ a y * eeC (-(p₁ : ℝ) * a - (p₂ : ℝ) * y))‖ₑ
      ≤ ∫⁻ a in Set.Ioc (0 : ℝ) 1, (∫⁻ y in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ‖τ a y‖) := by
        refine (enorm_integral_le_lintegral_enorm _).trans ?_
        exact lintegral_mono hstep
    _ ≤ ∫⁻ a in Set.Ioc (0 : ℝ) 1, (∫⁻ y in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ‖τ a y‖) :=
        lintegral_mono (fun a => lintegral_mono_set Set.Ioc_subset_Icc_self)
    _ ≤ ∫⁻ a in Set.Icc (0 : ℝ) 1, (∫⁻ y in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ‖τ a y‖) :=
        lintegral_mono_set Set.Ioc_subset_Icc_self

end Work.KMTPlan.A6
