import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay
import Submission.Work.LinnikAreas.Density4.gamma_vertical_integrable_of_bound

open Complex MeasureTheory Set
open scoped FourierTransform

namespace Work.LinnikAreas.Density4

/-- Mellin inversion for the exponential kernel: for `c > 0` and `y > 0`,
`(1/(2π)) ∫_ℝ y^{-(c+it)} Γ(c+it) dt = e^{-y}`.

This is the inverse Mellin transform of `Γ` at the parameter `c`, i.e. the statement
that the Mellin transform of `x ↦ e^{-x}` is `Γ` (`Complex.GammaIntegral_eq_mellin`),
inverted by `mellinInv_mellin_eq` on the vertical line `Re s = c`. -/
theorem mellin_kernel_exp (c : ℝ) (hc : 0 < c) (y : ℝ) (hy : 0 < y) :
    (1 / (2 * Real.pi)) * ∫ t : ℝ,
        (y : ℂ) ^ (-(c + (t : ℂ) * Complex.I)) * Complex.Gamma (c + (t : ℂ) * Complex.I)
      = ((Real.exp (-y) : ℝ) : ℂ) := by
  classical
  -- The Mellin transform of `x ↦ e^{-x}` agrees with `Γ` on the vertical line `Re s = c`.
  have hmellin : ∀ t : ℝ, mellin (fun x : ℝ => (Real.exp (-x) : ℂ)) (c + (t:ℂ)*Complex.I)
      = Complex.Gamma (c + (t:ℂ)*Complex.I) := fun t => by
    rw [Complex.Gamma_eq_integral (s := c + (t:ℂ)*Complex.I) (by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
      exact hc)]
    rw [Complex.GammaIntegral_eq_mellin]
  -- Convergence of the Mellin integral of `x ↦ e^{-x}` at `s = c`.
  have hmc : MellinConvergent (fun x : ℝ => (Real.exp (-x) : ℂ)) (c:ℂ) := by
    rw [MellinConvergent]
    have h := Complex.GammaIntegral_convergent (s := (c:ℂ)) (by simpa using hc)
    refine (MeasureTheory.integrableOn_congr_fun ?_ measurableSet_Ioi).mp h
    intro t ht
    simp only [smul_eq_mul]
    rw [Complex.ofReal_exp]; ring
  -- Integrability of `Γ` along the vertical line `Re s = c`.
  have hvi : Complex.VerticalIntegrable (mellin (fun x : ℝ => (Real.exp (-x) : ℂ))) c := by
    obtain ⟨C, hCpos, hCbd⟩ :=
      Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay c hc
    rw [Complex.VerticalIntegrable]
    have hInt : MeasureTheory.Integrable (fun y : ℝ => Complex.Gamma (c + (y:ℂ)*Complex.I)) :=
      gamma_vertical_integrable_of_bound c C hCpos (fun t => by
        rw [show c + (t:ℂ)*Complex.I = (c:ℂ) + Complex.I*(t:ℂ) by ring]
        exact hCbd t)
    refine hInt.congr ?_
    filter_upwards with y
    rw [Complex.Gamma_eq_integral (s := c + (y:ℂ)*Complex.I) (by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
      exact hc)]
    rw [Complex.GammaIntegral_eq_mellin]
  -- Continuity of `x ↦ e^{-x}` at `y`.
  have hcont : ContinuousAt (fun x : ℝ => (Real.exp (-x) : ℂ)) y := by fun_prop
  -- Apply the Mellin inversion formula.
  have hmain := mellinInv_mellin_eq c (fun x : ℝ => (Real.exp (-x) : ℂ)) hy hmc hvi hcont
  rw [mellinInv] at hmain
  -- Replace `mellin (e^{-·})` by `Γ` on the integration line, and unfold the scalar.
  have hcongr : (fun t : ℝ => (y:ℂ)^(-((c:ℂ) + (t:ℂ)*Complex.I)) •
        mellin (fun x : ℝ => (Real.exp (-x) : ℂ)) ((c:ℂ) + (t:ℂ)*Complex.I))
      = fun t : ℝ => (y:ℂ)^(-(c + (t:ℂ)*Complex.I)) *
          Complex.Gamma (c + (t:ℂ)*Complex.I) := by
    funext t
    rw [hmellin t, smul_eq_mul]
  rw [hcongr] at hmain
  rw [Complex.real_smul] at hmain
  simpa using hmain

end Work.LinnikAreas.Density4
