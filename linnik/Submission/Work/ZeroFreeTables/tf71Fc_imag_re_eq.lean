/-
# ZeroFreeTables — `tf71Fc_imag_re_eq`

The Laplace transform `tf71Fc` of HB Lemma 7.1's test function `tf71f`, evaluated on the
imaginary axis at `z = iy`, has real part the cosine transform of `f`:

  `Re F(iy) = ∫₀^{2γ} cos(y t) f(t) dt`.

Indeed `F(z) = ∫₀^{2γ} e^{−zt} f(t) dt`, so for `z = iy` the integrand is
`e^{−iyt} f(t) = (cos(yt) − i sin(yt)) f(t)`; taking real parts of an interval integral
(`intervalIntegral_re`, the integrand being continuous) and comparing pointwise gives the
claim.  On `[0, 2γ]` the piecewise function `tf71f` agrees with the trigonometric closed
form `tf71cf`, which is what makes the integrand continuous.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.testFn71_defs
import Submission.Work.ZeroFreeTables.tf71Fc_model

noncomputable section
open scoped Real
namespace Work.ZeroFreeTables

/-- Pointwise form of the claim: on `[0, 2γ]` the real part of the integrand of `tf71Fc`
at `z = iy` is `cos (y t) * tf71cf θ lam t`. -/
lemma tf71Fc_integrand_re (θ lam y t : ℝ) :
    (Complex.exp (-(((y : ℂ) * Complex.I) * (t : ℂ))) * tf71cfC θ lam t).re
      = Real.cos (y * t) * tf71cf θ lam t := by
  have h1 : -(((y : ℂ) * Complex.I) * (t : ℂ)) = ((-(y * t) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  simp only [tf71cfC]
  rw [h1, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.ofReal_re, Complex.ofReal_im, Real.cos_neg, mul_zero, sub_zero]

theorem tf71Fc_imag_re_eq (θ lam : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam)
    (y : ℝ) :
    (Work.ZeroFreeTables.tf71Fc θ lam ((y : ℂ) * Complex.I)).re
      = ∫ t in (0:ℝ)..(2 * Work.ZeroFreeTables.tf71γ θ lam),
          Real.cos (y * t) * Work.ZeroFreeTables.tf71f θ lam t := by
  have hγ2 : (0:ℝ) ≤ 2 * tf71γ θ lam := tf71_twoγ_nonneg hθ0 hθ1 hlam
  -- identify `tf71Fc` with the Laplace transform of the continuous closed form
  rw [tf71Fc_eq_integral_cf hθ0 hθ1 hlam]
  have hcont : Continuous
      (fun t : ℝ => Complex.exp (-(((y : ℂ) * Complex.I) * (t : ℂ))) * tf71cfC θ lam t) :=
    (Complex.continuous_exp.comp (by fun_prop)).mul (tf71cfC_cont θ lam)
  have hint : IntervalIntegrable
      (fun t : ℝ => Complex.exp (-(((y : ℂ) * Complex.I) * (t : ℂ))) * tf71cfC θ lam t)
      MeasureTheory.volume (0:ℝ) (2 * tf71γ θ lam) := hcont.intervalIntegrable _ _
  -- real part of an interval integral of a continuous ℂ-valued function
  have hre : (∫ t in (0:ℝ)..(2 * tf71γ θ lam),
        Complex.exp (-(((y : ℂ) * Complex.I) * (t : ℂ))) * tf71cfC θ lam t).re
      = ∫ t in (0:ℝ)..(2 * tf71γ θ lam),
        (Complex.exp (-(((y : ℂ) * Complex.I) * (t : ℂ))) * tf71cfC θ lam t).re := by
    simpa only [Complex.reCLM_apply] using
      (Complex.reCLM.intervalIntegral_comp_comm hint).symm
  rw [hre]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hγ2] at ht
  simp only [tf71Fc_integrand_re, tf71f_eq_cf θ lam t ht]

end Work.ZeroFreeTables
