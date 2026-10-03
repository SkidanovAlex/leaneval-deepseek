import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

namespace Commons.Analysis.Fourier

open MeasureTheory

/-- For an integrable `F : ℝ → ℂ`, the integral over all of `ℝ` equals the integral over `(0,∞)`
of `F(-x) + F x`. -/
lemma integral_eq_integral_Ioi_add_comp_neg (F : ℝ → ℂ) (hF : Integrable F) :
    ∫ x, F x = ∫ x in Set.Ioi (0 : ℝ), (F (-x) + F x) := by
  have hcompl : (∫ x in Set.Iic (0 : ℝ), F x) + ∫ x in (Set.Iic (0 : ℝ))ᶜ, F x = ∫ x, F x :=
    integral_add_compl measurableSet_Iic hF
  rw [Set.compl_Iic] at hcompl
  have hneg : (∫ x in Set.Iic (0 : ℝ), F x) = ∫ x in Set.Ioi (0 : ℝ), F (-x) := by
    have h := integral_comp_neg_Ioi (c := (0 : ℝ)) F
    rw [neg_zero] at h
    exact h.symm
  have hFneg : Integrable fun x : ℝ => F (-x) := hF.comp_neg
  have hadd : (∫ x in Set.Ioi (0 : ℝ), F (-x)) + ∫ x in Set.Ioi (0 : ℝ), F x
      = ∫ x in Set.Ioi (0 : ℝ), (F (-x) + F x) :=
    (integral_add hFneg.integrableOn hF.integrableOn).symm
  rw [← hcompl, hneg, hadd]

/- The Fourier transform of an even, continuous, compactly supported real function is the cosine
transform: `𝓕 h ξ = 2 * ∫_0^∞ h t cos(2πξt) dt`. -/
open scoped FourierTransform in
theorem fourier_even_eq (h : ℝ → ℝ) (hc : Continuous h) (hcs : HasCompactSupport h)
    (heven : ∀ x, h (-x) = h x) (ξ : ℝ) :
    (𝓕 fun t : ℝ => (h t : ℂ)) ξ
      = ((2 * ∫ t in Set.Ici (0 : ℝ), h t * Real.cos (2 * Real.pi * ξ * t) : ℝ) : ℂ) := by
  set g : ℝ → ℂ := fun t => (h t : ℂ) with hgdef
  set F : ℝ → ℂ := fun v => Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) * g v with hFdef
  have hgcs : HasCompactSupport g := by
    rw [hgdef]
    exact hcs.comp_left (g := Complex.ofReal) (by simp)
  have hcF : Continuous F := by
    rw [hFdef]
    exact Continuous.mul (by fun_prop) (Complex.continuous_ofReal.comp hc)
  have hcsF : HasCompactSupport F := by
    rw [hFdef]
    exact hgcs.mul_left
  have hFi : Integrable F := hcF.integrable_of_hasCompactSupport hcsF
  have hfour : (𝓕 g) ξ = ∫ v : ℝ, F v := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp only [hFdef, smul_eq_mul]
  rw [hfour, integral_eq_integral_Ioi_add_comp_neg F hFi]
  have hpt : ∀ x : ℝ, F (-x) + F x = ((2 * (h x * Real.cos (2 * Real.pi * ξ * x)) : ℝ) : ℂ) := by
    intro x
    have hgn : g (-x) = g x := by
      change ((h (-x) : ℝ) : ℂ) = ((h x : ℝ) : ℂ)
      rw [heven x]
    have hexp : Complex.exp (↑(-2 * Real.pi * (-x) * ξ) * Complex.I)
        + Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I)
        = 2 * ((Real.cos (2 * Real.pi * ξ * x) : ℝ) : ℂ) := by
      have h1 : (-2 * Real.pi * (-x) * ξ) = 2 * Real.pi * ξ * x := by ring
      have h2 : (-2 * Real.pi * x * ξ) = -(2 * Real.pi * ξ * x) := by ring
      rw [h1, h2, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
      simp only [Complex.ofReal_neg]
      ring
    rw [hFdef]
    simp only [hgn]
    rw [← add_mul, hexp]
    rw [hgdef]
    push_cast
    ring
  rw [show (∫ x in Set.Ioi (0 : ℝ), (F (-x) + F x))
      = ∫ x in Set.Ioi (0 : ℝ), ((2 * (h x * Real.cos (2 * Real.pi * ξ * x)) : ℝ) : ℂ) from
      setIntegral_congr_fun measurableSet_Ioi (fun x _ => hpt x)]
  have hkey : (∫ x in Set.Ioi (0 : ℝ), 2 * (h x * Real.cos (2 * Real.pi * ξ * x)))
      = 2 * ∫ t in Set.Ici (0 : ℝ), h t * Real.cos (2 * Real.pi * ξ * t) := by
    rw [integral_const_mul, setIntegral_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))]
  trans ((∫ x in Set.Ioi (0 : ℝ), 2 * (h x * Real.cos (2 * Real.pi * ξ * x)) : ℝ) : ℂ)
  · exact integral_ofReal
  · rw [hkey]

open scoped FourierTransform in
theorem fourier_quadratic_eq (f : ℝ → ℝ) (b ξ : ℝ) (hf : Continuous f)
    (hcs : HasCompactSupport fun t : ℝ => f (t ^ 2 + b ^ 2)) :
    (𝓕 fun t : ℝ => ((f (t ^ 2 + b ^ 2) : ℝ) : ℂ)) ξ
      = ((2 * ∫ t in Set.Ici (0 : ℝ), f (t ^ 2 + b ^ 2) * Real.cos (2 * Real.pi * ξ * t) : ℝ) : ℂ) := by
  refine fourier_even_eq (fun t : ℝ => f (t ^ 2 + b ^ 2)) ?_ hcs ?_ ξ
  · exact hf.comp (by fun_prop)
  · intro x
    congr 1
    ring

end Commons.Analysis.Fourier