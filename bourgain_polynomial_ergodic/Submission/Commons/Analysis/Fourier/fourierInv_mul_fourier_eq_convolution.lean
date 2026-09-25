import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

theorem fourierInv_mul_fourier_eq_convolution {m f : ℝ → ℂ} (hm : MeasureTheory.Integrable m) (hf : MeasureTheory.Integrable f)
    (x : ℝ) :
    FourierTransformInv.fourierInv (fun ξ => m ξ * FourierTransform.fourier f ξ) x
      = ∫ y : ℝ, f y * FourierTransformInv.fourierInv m (x - y) := by
  let F : ℝ → ℝ → ℂ := fun ξ y =>
    Complex.exp ((↑(2 * Real.pi * (ξ * x)) : ℂ) * Complex.I) *
      (m ξ * (Complex.exp ((↑(-2 * Real.pi * (y * ξ)) : ℂ) * Complex.I) * f y))
  have hdom : Integrable (fun p : ℝ × ℝ => ‖m p.1‖ * ‖f p.2‖) (volume.prod volume) :=
    Integrable.mul_prod hm.norm hf.norm
  have hFae : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) := by
    have hfe : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.2) (volume.prod volume) :=
      hf.aestronglyMeasurable.comp_snd
    have hme : AEStronglyMeasurable (fun p : ℝ × ℝ => m p.1) (volume.prod volume) :=
      hm.aestronglyMeasurable.comp_fst
    have he1 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Complex.exp ((↑(2 * Real.pi * (p.1 * x)) : ℂ) * Complex.I))
        (volume.prod volume) :=
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    have he2 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Complex.exp ((↑(-2 * Real.pi * (p.2 * p.1)) : ℂ) * Complex.I))
        (volume.prod volume) :=
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    show AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Complex.exp ((↑(2 * Real.pi * (p.1 * x)) : ℂ) * Complex.I) *
        (m p.1 *
          (Complex.exp ((↑(-2 * Real.pi * (p.2 * p.1)) : ℂ) * Complex.I) * f p.2)))
      (volume.prod volume)
    exact he1.mul (hme.mul (he2.mul hfe))
  have hFint : Integrable (Function.uncurry F) (volume.prod volume) := by
    refine hdom.mono' hFae ?_
    filter_upwards with p
    show ‖Complex.exp ((↑(2 * Real.pi * (p.1 * x)) : ℂ) * Complex.I) *
        (m p.1 *
          (Complex.exp ((↑(-2 * Real.pi * (p.2 * p.1)) : ℂ) * Complex.I) * f p.2))‖
      ≤ ‖m p.1‖ * ‖f p.2‖
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I,
      Complex.norm_exp_ofReal_mul_I, one_mul, one_mul]
  have h1 : FourierTransformInv.fourierInv
        (fun ξ => m ξ * FourierTransform.fourier f ξ) x
      = ∫ ξ, ∫ y, F ξ y := by
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with ξ
    rw [Real.fourier_eq']
    simp only [Real.inner_apply, smul_eq_mul]
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  have h2 : (∫ ξ, ∫ y, F ξ y) = ∫ y, ∫ ξ, F ξ y := integral_integral_swap hFint
  have h3 : (∫ y, ∫ ξ, F ξ y) = ∫ y, f y * FourierTransformInv.fourierInv m (x - y) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [Real.fourierInv_eq']
    simp only [Real.inner_apply, smul_eq_mul]
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ξ
    simp only [F]
    have hphase : Complex.exp ((↑(2 * Real.pi * (ξ * x)) : ℂ) * Complex.I) *
          Complex.exp ((↑(-2 * Real.pi * (y * ξ)) : ℂ) * Complex.I)
        = Complex.exp ((↑(2 * Real.pi * (ξ * (x - y))) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← hphase]
    ring
  rw [h1, h2, h3]

end Commons.Analysis.Fourier