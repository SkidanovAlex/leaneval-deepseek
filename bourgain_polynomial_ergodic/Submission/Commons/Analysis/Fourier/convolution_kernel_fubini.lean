import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

/-- Change-of-variables identity relating the oscillatory integral defining the kernel to an
integral against `M` at the rescaled argument.  This is the substitution `θ = -2πξ`. -/
private lemma conv_kernel_change_of_variables (M : ℝ → ℂ) (t : ℝ) :
    (∫ θ : ℝ, M θ * Complex.exp (-(Complex.I * (t : ℂ) * (θ : ℂ))))
      = 2 * Real.pi *
        ∫ ξ : ℝ, Complex.exp ((↑(2 * Real.pi * ξ * t) : ℂ) * Complex.I) *
          M (-(2 * Real.pi) * ξ) := by
  have hne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have h := Measure.integral_comp_mul_left
    (fun ξ : ℝ => Complex.exp ((↑(2 * Real.pi * ξ * t) : ℂ) * Complex.I) *
      M (-(2 * Real.pi) * ξ))
    (-(1/(2 * Real.pi)))
  rw [show (-(1/(2*Real.pi)) : ℝ)⁻¹ = -(2*Real.pi) by field_simp] at h
  rw [abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi), Complex.real_smul] at h
  rw [show (↑(2*Real.pi) : ℂ) = 2 * (↑Real.pi : ℂ) by push_cast; ring] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards with θ
  have h1 : (2 * Real.pi * ((-(1/(2*Real.pi))) * θ) * t : ℝ) = -(θ * t) := by field_simp
  have h2 : (-(2 * Real.pi) * ((-(1/(2*Real.pi))) * θ) : ℝ) = θ := by field_simp
  rw [h1, h2, mul_comm (Complex.exp _) (M θ)]
  congr 1
  congr 1
  push_cast
  ring

/-- **Fubini identity for a smooth-window kernel on `ℝ`.**  Let `M : ℝ → ℂ` be measurable with
`M ∈ L¹ ∩ L² ∩ L^∞` and let `f ∈ L¹ ∩ L²`.  Then for every `x : ℝ`,
`∫ y, f y * (∫ θ, M θ * exp (-(I * (x - y) * θ))) = 2π · 𝓕⁻ (ξ ↦ M (-2π ξ) · 𝓕 f ξ) x`
(Mathlib Fourier convention). -/
theorem convolution_kernel_fubini (M : ℝ → ℂ) (f : ℝ → ℂ)
    (hMmeas : Measurable M) (hM1 : MemLp M 1 (volume : Measure ℝ))
    (hM2 : MemLp M 2 (volume : Measure ℝ)) (hMtop : MemLp M ⊤ (volume : Measure ℝ))
    (hf1 : MemLp f 1 (volume : Measure ℝ)) (hf2 : MemLp f 2 (volume : Measure ℝ)) (x : ℝ) :
    (∫ y, f y * (∫ θ, M θ * Complex.exp (-(Complex.I * ((x - y : ℝ)) * (θ : ℝ)))))
      = 2 * Real.pi *
        FourierTransformInv.fourierInv (fun ξ => M (-(2 * Real.pi) * ξ) * FourierTransform.fourier f ξ) x := by
  let F : ℝ → ℝ → ℂ := fun v y =>
    Complex.exp ((↑(2*Real.pi*(v*x)) : ℂ) * Complex.I) *
      (M (-(2*Real.pi)*v) * (Complex.exp ((↑(-2*Real.pi*(y*v)) : ℂ) * Complex.I) * f y))
  have hne : (-(2*Real.pi) : ℝ) ≠ 0 := neg_ne_zero.mpr (by positivity)
  have hdom_int : Integrable (fun p : ℝ × ℝ => ‖M (-(2*Real.pi)*p.1)‖ * ‖f p.2‖)
      (volume.prod volume) :=
    Integrable.mul_prod (((memLp_one_iff_integrable.mp hM1).norm).comp_mul_left' hne)
      ((memLp_one_iff_integrable.mp hf1).norm)
  have hFae : AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) := by
    have hfe : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.2) (volume.prod volume) :=
      hf1.aestronglyMeasurable.comp_snd
    have hMe : AEStronglyMeasurable (fun p : ℝ × ℝ => M (-(2*Real.pi)*p.1))
        (volume.prod volume) :=
      (hMmeas.comp (by fun_prop)).aestronglyMeasurable
    have he1 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Complex.exp ((↑(2*Real.pi*(p.1*x)) : ℂ) * Complex.I))
        (volume.prod volume) :=
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    have he2 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Complex.exp ((↑(-2*Real.pi*(p.2*p.1)) : ℂ) * Complex.I))
        (volume.prod volume) :=
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    show AEStronglyMeasurable (fun p : ℝ × ℝ =>
      Complex.exp ((↑(2*Real.pi*(p.1*x)) : ℂ) * Complex.I) *
        (M (-(2*Real.pi)*p.1) *
          (Complex.exp ((↑(-2*Real.pi*(p.2*p.1)) : ℂ) * Complex.I) * f p.2)))
      (volume.prod volume)
    exact he1.mul (hMe.mul (he2.mul hfe))
  have hFint : Integrable (Function.uncurry F) (volume.prod volume) := by
    refine hdom_int.mono' hFae ?_
    filter_upwards with p
    show ‖Complex.exp ((↑(2*Real.pi*(p.1*x)) : ℂ) * Complex.I) *
        (M (-(2*Real.pi)*p.1) *
          (Complex.exp ((↑(-2*Real.pi*(p.2*p.1)) : ℂ) * Complex.I) * f p.2))‖
      ≤ ‖M (-(2*Real.pi)*p.1)‖ * ‖f p.2‖
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I,
      Complex.norm_exp_ofReal_mul_I, one_mul, one_mul]
  have h1 : FourierTransformInv.fourierInv
        (fun ξ => M (-(2*Real.pi)*ξ) * FourierTransform.fourier f ξ) x
      = ∫ v, Complex.exp ((↑(2*Real.pi*(v*x)) : ℂ) * Complex.I) *
          (M (-(2*Real.pi)*v) * FourierTransform.fourier f v) := by
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with v
    simp only [Real.inner_apply, smul_eq_mul]
  have h2 : (∫ v, Complex.exp ((↑(2*Real.pi*(v*x)) : ℂ) * Complex.I) *
          (M (-(2*Real.pi)*v) * FourierTransform.fourier f v))
      = ∫ v, ∫ y, F v y := by
    apply integral_congr_ae
    filter_upwards with v
    rw [Real.fourier_eq']
    simp only [Real.inner_apply, smul_eq_mul]
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  have h3 : (∫ v, ∫ y, F v y) = ∫ y, ∫ v, F v y := integral_integral_swap hFint
  rw [h1, h2, h3]
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  have hpt : (∫ v, F v y)
      = f y * ∫ v, Complex.exp ((↑(2*Real.pi*v*(x-y)) : ℂ) * Complex.I) *
          M (-(2*Real.pi)*v) := by
    rw [show (∫ v, F v y)
        = ∫ v, f y * (Complex.exp ((↑(2*Real.pi*v*(x-y)) : ℂ) * Complex.I) *
            M (-(2*Real.pi)*v)) from ?_]
    · rw [MeasureTheory.integral_const_mul]
    · apply integral_congr_ae
      filter_upwards with v
      have hAB : Complex.exp ((↑(2*Real.pi*(v*x)) : ℂ) * Complex.I) *
            Complex.exp ((↑(-2*Real.pi*(y*v)) : ℂ) * Complex.I)
          = Complex.exp ((↑(2*Real.pi*v*(x-y)) : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      show Complex.exp ((↑(2*Real.pi*(v*x)) : ℂ) * Complex.I) *
          (M (-(2*Real.pi)*v) *
            (Complex.exp ((↑(-2*Real.pi*(y*v)) : ℂ) * Complex.I) * f y))
          = f y * (Complex.exp ((↑(2*Real.pi*v*(x-y)) : ℂ) * Complex.I) *
              M (-(2*Real.pi)*v))
      rw [← hAB]; ring
  rw [hpt, conv_kernel_change_of_variables M (x - y)]
  ring

end Commons.Analysis.Fourier