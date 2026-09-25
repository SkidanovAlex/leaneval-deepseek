import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Commons.Analysis.Fourier.bandTerm_apply

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped Interval

/-- The windowed band integral `∫_{λ-h}^{λ+h} φ((θ-λ)/h) e^{-I(x-y)θ} dθ`, the building block of
the band sum. -/
noncomputable def bandWindowTerm (φ : ℝ → ℝ) (lam h x y : ℝ) : ℂ :=
  ∫ th in (lam - h)..(lam + h),
    (φ ((th - lam) / h) : ℂ) * Complex.exp (-(Complex.I * ((x - y : ℝ) : ℂ) * (th : ℂ)))

/-- Closed form of the windowed band integral, obtained from the substitution `θ = λ + h u`
together with the support hypothesis on `φ`. -/
theorem bandWindowTerm_closed (φ : ℝ → ℝ) (hsupp : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    {lam h x : ℝ} (hh : 0 < h) (y : ℝ) :
    bandWindowTerm φ lam h x y
      = (h : ℂ) * (∫ u : ℝ, (φ u : ℂ) *
            Complex.exp (-(Complex.I * ((h * (x - y) : ℝ) : ℂ) * (u : ℂ))))
          * Complex.exp (-(Complex.I * (lam : ℂ) * ((x - y : ℝ) : ℂ))) := by
  rw [bandWindowTerm]
  exact bandTerm_apply φ hsupp hh

/-- Uniform norm bound for the windowed band integral: at most the length `2h` of the band. -/
theorem bandWindowTerm_norm_le (φ : ℝ → ℝ) (hbd : ∀ x : ℝ, ‖φ x‖ ≤ 1)
    {lam h x : ℝ} (hh : 0 ≤ h) (y : ℝ) :
    ‖bandWindowTerm φ lam h x y‖ ≤ 2 * h := by
  rw [bandWindowTerm]
  have h1 : ∀ th : ℝ, ‖(φ ((th - lam) / h) : ℂ) *
      Complex.exp (-(Complex.I * ((x - y : ℝ) : ℂ) * (th : ℂ)))‖ ≤ 1 := by
    intro th
    rw [norm_mul, show Complex.exp (-(Complex.I * ((x - y : ℝ) : ℂ) * (th : ℂ)))
        = Complex.exp (((-(x - y) * th : ℝ) : ℂ) * Complex.I) by congr 1; push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    simpa using hbd ((th - lam) / h)
  calc ‖∫ th in (lam - h)..(lam + h), (φ ((th - lam) / h) : ℂ) *
        Complex.exp (-(Complex.I * ((x - y : ℝ) : ℂ) * (th : ℂ)))‖
      ≤ 1 * |(lam + h) - (lam - h)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (fun th _ => h1 th)
    _ = 2 * h := by rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ lam + h - (lam - h))]; ring

/-- Continuity of the windowed band integral in the spatial variable `y`. -/
theorem bandWindowTerm_continuous (φ : ℝ → ℝ) (hφ : Continuous φ) (lam h x : ℝ) :
    Continuous (fun y : ℝ => bandWindowTerm φ lam h x y) := by
  have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := (volume : Measure ℝ))
    (f := fun y th : ℝ => (φ ((th - lam) / h) : ℂ) *
      Complex.exp (-(Complex.I * ((x - y : ℝ) : ℂ) * (th : ℂ)))) (by fun_prop) (lam - h) (lam + h)
  simpa [bandWindowTerm] using h

/-- Integrability of `f` times the windowed band integral, for `f ∈ L¹`. -/
theorem bandWindowTerm_integrable (φ : ℝ → ℝ) (hbd : ∀ x : ℝ, ‖φ x‖ ≤ 1)
    (hcontφ : Continuous φ) {f : ℝ → ℂ} (hf1 : MemLp f 1 (volume : Measure ℝ))
    {lam h x : ℝ} (hh : 0 ≤ h) :
    Integrable (fun y : ℝ => f y * bandWindowTerm φ lam h x y) (volume : Measure ℝ) := by
  refine Integrable.mono' (((memLp_one_iff_integrable.mp hf1).norm).const_mul (2 * h))
    (hf1.aestronglyMeasurable.mul
      ((bandWindowTerm_continuous φ hcontφ lam h x).aestronglyMeasurable)) ?_
  filter_upwards with y
  rw [norm_mul]
  calc ‖f y‖ * ‖bandWindowTerm φ lam h x y‖ ≤ ‖f y‖ * (2 * h) :=
        mul_le_mul_of_nonneg_left (bandWindowTerm_norm_le φ hbd hh y) (norm_nonneg _)
    _ = 2 * h * ‖f y‖ := by ring

/-- Pointwise reordering identity for the exponential factor of a single band. -/
theorem bandWindowTerm_exp (lam x : ℝ) :
    ∀ y : ℝ, Complex.exp (-(Complex.I * (lam : ℂ) * ((x - y : ℝ) : ℂ)))
      = Complex.exp (Complex.I * (lam : ℂ) * (y : ℂ)) *
        Complex.exp (-(Complex.I * (lam : ℂ) * (x : ℂ))) := by
  intro y
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- One-band windowed identity: the `y`-integral of `f` against a single band equals the
windowed smoothing of the modulated function, times the modulation factor `e^{-Iλx}`. -/
theorem bandWindowTerm_windowed (φ : ℝ → ℝ) (hsupp : ∀ x : ℝ, 1 ≤ |x| → φ x = 0)
    {lam h : ℝ} (hh : 0 < h) {f : ℝ → ℂ} (x : ℝ) :
    (∫ y : ℝ, f y * bandWindowTerm φ lam h x y)
      = (∫ y : ℝ, f y * Complex.exp (Complex.I * (lam : ℂ) * (y : ℂ)) *
            ((h : ℂ) * ∫ u : ℝ, (φ u : ℂ) *
              Complex.exp (-(Complex.I * ((h * (x - y) : ℝ) : ℂ) * (u : ℂ)))))
          * Complex.exp (-(Complex.I * (lam : ℂ) * (x : ℂ))) := by
  have hcongr : (∫ y : ℝ, f y * bandWindowTerm φ lam h x y)
      = ∫ y : ℝ, f y * ((h : ℂ) * (∫ u : ℝ, (φ u : ℂ) *
            Complex.exp (-(Complex.I * ((h * (x - y) : ℝ) : ℂ) * (u : ℂ)))))
          * Complex.exp (-(Complex.I * (lam : ℂ) * ((x - y : ℝ) : ℂ))) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [bandWindowTerm_closed φ hsupp hh y]
    ring
  rw [hcongr, ← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with y
  rw [bandWindowTerm_exp lam x y]
  ring

set_option linter.unusedVariables false in
theorem bandSum_windowed (K : ℕ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ⊤ φ)
    (hbd : ∀ x : ℝ, ‖φ x‖ ≤ 1) (hsupp : ∀ x : ℝ, 1 ≤ |x| → φ x = 0) (lam : Fin K → ℝ)
    {h : ℝ} (hh : 0 < h)
    {f : ℝ → ℂ} (hf1 : MeasureTheory.MemLp f 1 MeasureTheory.volume)
    (hf2 : MeasureTheory.MemLp f 2 MeasureTheory.volume) (x : ℝ) :
    (∫ y : ℝ, f y * (∑ k : Fin K,
        ∫ th in (lam k - h)..(lam k + h),
          (φ ((th - lam k) / h) : ℂ) *
            Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (th : ℂ)))))
      = ∑ k : Fin K,
          (∫ y : ℝ, f y * Complex.exp (Complex.I * (lam k : ℂ) * (y : ℂ)) *
              ((h : ℂ) * ∫ u : ℝ, (φ u : ℂ) *
                Complex.exp (-(Complex.I * ((h * (x - y) : ℝ) : ℂ) * (u : ℂ)))))
            * Complex.exp (-(Complex.I * (lam k : ℂ) * (x : ℂ))) := by
  have hLHS : (∫ y : ℝ, f y * (∑ k : Fin K, bandWindowTerm φ (lam k) h x y))
      = (∫ y : ℝ, f y * (∑ k : Fin K,
          ∫ th in (lam k - h)..(lam k + h),
            (φ ((th - lam k) / h) : ℂ) *
              Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (th : ℂ))))) := rfl
  rw [← hLHS]
  have hint : ∀ k : Fin K, Integrable (fun y : ℝ => f y * bandWindowTerm φ (lam k) h x y)
      (volume : Measure ℝ) :=
    fun k => bandWindowTerm_integrable φ hbd hφ.continuous hf1 hh.le
  have hpt : (fun y : ℝ => f y * (∑ k : Fin K, bandWindowTerm φ (lam k) h x y))
      = fun y : ℝ => ∑ k : Fin K, f y * bandWindowTerm φ (lam k) h x y := by
    funext y
    rw [Finset.mul_sum]
  rw [hpt, integral_finsetSum _ (fun k _ => hint k)]
  exact Finset.sum_congr rfl (fun k _ => bandWindowTerm_windowed φ hsupp hh x)

end Commons.Analysis.Fourier
