import Mathlib
import Submission.Commons.Analysis.Complex.laplace_inversion_piecewise_C2
import Submission.Commons.Analysis.Integral.tendsto_interval_integral_atTop

namespace Commons.Analysis.Complex

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

/-- The Laplace-type inner integral equals the Fourier transform of
`s ↦ exp (-c s) f (max 0 (min s x₀))`, evaluated at `γ / (2π)`. -/
lemma laplace_inner_eq_fourier {f : ℝ → ℂ} {x₀ c : ℝ} (hx₀ : 0 < x₀)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) (hf0 : f 0 = 0)
    (γ : ℝ) :
    (∫ s in (0:ℝ)..x₀, Complex.exp (-(((c : ℂ) + γ * Complex.I) * (s : ℂ))) * f s)
      = 𝓕 (fun s : ℝ => Complex.exp (-(c : ℂ) * (s : ℂ)) * f (max 0 (min s x₀)))
          (γ / (2 * Real.pi)) := by
  set h : ℝ → ℂ := fun s => Complex.exp (-(c : ℂ) * (s : ℂ)) * f (max 0 (min s x₀)) with hh
  have hzero_h : ∀ s : ℝ, s ∉ Set.Icc (0:ℝ) x₀ → h s = 0 := by
    intro s hs
    rw [Set.mem_Icc, not_and_or] at hs
    rcases hs with hs | hs
    · rw [not_le] at hs
      have hcl : max 0 (min s x₀) = 0 := by
        rw [min_eq_left (le_of_lt (lt_of_lt_of_le hs hx₀.le)), max_eq_left hs.le]
      simp only [hh]
      rw [hcl, hf0, mul_zero]
    · rw [not_le] at hs
      have hcl : max 0 (min s x₀) = x₀ := by
        rw [min_eq_right hs.le, max_eq_right hx₀.le]
      simp only [hh]
      rw [hcl, hvan x₀ le_rfl, mul_zero]
  have key : ∀ s : ℝ,
      Complex.exp (↑(-2 * Real.pi * (s * (γ / (2 * Real.pi)))) * Complex.I) *
          Complex.exp (-(c:ℂ)*(s:ℂ))
        = Complex.exp (-(((c:ℂ) + γ * Complex.I) * (s:ℂ))) := by
    intro s
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  have hind : (Set.Icc (0:ℝ) x₀).indicator
        (fun s => Complex.exp (-(((c : ℂ) + γ * Complex.I) * (s : ℂ))) * f s)
      = fun s => Complex.exp (↑(-2 * Real.pi * (s * (γ / (2 * Real.pi)))) * Complex.I) • h s := by
    funext s
    by_cases hs : s ∈ Set.Icc (0:ℝ) x₀
    · rw [Set.indicator_of_mem hs]
      rw [smul_eq_mul]
      have hcl : max 0 (min s x₀) = s := by
        rw [min_eq_left hs.2, max_eq_right hs.1]
      simp only [hh]
      rw [hcl]
      rw [← mul_assoc, key s]
    · rw [Set.indicator_of_notMem hs, hzero_h s hs, smul_zero]
  have hmain : (∫ s in (0:ℝ)..x₀, Complex.exp (-(((c : ℂ) + γ * Complex.I) * (s : ℂ))) * f s)
      = 𝓕 h (γ / (2 * Real.pi)) := by
    calc (∫ s in (0:ℝ)..x₀, Complex.exp (-(((c : ℂ) + γ * Complex.I) * (s : ℂ))) * f s)
        = ∫ s : ℝ, (Set.Icc (0:ℝ) x₀).indicator
            (fun s => Complex.exp (-(((c : ℂ) + γ * Complex.I) * (s : ℂ))) * f s) s := by
          rw [intervalIntegral.integral_of_le hx₀.le, ← integral_Icc_eq_integral_Ioc,
            ← integral_indicator measurableSet_Icc]
      _ = ∫ s : ℝ, Complex.exp (↑(-2 * Real.pi * (s * (γ / (2 * Real.pi)))) * Complex.I) • h s := by
          apply integral_congr_ae
          filter_upwards with s
          exact congrFun hind s
      _ = 𝓕 h (γ / (2 * Real.pi)) := by
          rw [Real.fourier_eq']
          apply integral_congr_ae
          filter_upwards with v
          rw [Real.inner_apply]
  simpa only [hh] using hmain

theorem laplace_inversion_compact {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) (hf0 : f 0 = 0)
    {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : t ∈ Set.Ioo 0 x₀) :
    Filter.Tendsto (fun T : ℝ => (1 / (2 * (Real.pi : ℂ))) *
        ∫ τ : ℝ in -T..T,
          (∫ u in (0:ℝ)..x₀, Complex.exp (-(((c : ℂ) + (τ : ℂ) * Complex.I) * (u : ℂ))) * f u) *
            Complex.exp (((c : ℂ) + (τ : ℂ) * Complex.I) * (t : ℂ)))
      Filter.atTop (nhds (f t)) := by
  have _hBref : (0:ℝ) ≤ B := hB
  have h2πpos : (0:ℝ) < 2 * Real.pi := by positivity
  have h2πneR : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt h2πpos
  set h : ℝ → ℂ := fun s => Complex.exp (-(c : ℂ) * (s : ℂ)) * f (max 0 (min s x₀)) with hh
  have hFS : Integrable (𝓕 h) := by
    rw [hh]
    exact laplace_aux_fourier_integrable hx₀ hcont hf2 ⟨B, hBnd⟩ hvan hf0 hc
  set F : ℝ → ℂ := fun γ => ∫ s in (0:ℝ)..x₀,
      Complex.exp (-(((c : ℂ) + γ * Complex.I) * (s : ℂ))) * f s with hF
  set W : ℝ → ℂ := fun γ => Complex.exp (((c : ℂ) + γ * Complex.I) * (t : ℂ)) with hW
  set G : ℝ → ℂ := fun γ => F γ * W γ with hG
  have hinner : ∀ γ : ℝ, F γ = 𝓕 h (γ / (2 * Real.pi)) := by
    intro γ
    rw [hF, hh]
    exact laplace_inner_eq_fourier hx₀ hvan hf0 γ
  have hWcont : Continuous W := by rw [hW]; fun_prop
  have hWnorm : ∀ γ : ℝ, ‖W γ‖ = Real.exp (c * t) := by
    intro γ
    rw [hW, Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have hbint : Integrable (fun γ : ℝ => 𝓕 h (γ / (2 * Real.pi)) * W γ) := by
    have h1 : Integrable (fun γ : ℝ => 𝓕 h (γ / (2 * Real.pi))) := hFS.comp_div h2πneR
    have h2 : Integrable (fun γ : ℝ => Real.exp (c * t) * ‖𝓕 h (γ / (2 * Real.pi))‖) :=
      h1.norm.const_mul _
    refine Integrable.mono' h2 (h1.aestronglyMeasurable.mul hWcont.aestronglyMeasurable) ?_
    filter_upwards with γ
    rw [norm_mul, hWnorm γ, mul_comm]
  have hGint : Integrable G := by
    rw [hG]
    refine hbint.congr (Filter.Eventually.of_forall (fun γ => ?_))
    simp only [hinner γ]
  have htend := Commons.Analysis.Integral.tendsto_interval_integral_atTop G hGint
  have hpiece := laplace_inversion_piecewise_C2 hx₀ hcont hf2 ⟨B, hBnd⟩ hvan hf0 hc t ht.1
  have hIntEq : (∫ τ : ℝ, G τ) = ∫ γ : ℝ,
      (∫ s in (0:ℝ)..x₀, Complex.exp (-(((c : ℂ) + γ * Complex.I) * (s : ℂ))) * f s) *
        Complex.exp (((c : ℂ) + γ * Complex.I) * (t : ℂ)) := by
    apply integral_congr_ae
    filter_upwards with γ
    simp only [hG, hF, hW]
  have hlim_eq : (1 / (2 * (Real.pi : ℂ))) * ∫ τ : ℝ, G τ = f t := by
    rw [hIntEq, ← hpiece]
  rw [← hlim_eq]
  exact htend.const_mul (1 / (2 * (Real.pi : ℂ)))

end Commons.Analysis.Complex
