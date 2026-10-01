import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Commons.Analysis.Integral.laplace_bound_piecewiseC2

namespace Commons.Analysis.Complex

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

/-- The Fourier transform `𝓕 H` of an integrable function `H : ℝ → ℂ` is continuous. -/
lemma laplace_aux_continuous_fourier {h : ℝ → ℂ} (hh : MeasureTheory.Integrable h) :
    Continuous (fun x : ℝ => 𝓕 h x) := by
  have hc : Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) h) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hh
  convert hc using 1

lemma laplace_aux_fourier_integrable {f : ℝ → ℂ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hcont : ContinuousOn f (Set.Icc 0 x₀))
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hbound : ∃ B : ℝ, ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvanish : ∀ t : ℝ, x₀ ≤ t → f t = 0) (hf0 : f 0 = 0)
    {c : ℝ} (hc : 0 < c) :
    MeasureTheory.Integrable (𝓕 (fun s : ℝ => Complex.exp (-(c:ℂ) * (s:ℂ)) * f (max 0 (min s x₀)))) := by
  rcases hbound with ⟨B, hB⟩
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB (x₀/2) ⟨by linarith, by linarith⟩)
  set h : ℝ → ℂ := fun s => Complex.exp (-(c:ℂ) * (s:ℂ)) * f (max 0 (min s x₀)) with hh
  have hcont_h : Continuous h := by
    rw [hh]
    exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
      (hcont.comp_continuous (continuous_const.max (continuous_id.min continuous_const))
        (fun s => ⟨le_max_left _ _, max_le hx₀.le (min_le_right _ _)⟩))
  have hsupport : ∀ s : ℝ, s ∉ Set.Icc (0:ℝ) x₀ → h s = 0 := by
    intro s hs
    rw [Set.mem_Icc, not_and_or] at hs
    rcases hs with hs | hs
    · rw [not_le] at hs
      have hcl : max 0 (min s x₀) = 0 := by
        rw [min_eq_left (le_of_lt (lt_of_lt_of_le hs hx₀.le)), max_eq_left hs.le]
      simp only [hh]; rw [hcl, hf0, mul_zero]
    · rw [not_le] at hs
      have hcl : max 0 (min s x₀) = x₀ := by
        rw [min_eq_right hs.le, max_eq_right hx₀.le]
      simp only [hh]; rw [hcl, hvanish x₀ le_rfl, mul_zero]
  have hS : MeasureTheory.Integrable h := hcont_h.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc (fun s hs => by
      by_contra hmem; exact hs (hsupport s hmem)))
  have hcontF : Continuous (fun w : ℝ => 𝓕 h w) := laplace_aux_continuous_fourier hS
  have hFt : ∀ w : ℝ, 𝓕 h w = ∫ s in (0:ℝ)..x₀,
      Complex.exp (-(((c:ℂ) + ↑(2*Real.pi*w) * Complex.I) * (s:ℂ))) * f s := by
    intro w
    have key : ∀ s : ℝ,
        Complex.exp (↑(-2*Real.pi*(s*w))*Complex.I) * Complex.exp (-(c:ℂ)*(s:ℂ))
          = Complex.exp (-(((c:ℂ) + ↑(2*Real.pi*w) * Complex.I) * (s:ℂ))) := by
      intro s
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have hind : (Set.Icc (0:ℝ) x₀).indicator
          (fun s => Complex.exp (-(((c:ℂ)+↑(2*Real.pi*w) * Complex.I)*(s:ℂ))) * f s)
        = fun s => Complex.exp (↑(-2*Real.pi*(s*w))*Complex.I) • h s := by
      funext s
      by_cases hs : s ∈ Set.Icc (0:ℝ) x₀
      · rw [Set.indicator_of_mem hs, smul_eq_mul]
        have hcl : max 0 (min s x₀) = s := by rw [min_eq_left hs.2, max_eq_right hs.1]
        simp only [hh]; rw [hcl]
        rw [← mul_assoc, key s]
      · rw [Set.indicator_of_notMem hs, hsupport s hs, smul_zero]
    calc 𝓕 h w = ∫ s : ℝ, Complex.exp (↑(-2*Real.pi*(s*w))*Complex.I) • h s := by
          rw [Real.fourier_eq']
          apply integral_congr_ae
          filter_upwards with s
          rw [Real.inner_apply]
      _ = ∫ s : ℝ, (Set.Icc (0:ℝ) x₀).indicator
            (fun s => Complex.exp (-(((c:ℂ)+↑(2*Real.pi*w) * Complex.I)*(s:ℂ))) * f s) s := by
          rw [← hind]
      _ = ∫ s in (0:ℝ)..x₀, Complex.exp (-(((c:ℂ)+↑(2*Real.pi*w) * Complex.I)*(s:ℂ))) * f s := by
          rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le hx₀.le]
  have hzn : ∀ w : ℝ, ‖(c:ℂ) + ↑(2*Real.pi*w) * Complex.I‖^2 = c^2 + (2*Real.pi*w)^2 := by
    intro w
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hpt : ∀ w : ℝ, ‖𝓕 h w‖ ≤ 3 * B * x₀ / (c^2 + (2*Real.pi*w)^2) := by
    intro w
    rw [hFt w]
    have hzre : 0 < ((c:ℂ) + ↑(2*Real.pi*w) * Complex.I).re := by
      rw [show ((c:ℂ) + ↑(2*Real.pi*w) * Complex.I).re = c by
        simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]]
      exact hc
    have h := Commons.Analysis.Integral.laplace_bound_piecewiseC2 hx₀ hcont hf2 hB
      (hvanish x₀ le_rfl) hf0 hzre
    calc ‖∫ s in (0:ℝ)..x₀, Complex.exp (-(((c:ℂ)+↑(2*Real.pi*w) * Complex.I)*(s:ℂ))) * f s‖
        ≤ (1 / ‖(c:ℂ) + ↑(2*Real.pi*w) * Complex.I‖^2) * (3 * B * x₀) := h
      _ = 3 * B * x₀ / (c^2 + (2*Real.pi*w)^2) := by rw [hzn w]; ring
  set m : ℝ := min (c^2) (4*Real.pi^2) with hm
  have hmpos : 0 < m := by rw [hm]; exact lt_min (by positivity) (by positivity)
  set C : ℝ := 3 * B * x₀ / m with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; exact div_nonneg (by positivity) hmpos.le
  have hbound2 : ∀ w : ℝ, ‖𝓕 h w‖ ≤ C * (1 + w^2)⁻¹ := by
    intro w
    have hkey : m * (1 + w^2) ≤ c^2 + (2*Real.pi*w)^2 := by
      have h1 : m ≤ c^2 := by rw [hm]; exact min_le_left _ _
      have h2 : m ≤ 4*Real.pi^2 := by rw [hm]; exact min_le_right _ _
      have h3 : m * w^2 ≤ 4*Real.pi^2 * w^2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg w)
      have hsq : (2*Real.pi*w)^2 = 4*Real.pi^2 * w^2 := by ring
      nlinarith [h1, h3, hsq]
    have hpos1 : 0 < c^2 + (2*Real.pi*w)^2 := by positivity
    have hpos2 : 0 < m * (1 + w^2) := mul_pos hmpos (by positivity)
    have h1 : (c^2 + (2*Real.pi*w)^2)⁻¹ ≤ m⁻¹ * (1 + w^2)⁻¹ := by
      have := (inv_le_inv₀ hpos1 hpos2).mpr hkey
      rwa [mul_inv] at this
    have hK0 : 0 ≤ 3 * B * x₀ := by positivity
    have hgoal : 3 * B * x₀ / (c^2 + (2*Real.pi*w)^2) ≤ (3 * B * x₀ / m) * (1 + w^2)⁻¹ := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      calc 3 * B * x₀ * (c^2 + (2*Real.pi*w)^2)⁻¹
          ≤ 3 * B * x₀ * (m⁻¹ * (1 + w^2)⁻¹) := mul_le_mul_of_nonneg_left h1 hK0
        _ = 3 * B * x₀ * m⁻¹ * (1 + w^2)⁻¹ := by ring
    calc ‖𝓕 h w‖ ≤ 3 * B * x₀ / (c^2 + (2*Real.pi*w)^2) := hpt w
      _ ≤ C * (1 + w^2)⁻¹ := by rw [hCdef]; exact hgoal
  refine MeasureTheory.Integrable.mono (Integrable.const_mul integrable_inv_one_add_sq C)
    hcontF.aestronglyMeasurable ?_
  filter_upwards with w
  have h5 : ‖C * (1 + w^2)⁻¹‖ = C * (1 + w^2)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC0 (inv_nonneg.mpr (by positivity)))]
  rw [h5]
  exact hbound2 w

theorem laplace_inversion_piecewise_C2 {f : ℝ → ℂ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hcont : ContinuousOn f (Set.Icc 0 x₀))
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hbound : ∃ B : ℝ, ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvanish : ∀ t : ℝ, x₀ ≤ t → f t = 0) (hf0 : f 0 = 0)
    {c : ℝ} (hc : 0 < c) :
    ∀ t : ℝ, 0 < t →
      f t = (1 / (2 * Real.pi)) * ∫ γ : ℝ,
        (∫ s in (0:ℝ)..x₀, Complex.exp (-(((c : ℂ) + γ * Complex.I) * (s : ℂ))) * f s) *
          Complex.exp ((((c : ℂ) + γ * Complex.I)) * (t : ℂ)) := by
  intro t ht
  set h : ℝ → ℂ := fun s => Complex.exp (-(c : ℂ) * (s : ℂ)) * f (max 0 (min s x₀)) with hh
  have hφ_cont : Continuous (fun s : ℝ => (max 0 (min s x₀) : ℝ)) :=
    continuous_const.max (continuous_id.min continuous_const)
  have hφ_mem : ∀ s : ℝ, max 0 (min s x₀) ∈ Set.Icc (0:ℝ) x₀ := by
    intro s
    exact ⟨le_max_left _ _, max_le hx₀.le (min_le_right _ _)⟩
  have hfφ_cont : Continuous (fun s : ℝ => f (max 0 (min s x₀))) :=
    hcont.comp_continuous hφ_cont hφ_mem
  have hcont_h : Continuous h := by
    rw [hh]
    exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul hfφ_cont
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
      rw [hcl, hvanish x₀ le_rfl, mul_zero]
  have hcpt_h : HasCompactSupport h :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (fun s hs => by
      by_contra hmem
      exact hs (hzero_h s hmem))
  have hS : Integrable h := hcont_h.integrable_of_hasCompactSupport hcpt_h
  have hFS : Integrable (𝓕 h) := laplace_aux_fourier_integrable hx₀ hcont hf2 hbound hvanish hf0 hc
  have hinv : 𝓕⁻ (𝓕 h) t = h t :=
    MeasureTheory.Integrable.fourierInv_fourier_eq hS hFS hcont_h.continuousAt
  have hinner : ∀ γ : ℝ, (∫ s in (0:ℝ)..x₀, Complex.exp (-(((c : ℂ) + γ * Complex.I) * (s : ℂ))) * f s)
      = 𝓕 h (γ / (2 * Real.pi)) := by
    intro γ
    have key : ∀ s : ℝ,
        Complex.exp (↑(-2 * Real.pi * (s * (γ / (2 * Real.pi)))) * Complex.I) * Complex.exp (-(c:ℂ)*(s:ℂ))
          = Complex.exp (-(((c:ℂ) + γ * Complex.I) * (s:ℂ))) := by
      intro s
      rw [← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring
    have hind : (Set.Icc (0:ℝ) x₀).indicator (fun s => Complex.exp (-(((c : ℂ) + γ * Complex.I) * (s : ℂ))) * f s)
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
  have h2πpos : (0:ℝ) < 2 * Real.pi := by positivity
  have h2πneR : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt h2πpos
  have h2πneC : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h2πneR
  have h2πneC' : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 := by exact_mod_cast h2πneR
  have hsub : (∫ γ : ℝ, 𝓕 h (γ / (2 * Real.pi)) * Complex.exp (((c : ℂ) + ↑γ * Complex.I) * (t : ℂ)))
      = ((2 * Real.pi : ℝ) : ℂ) * ∫ w : ℝ, (𝓕 h ((2 * Real.pi * w) / (2 * Real.pi)) *
          Complex.exp (((c : ℂ) + ↑(2*Real.pi*w) * Complex.I) * (t : ℂ))) := by
    have hA := Measure.integral_comp_mul_left
      (fun x : ℝ => 𝓕 h (x / (2 * Real.pi)) * Complex.exp (((c : ℂ) + ↑x * Complex.I) * (t : ℂ)))
      (2 * Real.pi)
    rw [abs_of_pos (by positivity : (0:ℝ) < (2 * Real.pi)⁻¹)] at hA
    have hA' : (∫ x : ℝ, 𝓕 h ((2 * Real.pi * x) / (2 * Real.pi)) *
          Complex.exp (((c : ℂ) + ↑(2 * Real.pi * x) * Complex.I) * (t : ℂ)))
        = (↑((2 * Real.pi)⁻¹) : ℂ) * (∫ y : ℝ, 𝓕 h (y / (2 * Real.pi)) *
            Complex.exp (((c : ℂ) + ↑y * Complex.I) * (t : ℂ))) := by
      simpa only [Complex.real_smul] using hA
    rw [hA', ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ h2πneR, Complex.ofReal_one, one_mul]
  have hsub2 : (∫ w : ℝ, (𝓕 h ((2 * Real.pi * w) / (2 * Real.pi)) *
          Complex.exp (((c : ℂ) + ↑(2*Real.pi*w) * Complex.I) * (t : ℂ))))
      = ∫ w : ℝ, 𝓕 h w * Complex.exp (((c : ℂ) + ↑(2*Real.pi*w) * Complex.I) * (t : ℂ)) := by
    apply integral_congr_ae
    filter_upwards with w
    rw [mul_div_cancel_left₀ _ h2πneR]
  have hfac : ∀ w : ℝ, 𝓕 h w * Complex.exp (((c : ℂ) + ↑(2*Real.pi*w) * Complex.I) * (t : ℂ))
      = Complex.exp ((c : ℂ) * (t : ℂ)) * (𝓕 h w * Complex.exp ((↑(2 * Real.pi * (w * t)) : ℝ) * Complex.I)) := by
    intro w
    have key : ((c : ℂ) + ↑(2*Real.pi*w) * Complex.I) * (t : ℂ)
        = (c : ℂ) * (t : ℂ) + (↑(2 * Real.pi * (w * t)) : ℝ) * Complex.I := by
      push_cast
      ring
    rw [key, Complex.exp_add]
    ring
  have hIntFac : (∫ w : ℝ, 𝓕 h w * Complex.exp (((c : ℂ) + ↑(2*Real.pi*w) * Complex.I) * (t : ℂ)))
      = Complex.exp ((c : ℂ) * (t : ℂ)) *
        ∫ w : ℝ, 𝓕 h w * Complex.exp ((↑(2 * Real.pi * (w * t)) : ℝ) * Complex.I) := by
    simp_rw [hfac]
    rw [integral_const_mul]
  have hInv : (∫ w : ℝ, 𝓕 h w * Complex.exp ((↑(2 * Real.pi * (w * t)) : ℝ) * Complex.I))
      = 𝓕⁻ (𝓕 h) t := by
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with w
    simp only [Real.inner_apply, smul_eq_mul]
    ring
  have hct : Complex.exp ((c : ℂ) * (t : ℂ)) * h t = f t := by
    by_cases htx : t ≤ x₀
    · have hcl : max 0 (min t x₀) = t := by
        rw [min_eq_left htx, max_eq_right ht.le]
      simp only [hh]
      rw [hcl]
      rw [← mul_assoc, ← Complex.exp_add, show (c:ℂ)*(t:ℂ) + -(c:ℂ)*(t:ℂ) = 0 by ring,
        Complex.exp_zero, one_mul]
    · have htx' : x₀ < t := not_le.mp htx
      have hcl : max 0 (min t x₀) = x₀ := by
        rw [min_eq_right htx'.le, max_eq_right hx₀.le]
      simp only [hh]
      rw [hcl, hvanish x₀ le_rfl, mul_zero, mul_zero, hvanish t htx'.le]
  have hLHS : (∫ γ : ℝ, (∫ s in (0:ℝ)..x₀, Complex.exp (-(((c : ℂ) + γ * Complex.I) * (s : ℂ))) * f s)
        * Complex.exp (((c : ℂ) + γ * Complex.I) * (t : ℂ))) = ((2 * Real.pi : ℝ) : ℂ) * f t := by
    have e1 : (∫ γ : ℝ, (∫ s in (0:ℝ)..x₀, Complex.exp (-(((c : ℂ) + γ * Complex.I) * (s : ℂ))) * f s)
        * Complex.exp (((c : ℂ) + γ * Complex.I) * (t : ℂ)))
        = ∫ γ : ℝ, 𝓕 h (γ / (2 * Real.pi)) * Complex.exp (((c : ℂ) + ↑γ * Complex.I) * (t : ℂ)) := by
      apply integral_congr_ae
      filter_upwards with γ
      rw [hinner γ]
    rw [e1, hsub, hsub2, hIntFac, hInv, hinv, hct]
  rw [hLHS, one_div]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ h2πneC', one_mul]


end Commons.Analysis.Complex