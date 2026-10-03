import Mathlib.Algebra.Ring.IsFormallyReal
import Submission.Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

/-- The Fourier transform on `ℝ` written as an integral against `exp(-2πi u s)`. -/
private lemma fourier_real_eq_integral (f : ℝ → ℂ) (s : ℝ) :
    𝓕 f s = ∫ u : ℝ, f u * Complex.exp (-(2 * Real.pi * Complex.I) * ((u * s : ℝ) : ℂ)) := by
  rw [Real.fourier_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  simp only [Circle.smul_def, smul_eq_mul]
  rw [mul_comm]
  congr 1
  rw [Real.fourierChar_apply, Real.inner_apply]
  congr 1
  push_cast
  ring

/-- The angular Fourier integral at frequency `t` equals the standard Fourier transform at
`t / (2π)`. -/
private lemma angular_eq_fourier (f : ℝ → ℂ) (t : ℝ) :
    (∫ u : ℝ, f u * Complex.exp (-(Complex.I * (t : ℂ) * (u : ℂ))))
      = 𝓕 f (t / (2 * Real.pi)) := by
  rw [fourier_real_eq_integral f (t / (2 * Real.pi))]
  apply integral_congr_ae
  filter_upwards with u
  congr 1
  push_cast
  field_simp

/-- Rescaling the Fourier integral: substituting `u = h v`. -/
private lemma integral_comp_div_mul_exp (f : ℝ → ℂ) {h : ℝ} (hh : 0 < h) (τ : ℝ) :
    (∫ u : ℝ, (f (u / h) / (h : ℂ)) * Complex.exp (-(Complex.I * (τ : ℂ) * (u : ℂ))))
      = ∫ v : ℝ, f v * Complex.exp (-(Complex.I * ((τ * h : ℝ) : ℂ) * (v : ℂ))) := by
  have hne : h ≠ 0 := ne_of_gt hh
  have hcne : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hne
  rw [show (∫ u : ℝ, (f (u / h) / (h : ℂ)) * Complex.exp (-(Complex.I * (τ : ℂ) * (u : ℂ))))
      = (1 / (h : ℂ)) * ∫ u : ℝ, f (u / h) * Complex.exp (-(Complex.I * (τ : ℂ) * (u : ℂ))) from by
        rw [← MeasureTheory.integral_const_mul]
        apply integral_congr_ae
        filter_upwards with u
        ring]
  have hsub := MeasureTheory.Measure.integral_comp_div
      (fun v : ℝ => f v * Complex.exp (-(Complex.I * ((τ * h : ℝ) : ℂ) * (v : ℂ)))) h
  have hpt : ∀ x : ℝ, f (x / h) * Complex.exp (-(Complex.I * (τ : ℂ) * (x : ℂ)))
      = (fun v : ℝ => f v * Complex.exp (-(Complex.I * ((τ * h : ℝ) : ℂ) * (v : ℂ)))) (x / h) := by
    intro x
    have harg : Complex.I * (τ : ℂ) * (x : ℂ)
        = Complex.I * ((τ * h : ℝ) : ℂ) * ((x / h : ℝ) : ℂ) := by
      push_cast
      field_simp
    simp only [harg]
  rw [show (∫ u : ℝ, f (u / h) * Complex.exp (-(Complex.I * (τ : ℂ) * (u : ℂ))))
      = ∫ u : ℝ, (fun v : ℝ => f v * Complex.exp (-(Complex.I * ((τ * h : ℝ) : ℂ) * (v : ℂ)))) (u / h) from by
        apply integral_congr_ae
        filter_upwards with u
        exact hpt u]
  rw [hsub, abs_of_pos hh, Complex.real_smul]
  rw [← mul_assoc, one_div, inv_mul_cancel₀ hcne, one_mul]

/-- Polynomial decay of the angular Fourier integral of a smooth compactly supported function. -/
private lemma angular_fourier_decay (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcs : HasCompactSupport f) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖∫ u : ℝ, f u * Complex.exp (-(Complex.I * (t : ℂ) * (u : ℂ)))‖
        ≤ C * (1 + |t|) ^ (-(N : ℝ)) := by
  obtain ⟨C₁, hC₁, hdecay⟩ := fourierTransform_iteratedDeriv_decay N hf hcs
  set B : ℝ := ∫ u : ℝ, ‖f u‖ with hB
  have hBnn : 0 ≤ B := by rw [hB]; exact integral_nonneg (fun u => norm_nonneg _)
  have hgen : ∀ t : ℝ, ‖∫ u : ℝ, f u * Complex.exp (-(Complex.I * (t : ℂ) * (u : ℂ)))‖ ≤ B := by
    intro t
    rw [hB]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    apply integral_congr_ae
    filter_upwards with u
    rw [norm_mul]
    have hz : -(Complex.I * (t : ℂ) * (u : ℂ)) = ((-(t * u) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [hz, Complex.norm_exp_ofReal_mul_I, mul_one]
  refine ⟨max (B * (2:ℝ)^N) (C₁ * (2*Real.pi)^N * (2:ℝ)^N), ?_, ?_⟩
  · exact le_trans (mul_nonneg hBnn (pow_nonneg (by norm_num) N)) (le_max_left _ _)
  · intro t
    have hrpow : (1 + |t|)^(-(N:ℝ)) = ((1+|t|)^N)⁻¹ := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
    by_cases ht : |t| ≤ 1
    · have hpow : (1 + |t|)^N ≤ (2:ℝ)^N := by
        exact pow_le_pow_left₀ (by positivity) (by linarith) N
      have hinv : ((2:ℝ)^N)⁻¹ ≤ ((1+|t|)^N)⁻¹ := by
        rw [inv_le_inv₀ (pow_pos (by norm_num) N) (pow_pos (by positivity) N)]
        exact hpow
      calc ‖∫ u, f u * Complex.exp (-(Complex.I * (t:ℂ) * (u:ℂ)))‖
          ≤ B := hgen t
        _ = B * ((2:ℝ)^N * ((2:ℝ)^N)⁻¹) := by
              rw [mul_inv_cancel₀ (pow_ne_zero N (by norm_num))]; ring
        _ = B * (2:ℝ)^N * ((2:ℝ)^N)⁻¹ := by ring
        _ ≤ B * (2:ℝ)^N * ((1+|t|)^N)⁻¹ :=
              mul_le_mul_of_nonneg_left hinv (mul_nonneg hBnn (pow_nonneg (by norm_num) N))
        _ = B * (2:ℝ)^N * (1+|t|)^(-(N:ℝ)) := by rw [hrpow]
        _ ≤ max (B*(2:ℝ)^N) (C₁*(2*Real.pi)^N*(2:ℝ)^N) * (1+|t|)^(-(N:ℝ)) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _)
    · have ht' : 1 < |t| := lt_of_not_ge ht
      have htne : t ≠ 0 := by intro h0; rw [h0, abs_zero] at ht'; linarith
      have habs : 0 < |t| := abs_pos.mpr htne
      have hξne : t / (2*Real.pi) ≠ 0 := div_ne_zero htne (by positivity)
      have hdec := hdecay (t/(2*Real.pi)) hξne
      have hξabs : |t/(2*Real.pi)| = |t|/(2*Real.pi) := by
        rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)]
      have hξpow : |t/(2*Real.pi)|^N = |t|^N/(2*Real.pi)^N := by rw [hξabs, div_pow]
      have heq : C₁ / |t/(2*Real.pi)|^N = C₁ * (2*Real.pi)^N / |t|^N := by
        rw [hξpow, div_div_eq_mul_div]
      have hpow2 : (1+|t|)^N ≤ (2:ℝ)^N * |t|^N := by
        have h2 : (1 + |t|)^N ≤ (2*|t|)^N :=
          pow_le_pow_left₀ (by positivity) (by nlinarith [ht'.le]) N
        rwa [mul_pow] at h2
      have hkey : 1 / |t|^N ≤ (2:ℝ)^N * (1+|t|)^(-(N:ℝ)) := by
        rw [hrpow, ← div_eq_mul_inv]
        rw [div_le_div_iff₀ (pow_pos habs N) (pow_pos (by positivity) N)]
        simpa using hpow2
      calc ‖∫ u, f u * Complex.exp (-(Complex.I * (t:ℂ) * (u:ℂ)))‖
          = ‖𝓕 f (t/(2*Real.pi))‖ := by rw [angular_eq_fourier]
        _ ≤ C₁ / |t/(2*Real.pi)|^N := hdec
        _ = C₁ * (2*Real.pi)^N / |t|^N := heq
        _ = (C₁ * (2*Real.pi)^N) * (1/|t|^N) := by ring
        _ ≤ (C₁ * (2*Real.pi)^N) * ((2:ℝ)^N * (1+|t|)^(-(N:ℝ))) :=
              mul_le_mul_of_nonneg_left hkey (mul_nonneg hC₁ (pow_nonneg (by positivity) N))
        _ = (C₁*(2*Real.pi)^N*(2:ℝ)^N) * (1+|t|)^(-(N:ℝ)) := by ring
        _ ≤ max (B*(2:ℝ)^N) (C₁*(2*Real.pi)^N*(2:ℝ)^N) * (1+|t|)^(-(N:ℝ)) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)

theorem scaled_bump_fourier_decay (ψ : ℝ → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ τ : ℝ,
      ‖∫ u : ℝ, (ψ (u / h) / (h : ℂ)) * Complex.exp (-(Complex.I * (τ : ℂ) * (u : ℂ)))‖
        ≤ C * (1 + h * |τ|) ^ (-(N : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := angular_fourier_decay ψ hψ hψc N
  refine ⟨C, hC, ?_⟩
  intro h hh τ
  rw [integral_comp_div_mul_exp ψ hh τ]
  have hmain := hbound (τ * h)
  have habs : |τ * h| = h * |τ| := by rw [abs_mul, abs_of_pos hh, mul_comm]
  rw [habs] at hmain
  exact hmain

end Commons.Analysis.Fourier