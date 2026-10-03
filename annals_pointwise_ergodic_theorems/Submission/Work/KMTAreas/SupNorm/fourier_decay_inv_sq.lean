import Mathlib

namespace Work.KMTAreas.SupNorm

open MeasureTheory

/-- Pointwise decay of the Fourier transform of a `C²` compactly supported function on `ℝ`:
taking the (distributional) second derivative of `x ↦ 𝐞(-x w) h x` gives the identity
`𝓕 (h'') w = (2πiw)² · 𝓕 h w`, hence `w² ‖𝓕 h w‖ ≤ ∫ ‖h''‖`, and the latter is bounded
by the sum of the `L¹` norms of `h`, `h'`, `h''`. -/
theorem fourier_decay_inv_sq (h : ℝ → ℂ) (hh : ContDiff ℝ 2 h) (hs : HasCompactSupport h) (w : ℝ) :
    (w ^ 2) * ‖FourierTransform.fourier h w‖
      ≤ 4 * ((∫ x, ‖h x‖) + (∫ x, ‖deriv h x‖) + (∫ x, ‖iteratedDeriv 2 h x‖)) := by
  -- Integrability of the first two derivatives, from compact support and smoothness.
  have hInt : ∀ n : ℕ, ↑n ≤ (2 : ℕ∞) → Integrable (iteratedDeriv n h) := by
    have hd1 : ContDiff ℝ 1 (deriv h) := hh.deriv'
    have hd2 : ContDiff ℝ 0 (deriv (deriv h)) := hd1.deriv'
    intro n hn
    have hn2 : n ≤ 2 := by exact_mod_cast hn
    interval_cases n
    · simpa using hh.continuous.integrable_of_hasCompactSupport hs
    · rw [iteratedDeriv_one]
      exact hd1.continuous.integrable_of_hasCompactSupport hs.deriv
    · rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
      exact hd2.continuous.integrable_of_hasCompactSupport hs.deriv.deriv
  -- The Fourier transform of the second derivative, `𝓕 (h'') w = (2πiw)² • 𝓕 h w`.
  have hkey : FourierTransform.fourier (iteratedDeriv 2 h)
      = fun x : ℝ => ((2 * ↑Real.pi * Complex.I * (x:ℂ))^2) • FourierTransform.fourier h x :=
    Real.fourier_iteratedDeriv (N := (2:ℕ∞)) hh hInt le_rfl
  -- Taking norms: `‖𝓕 (h'') w‖ = (2πw)² ‖𝓕 h w‖`.
  have hnorm : ‖FourierTransform.fourier (iteratedDeriv 2 h) w‖
      = (2 * Real.pi * w)^2 * ‖FourierTransform.fourier h w‖ := by
    rw [congrFun hkey w, norm_smul]
    have hc : (2 * ↑Real.pi * Complex.I * (w:ℂ))^2 = -(((2*Real.pi*w)^2 : ℝ) : ℂ) := by
      have hh2 : (2 * ↑Real.pi * Complex.I * (w:ℂ))^2
          = (2*↑Real.pi*↑w)^2 * (Complex.I * Complex.I) := by ring
      rw [hh2, Complex.I_mul_I]
      push_cast
      ring
    congr 1
    rw [hc, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  -- The uniform bound `‖𝓕 g w‖ ≤ ∫ ‖g‖` for the `L¹` function `g = h''`.
  have hbound : ‖FourierTransform.fourier (iteratedDeriv 2 h) w‖
      ≤ ∫ x, ‖iteratedDeriv 2 h x‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume (innerₗ ℝ)
      (iteratedDeriv 2 h) w
  have hpi : (1:ℝ) ≤ (2 * Real.pi)^2 := by nlinarith [Real.pi_gt_three]
  have hA : (0:ℝ) ≤ ∫ x, ‖h x‖ := integral_nonneg fun x => norm_nonneg _
  have hB : (0:ℝ) ≤ ∫ x, ‖deriv h x‖ := integral_nonneg fun x => norm_nonneg _
  have hC : (0:ℝ) ≤ ∫ x, ‖iteratedDeriv 2 h x‖ := integral_nonneg fun x => norm_nonneg _
  calc (w ^ 2) * ‖FourierTransform.fourier h w‖
      ≤ ((2 * Real.pi)^2 * w^2) * ‖FourierTransform.fourier h w‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa using mul_le_mul_of_nonneg_right hpi (sq_nonneg w)
    _ = (2 * Real.pi * w)^2 * ‖FourierTransform.fourier h w‖ := by ring
    _ = ‖FourierTransform.fourier (iteratedDeriv 2 h) w‖ := hnorm.symm
    _ ≤ ∫ x, ‖iteratedDeriv 2 h x‖ := hbound
    _ ≤ 4 * ((∫ x, ‖h x‖) + (∫ x, ‖deriv h x‖) + (∫ x, ‖iteratedDeriv 2 h x‖)) := by
        linarith [hA, hB, hC]

end Work.KMTAreas.SupNorm
