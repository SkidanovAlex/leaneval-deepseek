import Mathlib
import Submission.Work.FIArea4.Vflip.sep_defs

open MeasureTheory
open scoped FourierTransform

namespace Work.FIArea4.Vflip

/-- Equality of the two exponential arguments appearing in the Mellin inversion formula. -/
private lemma sepG_exp_arg_eq (v η : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (v * Real.log η))
      = Complex.exp (((2 * Real.pi * inner ℝ v (Real.log η) : ℝ) : ℂ) * Complex.I) := by
  congr 1
  rw [Real.inner_apply]
  push_cast
  ring

/-- **Mellin inversion for a smooth compactly supported `ψ`.**

With `sepG ψ t = 𝓕 (fun u => ψ (Real.exp u)) t`, for every `η > 0`:
`ψ η = ∫ t, sepG ψ t * exp (2 π i t log η) dt`.

Suggested route: `f := fun u => (ψ (Real.exp u) : ℂ)` is `C^∞` with compact support, so `f` and
`𝓕 f` are integrable; `Continuous.fourierInv_fourier_eq` gives `𝓕⁻ (𝓕 f) = f`, and
`Real.fourierInv_eq'` writes `𝓕⁻ (𝓕 f) s = ∫ t, exp (2πi (t*s)) * 𝓕 f t`.  Evaluate at
`s = Real.log η` and rewrite `exp (2πi (t * log η))` as `exp (2 π i t log η)`. -/
theorem sepG_mellin {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hsupp : ∀ y : ℝ, (y ≤ 1 / 2 ∨ 5 / 2 ≤ y) → ψ y = 0) :
    ∀ η : ℝ, 0 < η → (ψ η : ℂ) =
      ∫ t : ℝ, Work.FIArea4.Vflip.sepG ψ t *
        Complex.exp (2 * Real.pi * Complex.I * (t * Real.log η)) := by
  intro η hη
  -- Smoothness and compact support of `f := fun u => (ψ (exp u) : ℂ)`.
  have hfcd : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => (ψ (Real.exp u) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hψ.comp Real.contDiff_exp)
  have hfcs : HasCompactSupport (fun u : ℝ => (ψ (Real.exp u) : ℂ)) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (Real.log (1 / 2)) (Real.log (5 / 2))) isCompact_Icc ?_
    rw [Function.support_subset_iff]
    intro u hu
    have hψne : ψ (Real.exp u) ≠ 0 := by
      simpa using hu
    have h1 : 1 / 2 < Real.exp u := by
      by_contra hc
      exact hψne (hsupp _ (Or.inl (le_of_not_gt hc)))
    have h2 : Real.exp u < 5 / 2 := by
      by_contra hc
      exact hψne (hsupp _ (Or.inr (le_of_not_gt hc)))
    rw [Set.mem_Icc]
    exact ⟨le_of_lt ((Real.log_lt_iff_lt_exp (by norm_num)).mpr h1),
      le_of_lt ((Real.lt_log_iff_exp_lt (by norm_num)).mpr h2)⟩
  -- Integrability of `f` and of `𝓕 f`.
  have hAint : Integrable (fun u : ℝ => (ψ (Real.exp u) : ℂ)) := by
    have h := (hfcs.toSchwartzMap hfcd).integrable (μ := volume)
    have hcoe : (((hfcs.toSchwartzMap hfcd) : SchwartzMap ℝ ℂ) : ℝ → ℂ)
        = (fun u : ℝ => (ψ (Real.exp u) : ℂ)) := rfl
    rw [hcoe] at h
    exact h
  have hFA : Integrable (𝓕 (fun u : ℝ => (ψ (Real.exp u) : ℂ))) := by
    have h := (𝓕 (hfcs.toSchwartzMap hfcd)).integrable (μ := volume)
    rw [SchwartzMap.fourier_coe] at h
    have hcoe : (((hfcs.toSchwartzMap hfcd) : SchwartzMap ℝ ℂ) : ℝ → ℂ)
        = (fun u : ℝ => (ψ (Real.exp u) : ℂ)) := rfl
    rw [hcoe] at h
    exact h
  -- Fourier inversion.
  have hinv : 𝓕⁻ (𝓕 (fun u : ℝ => (ψ (Real.exp u) : ℂ)))
      = (fun u : ℝ => (ψ (Real.exp u) : ℂ)) :=
    Continuous.fourierInv_fourier_eq hfcd.continuous hAint hFA
  -- Rewrite the integral as `𝓕⁻ (𝓕 f) (log η)`.
  have key : (∫ t : ℝ, Work.FIArea4.Vflip.sepG ψ t *
        Complex.exp (2 * Real.pi * Complex.I * (t * Real.log η)))
      = 𝓕⁻ (𝓕 (fun u : ℝ => (ψ (Real.exp u) : ℂ))) (Real.log η) := by
    rw [Real.fourierInv_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul, sepG]
    rw [sepG_exp_arg_eq v η]
    ring
  rw [key, congr_fun hinv (Real.log η), Real.exp_log hη]

end Work.FIArea4.Vflip
