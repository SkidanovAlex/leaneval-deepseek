import Mathlib
import Submission.Work.Maximal.band_schwartz_fourier_bump
import Submission.Work.Maximal.fourierInv_eq_tsum_sampling
import Submission.Work.Maximal.Decimated.sampling_identity_integrable

/-!
# Lattice sampling/reproduction for continuous integrable band-limited functions

If `H : ℝ → ℂ` is continuous and integrable and its Fourier transform vanishes outside
`[-1/4, 1/4]`, and `ψ` is a Schwartz window whose Fourier transform equals `1` on `[-1/4, 1/4]`
and vanishes off `[-1/2, 1/2]`, then `H` is reproduced from its integer samples:

`H y = ∑' j : ℤ, ψ (y - j) * H j`  for every `y : ℝ`.

The proof feeds the amplitude `W = 𝓕 H` (integrable, supported in `[-1/4, 1/4]`) to the
sampling identity for integrable band-limited amplitudes
(`Work.Maximal.Decimated.sampling_identity_integrable`), and then replaces the band-limited
function `𝓕⁻ W` by `H` using Fourier inversion at every point.
-/

namespace Work.BourgainPlan.Maximal

theorem lat_sampling_reproduce {H : ℝ → ℂ} (hHc : Continuous H)
    (hH1 : MeasureTheory.Integrable H)
    (hband : ∀ ξ : ℝ, 1 / 4 < |ξ| → FourierTransform.fourier H ξ = 0)
    {ψ : SchwartzMap ℝ ℂ}
    (hψ1 : ∀ ξ ∈ Set.Icc (-(1 / 4) : ℝ) (1 / 4), FourierTransform.fourier (⇑ψ) ξ = 1)
    (hψ0 : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → FourierTransform.fourier (⇑ψ) ξ = 0) :
    ∀ y : ℝ, H y = ∑' j : ℤ, ψ (y - (j : ℝ)) * H (j : ℝ) := by
  -- On the complement of `[-1/4, 1/4]` the modulus exceeds `1/4`.
  have hstrict : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / 4) : ℝ) (1 / 4) → (1 / 4 : ℝ) < |ξ| := by
    intro ξ hξ
    by_contra hcon
    exact hξ (by rw [Set.mem_Icc]; exact abs_le.mp (le_of_not_gt hcon))
  have hWsupp : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / 4) : ℝ) (1 / 4) →
      FourierTransform.fourier H ξ = 0 :=
    fun ξ hξ => hband ξ (hstrict ξ hξ)
  -- The Fourier transform of `H` is continuous with compact support, hence integrable.
  have hHf_cont : Continuous (FourierTransform.fourier H) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hH1
  have hHf_supp : Function.support (FourierTransform.fourier H) ⊆
      Set.Icc (-(1 / 4) : ℝ) (1 / 4) := by
    intro ξ hξ
    by_contra h
    exact hξ (hWsupp ξ h)
  have hWint : MeasureTheory.Integrable (FourierTransform.fourier H) :=
    hHf_cont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hHf_supp)
  -- Fourier inversion identifies `𝓕⁻ (𝓕 H)` with `H` everywhere (`H` is continuous).
  have hinv : ∀ x : ℝ,
      FourierTransformInv.fourierInv (FourierTransform.fourier H) x = H x :=
    fun x => hH1.fourierInv_fourier_eq hWint (hHc.continuousAt)
  intro y
  calc H y = FourierTransformInv.fourierInv (FourierTransform.fourier H) y := (hinv y).symm
    _ = ∑' m : ℤ, (ψ : ℝ → ℂ) (y - (m : ℝ)) *
          FourierTransformInv.fourierInv (FourierTransform.fourier H) ((m : ℤ) : ℝ) :=
        Work.Maximal.Decimated.sampling_identity_integrable (c0 := 1 / 4)
          (by norm_num) (by norm_num) ψ hψ1 hψ0 (FourierTransform.fourier H) hWint hWsupp y
    _ = ∑' j : ℤ, ψ (y - (j : ℝ)) * H (j : ℝ) := by
        apply tsum_congr
        intro m
        rw [hinv]

end Work.BourgainPlan.Maximal
