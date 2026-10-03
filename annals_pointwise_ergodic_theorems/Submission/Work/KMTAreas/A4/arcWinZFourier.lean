/-
# The `ℤ`-Fourier transform of the arc window `arcWin ψ N s`

For a Schwartz window profile `ψ` whose Fourier transform is the tiling bump `arcChi`, the
`ℤ`-Fourier transform of the window kernel

`arcWin ψ N s m = N⁻¹ ψ(m/N) e(m s)`

at the real frequency `t` is the periodisation of the bump:

`𝓕_ℤ (arcWin ψ N s)(t) = ∑_n arcChi (N (t - s + n))`.

This is Poisson summation (`Work.KMTAreas.A4.lipPoissonMultiplier`) for the dilated, modulated
profile `x ↦ e^{-2πi(t-s)x} N⁻¹ ψ(N⁻¹ x)`: the character product
`e(m s) e(-m t) = e(-m (t - s))` collapses the two exponentials, and the hypothesis
`𝓕ψ = arcChi` identifies the right-hand side with the periodised bump.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lip2ArcDefs
import Submission.Work.KMTAreas.A4.winZFourier

set_option maxHeartbeats 1000000

open scoped BigOperators FourierTransform
open MeasureTheory

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

theorem arcWinZFourier (ψ : Work.Analysis.InverseTheory.SchwartzR) (hψ : ∀ u : ℝ, Work.KMTAreas.A4.schFT ψ u = Work.KMTAreas.A4.arcChi u) (N : ℕ) (hN : 1 ≤ N) (s t : ℝ) : Work.Analysis.InverseTheory.ZFourier (Work.KMTAreas.A4.arcWin ψ N s) ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) = ∑' n : ℤ, Work.KMTAreas.A4.arcChi ((N : ℝ) * (t - s + (n : ℝ))) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hinv : 0 < ((N : ℝ))⁻¹ := inv_pos.mpr hNpos
  -- Poisson summation for the dilated, modulated profile, with `ε = N⁻¹`, `θ = t - s`
  have hpoisson : ((N : ℂ))⁻¹ *
      (∑' u : ℤ, (ψ (((N : ℝ))⁻¹ * (u : ℝ)) : ℂ) *
        (fourier (-u) (((t - s) : ℝ) : FreqCircle) : ℂ))
      = ∑' n : ℤ, arcChi (((N : ℝ)) * (t - s + (n : ℝ))) := by
    have h := lipPoissonMultiplier ψ hinv (t - s)
    have hcast : ((((N : ℝ))⁻¹ : ℝ) : ℂ) = ((N : ℂ))⁻¹ := by
      rw [Complex.ofReal_inv, Complex.ofReal_natCast]
    rw [hcast] at h
    rw [h]
    refine tsum_congr fun n => ?_
    rw [hψ]
    congr 1
    rw [div_inv_eq_mul]
    ring
  rw [ZFourier, ← hpoisson, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  simp only [arcWin]
  rw [show (m : ℝ) / ((N : ℝ)) = ((N : ℝ))⁻¹ * (m : ℝ) from div_eq_inv_mul _ _]
  rw [← fourier_mul_fourier_neg s t m]
  ring

end Work.KMTAreas.A4
