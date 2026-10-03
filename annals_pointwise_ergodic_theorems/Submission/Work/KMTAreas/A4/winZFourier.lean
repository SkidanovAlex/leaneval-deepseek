/-
# The `ℤ`-Fourier transform of the reproducing window `win M s`

This module computes the `ℤ`-Fourier transform of the normalized reproducing window
`win M γ m = (1/M) ψ(m/M) e(m γ)` (`ψ = lipSchPsi`, the inverse Fourier transform of the bump
`lipSchChi`): for the real representative `s` of the frequency and a real frequency `t`,

  `𝓕_ℤ (win M s) (t) = winFT M s t = ∑_n χ (M (t - s + n))`,

the periodisation of the Fourier transform `χ = 𝓕ψ` of the window profile.  Equivalently, the
`ℤ`-Fourier transform of the window is the dilation by `1/M` of the profile of the smoothing
weight, sampled at the frequencies `t - s + n` — the statement that `win` is a reproducing kernel
on arcs of radius `1/(2M)`.

The proof is Poisson summation in the form `lipPoissonMultiplier` (applied to `ψ = lipSchPsi`, the
dilation `ε = 1/M` and the modulation `θ = t - s`): the left-hand side of that identity is exactly
the series defining `ZFourier (win M s) (t)`, since the character product
`e(m s) e(-m t) = e(-m (t - s))` collapses the two exponentials, and the right-hand side is
`∑_n 𝓕ψ (M (t - s + n)) = ∑_n χ (M (t - s + n)) = winFT M s t`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lip2Defs

set_option maxHeartbeats 800000

open scoped BigOperators FourierTransform
open MeasureTheory

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- The character `fourier n` at the class of the real frequency `x` is `𝐞 (x * n)`. -/
theorem fourier_coe_real_mul (n : ℤ) (x : ℝ) :
    (fourier n ((x : ℝ) : FreqCircle) : ℂ) = (𝐞 (x * (n : ℝ)) : ℂ) := by
  have h := lipFourierNegCoe (-n) x
  simpa using h

/-- The character pairing of the window profile: `e(m s) e(-m t) = e(-m (t - s))`. -/
theorem fourier_mul_fourier_neg (s t : ℝ) (m : ℤ) :
    (fourier m ((s : ℝ) : FreqCircle) : ℂ) * (fourier (-m) ((t : ℝ) : FreqCircle) : ℂ)
      = (fourier (-m) (((t - s) : ℝ) : FreqCircle) : ℂ) := by
  rw [fourier_coe_real_mul m s, fourier_coe_real_mul (-m) t,
    fourier_coe_real_mul (-m) (t - s), ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  congr 1
  congr 1
  push_cast
  ring

/-- **The Fourier transform of the reproducing window.**  For `M > 0`, real `s` and real `t`,

`𝓕_ℤ (win M s) (t) = winFT M s t`.

This is the Poisson-summation identity `lipPoissonMultiplier` for the dilated, modulated window
profile, with the character product `e(m s) e(-m t) = e(-m (t - s))` performed first. -/
theorem winZFourier (M s t : ℝ) (hM : 0 < M) :
    Work.Analysis.InverseTheory.ZFourier (Work.KMTAreas.A4.win M ((s : ℝ) : Work.Analysis.InverseTheory.FreqCircle))
      ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle)
    = Work.KMTAreas.A4.winFT M s t := by
  have hMinv : 0 < M⁻¹ := inv_pos.mpr hM
  -- Poisson summation for the dilated window profile `u ↦ ψ(u/M)`, modulated by `t - s`
  have hpoisson : (M : ℂ)⁻¹ * (∑' u : ℤ, lipSchPsi (M⁻¹ * (u : ℝ)) *
      (fourier (-u) (((t - s) : ℝ) : FreqCircle) : ℂ)) = winFT M s t := by
    rw [← Complex.ofReal_inv]
    rw [lipPoissonMultiplier lipSchPsi hMinv (t - s)]
    rw [winFT]
    refine tsum_congr fun n => ?_
    rw [schFT, lipSchPsi_fourier]
    congr 1
    rw [div_inv_eq_mul]
    ring
  rw [ZFourier, ← hpoisson, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  simp only [win]
  rw [show (m : ℝ) / M = M⁻¹ * (m : ℝ) from div_eq_inv_mul _ _]
  rw [← fourier_mul_fourier_neg s t m]
  ring

end Work.KMTAreas.A4
