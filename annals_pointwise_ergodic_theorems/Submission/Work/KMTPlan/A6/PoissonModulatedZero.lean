import Mathlib
import Submission.Work.KMTAreas.A4.lipPoissonVanish

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped FourierTransform

/-- Reflection symmetry of the additive characters of `AddCircle T`:
`fourier (-n) (-x) = fourier n x`. -/
lemma fourier_neg_neg_coe {T : ℝ} (n : ℤ) (x : ℝ) :
    (fourier (-n)) (((-x : ℝ)) : AddCircle T) = (fourier n) ((x : ℝ) : AddCircle T) := by
  rw [fourier_coe_apply, fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- **Poisson summation with a compactly supported Fourier transform.**
If the Fourier transform of the Schwartz function `ψ` vanishes outside `[-1,1]` and the modulation
frequency `t` stays at distance `> 1/R` from every integer, then the Poisson-modulated lattice sum
`∑_n ψ(n/R) · e^{2πi n t}` vanishes: Poisson summation exhibits it as
`R · ∑_m ψ̂(R(t+m))` and every term of the latter is zero. -/
theorem PoissonModulatedZero (ψ : SchwartzMap ℝ ℂ) {R : ℝ} (hR : 0 < R)
    (hψ : ∀ ξ : ℝ, 1 < |ξ| → FourierTransform.fourier (ψ : ℝ → ℂ) ξ = 0) (t : ℝ)
    (ht : ∀ m : ℤ, 1 / R < |t + m|) :
    tsum (fun n : ℤ => (ψ : ℝ → ℂ) ((n : ℝ) / R) * fourier n (t : AddCircle (1 : ℝ))) = 0 := by
  have hε : (0 : ℝ) < 1 / R := by positivity
  -- transfer the vanishing hypothesis to the plain Fourier transform `schFT`
  have hη : ∀ s : ℝ, 1 < |s| → Work.KMTAreas.A4.schFT ψ s = 0 := by
    intro s hs
    rw [Work.KMTAreas.A4.schFT, SchwartzMap.fourier_coe]
    exact hψ s hs
  -- the separation hypothesis, in the form required by `lipPoissonVanish`
  have hθ : ∀ n : ℤ, (1 / R) < |-t - (n : ℝ)| := by
    intro n
    have h1 : -t - (n : ℝ) = -(t + (n : ℝ)) := by ring
    rw [h1, abs_neg]
    exact ht n
  -- Poisson summation, in the `lipPoissonVanish` form
  have hm := Work.KMTAreas.A4.lipPoissonVanish ψ hη hε hθ
  have hne : (((1 / R : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (one_div_ne_zero hR.ne')
  have hX := (mul_eq_zero.mp hm).resolve_left hne
  -- match the two forms of the summand
  have hcongr : (∑' (u : ℤ), (ψ : ℝ → ℂ) ((1 / R) * (u : ℝ)) *
        (fourier (-u)) (((-t : ℝ)) : AddCircle (1 : ℝ)))
      = (∑' (u : ℤ), (ψ : ℝ → ℂ) ((u : ℝ) / R) *
        fourier u (((t : ℝ)) : AddCircle (1 : ℝ))) := by
    refine tsum_congr fun u => ?_
    have h1 : (1 / R : ℝ) * (u : ℝ) = (u : ℝ) / R := by rw [div_eq_mul_inv]; ring
    have h2 : (fourier (-u)) (((-t : ℝ)) : AddCircle (1 : ℝ))
        = fourier u (((t : ℝ)) : AddCircle (1 : ℝ)) := fourier_neg_neg_coe u t
    rw [h1, h2]
  exact hcongr.symm.trans hX

end Work.KMTPlan.A6
