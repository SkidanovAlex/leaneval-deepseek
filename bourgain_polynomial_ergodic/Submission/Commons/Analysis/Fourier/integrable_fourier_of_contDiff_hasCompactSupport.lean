import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

open scoped FourierTransform SchwartzMap
open MeasureTheory

namespace Commons.Analysis.Fourier

/-- The Fourier transform of a smooth compactly supported function on `ℝ` is integrable:
a smooth compactly supported function is a Schwartz function, its Fourier transform is again
a Schwartz function, and every Schwartz function is integrable. -/
theorem integrable_fourier_of_contDiff_hasCompactSupport {f : ℝ → ℂ} (hf : HasCompactSupport f)
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) :
    MeasureTheory.Integrable (FourierTransform.fourier f) := by
  -- A smooth compactly supported function is a Schwartz function ...
  let g : 𝓢(ℝ, ℂ) := hf.toSchwartzMap hs
  have hgc : (g : ℝ → ℂ) = f := rfl
  -- ... and the underlying function of `g` is `f`.
  have h1 : MeasureTheory.Integrable ((𝓕 g : 𝓢(ℝ, ℂ)) : ℝ → ℂ) :=
    SchwartzMap.integrable (μ := volume) (𝓕 g)
  -- The Fourier transform of a Schwartz function, seen as a function, agrees with the
  -- Fourier transform of its underlying function.
  have h2 : MeasureTheory.Integrable (𝓕 (g : ℝ → ℂ)) := by
    simpa only [SchwartzMap.fourier_coe] using h1
  rw [hgc] at h2
  exact h2

end Commons.Analysis.Fourier