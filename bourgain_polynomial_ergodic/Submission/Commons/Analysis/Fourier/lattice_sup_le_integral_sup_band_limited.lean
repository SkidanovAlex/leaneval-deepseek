import Mathlib
import Submission.Commons.Analysis.Fourier.lattice_sup_le_integral_sup_band_limited_continuous

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped FourierTransform ENNReal
open VectorFourier

/-- Sup-sampling inequality for a family of continuous `(-1/2,1/2]`-band-limited functions: the
`ℓ²(ℤ)` norm of the lattice values of the pointwise supremum is controlled by the `L²(ℝ)` norm
of that supremum.  The `Continuous` hypothesis supplies the canonical representative whose
lattice values are well defined (the Fourier transform only sees the a.e. class). -/
theorem lattice_sup_le_integral_sup_band_limited (h : ℕ → ℝ → ℂ)
    (hcont : ∀ j : ℕ, Continuous (h j))
    (hint : ∀ j : ℕ, Integrable (h j))
    (hbl : ∀ (j : ℕ) (ξ : ℝ), ξ ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → (𝓕 (h j)) ξ = 0) :
    ∃ C : ℝ, 0 < C ∧
      ∫⁻ m : ℤ, (⨆ j : ℕ, ‖h j (m : ℝ)‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * ∫⁻ x : ℝ, (⨆ j : ℕ, ‖h j x‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.volume := by
  obtain ⟨C, hCpos, hC⟩ := lattice_sup_le_integral_sup_band_limited_continuous
  refine ⟨C, hCpos, ?_⟩
  simpa only [ofReal_norm] using hC h hint hcont hbl

end Commons.Analysis.Fourier
