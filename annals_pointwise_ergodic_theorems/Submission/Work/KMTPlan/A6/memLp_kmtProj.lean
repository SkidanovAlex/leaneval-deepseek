import Mathlib
import Submission.Work.KMTPlan.A6.HHBasic
import Submission.Work.KMTAreas.A7.KmtProjCrude

namespace Work.KMTPlan.A6

/-- **`MemLp` of the Ionescu--Wainger projections `kmtProj ρ l k`.**

The projection is the convolution of `f` with the Fourier coefficients of the IW symbol
`∑_{α ∈ (ℚ/ℤ)_{≤l}} η((ξ-α)/2^k)`, whose kernel is exponentially (hence `ℓ¹`) decaying;
`Work.KMTAreas.A7.KmtProjCrude` records the resulting `ℓ^q` bound for every `1 < q`, and at
`q = 2` it converts an `ℓ²` input into an `ℓ²` output. -/
theorem memLp_kmtProj (ρ : ℝ) (l : ℕ) (k : ℤ) {f : ℤ → ℂ} (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count) :
    MeasureTheory.MemLp (Work.KMTContract.kmtProj ρ l k f) 2 MeasureTheory.Measure.count := by
  -- The `ℓ¹` norm of the convolution kernel dominates the operator norm on `ℓ²`.
  obtain ⟨C, _hCpos, hC⟩ :=
    Work.KMTAreas.A7.KmtProjCrude (ρ := ρ) l k (q := 2) (by norm_num)
  have hbound : MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ l k f) 2
        (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      ≤ (C : ENNReal) * MeasureTheory.eLpNorm f 2 (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
    simpa using hC f
  -- Every function on the countable set `ℤ` is strongly measurable.
  refine MeasureTheory.memLp_iff.mpr ?_
  -- Finiteness of the `ℓ²` seminorm follows from the bound and the hypothesis.
  exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.coe_lt_top hf.eLpNorm_lt_top)

end Work.KMTPlan.A6
