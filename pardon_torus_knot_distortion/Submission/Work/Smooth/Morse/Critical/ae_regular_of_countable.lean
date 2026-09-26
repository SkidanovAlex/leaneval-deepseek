import Mathlib
import Submission.Work.Smooth.Morse.Defs

namespace Work.Smooth.Morse.Critical

/-- The Sard input, reduced to the countability of the critical values: the set of non-regular
values of `g|_F` is exactly `criticalValues ψ g`, and a countable subset of `ℝ` has measure zero
for Lebesgue measure (every singleton has measure zero and a countable union of null sets is
null). -/
theorem ae_regular_of_countable (ψ : Submission.Diffeo) (g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ) (h : (Work.Smooth.Morse.criticalValues ψ g).Countable) : Work.Smooth.Morse.AERegularValues ψ g := by
  simpa [Work.Smooth.Morse.AERegularValues, Work.Smooth.Morse.IsRegularValue] using
    h.ae_notMem (MeasureTheory.volume : MeasureTheory.Measure ℝ)

end Work.Smooth.Morse.Critical
