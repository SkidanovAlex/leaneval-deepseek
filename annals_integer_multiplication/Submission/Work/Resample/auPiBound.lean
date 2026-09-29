import Mathlib
import Submission.Work.Resample.auDefs
import Submission.Work.Fx.piIter
import Submission.Work.Fx.piDvalBound
import Submission.Work.Fx.piTwoSubAseq
import Submission.Work.Fx.piAseqSqrtBound
import Submission.Work.Fx.piUBound
import Submission.Work.Fx.piDefs

namespace Work.Resample

/-- `auPi p = uval (auPrec p)` is the fixed-point value `2^(auPrec p)·π` to within `1`.

This is the final bound of the fixed-point evaluation of `π` (`Work.Fx.piUBound`) applied at the
working precision `auPrec p = 3p + 100 ≥ 100` of the resampling word, with the uniform error
estimate `Work.Fx.piIter` of the nested-square-root iteration supplying the hypothesis. -/
theorem auPiBound (p : ℕ) (hp : 100 ≤ p) :
    |(auPi p : ℝ) - (2 : ℝ) ^ (auPrec p) * Real.pi| ≤ 1 := by
  have herr := (Work.Fx.piIter (auPrec p)).1 (auPrec p)
  have h := Work.Fx.piUBound (auPrec p) (by simp only [auPrec]; omega) herr
  simpa [auPi] using h

end Work.Resample
