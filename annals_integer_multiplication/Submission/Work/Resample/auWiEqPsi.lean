import Mathlib
import Submission.Work.Resample.auRowDefs

namespace Work.Resample

/-- `auWi` is `auPsi` evaluated at the un-wrapped window index `auK s t k + i - auM p α`.

Both sides are `(1/2α)·e^{−π·(t·n − s·k)²/(α²t²)}` with `n = auK s t k + i - auM p α`, since
`n - s·k/t = (t·n − s·k)/t`. -/
theorem auWiEqPsi (p α s t k i : ℕ) (ht : 0 < t) :
    Work.Resample.auWi p α s t k i = Work.Resample.auPsi α s t k ((Work.Resample.auK s t k : ℤ) + (i : ℤ) - (Work.Resample.auM p α : ℤ)) := by
  have ht' : (↑t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  unfold auWi auPsi auNsq auN
  push_cast
  congr 2
  by_cases hα : (α : ℝ) = 0
  · simp [hα]
  · have hX : (↑t * (↑(auK s t k) + ↑i - ↑(auM p α)) - ↑s * ↑k : ℝ)
        = ((↑(auK s t k) + ↑i - ↑(auM p α)) - ↑s * ↑k / ↑t) * ↑t := by
      field_simp
    rw [hX]
    field_simp

end Work.Resample
