import Mathlib
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.Work.CFTLib.Final
import Submission.Work.CFTLib.martinet_of_cftlib

open NumberField

namespace Submission

/-- **Martinet's asymptotically-good totally real towers.**

From the class-field-theory library (`Submission/NK/**`, `Submission/Work/CFTLib/Final.lean`):
Shafarevich's bound `CFTLib.ShafBound` and the maximality/class-group condition
`CFTLib.MaximalClassCond` feed `Work.CFTLib.martinet_of_cftlib`, which runs the unramified pro-`2`
tower over `gsF` (Golod--Shafarevich). -/
theorem exists_totallyReal_discr_le :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d :=
  Work.CFTLib.martinet_of_cftlib Work.CFTLib.shafBound_proved Work.CFTLib.maximalClassCond_proved

end Submission
