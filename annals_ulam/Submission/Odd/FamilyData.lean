import Mathlib
import Submission.Odd.Statement
import Submission.Odd.FreeFamilyData

/-!
# Odd-dimensional floating body: the family data

This is the odd-dimensional half of Ryabogin's construction, now phrased through the named
proposition `Submission.Odd.OddFamilyData` and derived from the free-tip chord curve delivered by
the chapter `Work.OddCurve.Free` (the paper's Steps 2 and 3): see
`Submission.Odd.odd_floating_family_data_free` in `Submission/Odd/FreeFamilyData.lean`.
-/

namespace Submission.Odd

open MeasureTheory
open scoped BigOperators ContDiff Pointwise RealInnerProductSpace

set_option autoImplicit false

variable {d : ℕ}

lemma odd_floating_family_data (hd : 3 ≤ d) (hdodd : Odd d) :
    letI : NeZero d := ⟨by omega⟩
    OddFamilyData d := by
  letI : NeZero d := ⟨by omega⟩
  exact odd_floating_family_data_free hd hdodd

end Submission.Odd
