import Mathlib
import Submission.NK.Ramification.Defs
import Submission.NK.Ramification.Herbrand

namespace NK.Ramification

/-- **The lower indices are maximal at zero**: since the ramification filtration is decreasing
(`ramificationSubgroup_antitone`), the subgroup `G_i` is contained in `G_0` for every `i`, and
`Nat.card` is monotone under inclusion of subgroups of a finite group.  In particular the
Herbrand function has nonnegative increments. -/
theorem lowerIndex_le_zero {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [Finite ↥(A.decompositionSubgroup K)] (i : ℕ) :
    NK.Ramification.lowerIndex (K := K) A i ≤ NK.Ramification.lowerIndex (K := K) A 0 := by
  have hle : ramificationSubgroup (K := K) A i ≤ ramificationSubgroup (K := K) A 0 :=
    ramificationSubgroup_le_ramificationSubgroup A (Nat.zero_le i)
  rw [lowerIndex, lowerIndex]
  exact Subgroup.card_le_of_le hle

end NK.Ramification
