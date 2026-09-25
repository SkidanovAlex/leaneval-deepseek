import Submission.NK.Ramification.Herbrand

namespace NK.Ramification

/-- **The lower index is `1` exactly for the trivial subgroup.** -/
theorem lowerIndex_eq_one_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [Finite ↥(A.decompositionSubgroup K)] (i : ℕ) :
    NK.Ramification.lowerIndex (K := K) A i = 1 ↔
      NK.Ramification.ramificationSubgroup (K := K) A i = ⊥ := by
  rw [lowerIndex, Subgroup.card_eq_one]

end NK.Ramification
