import Submission.NK.Ramification.Herbrand
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Ramification

/-- **The lower index is `1` exactly for the trivial subgroup.** -/
theorem lowerIndex_eq_one_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [Finite ↥(A.decompositionSubgroup K)] (i : ℕ) :
    NK.Ramification.lowerIndex (K := K) A i = 1 ↔
      NK.Ramification.ramificationSubgroup (K := K) A i = ⊥ := by
  rw [lowerIndex, Subgroup.card_eq_one]

end NK.Ramification
