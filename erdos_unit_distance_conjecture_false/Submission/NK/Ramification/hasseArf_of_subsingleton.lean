import Submission.NK.Ramification.Herbrand

namespace NK.Ramification

/-- **A satisfiability witness for `HasseArf`**: whenever the decomposition subgroup is trivial —
for instance for the trivial extension `L = K` — the ramification filtration is trivial, the only
possible lower break is `i = 0`, and `HasseArf` holds.  (Used in the audit: it exhibits an
inhabitant of the hypothesis class of `HasseArf` and a case in which the conclusion is true.) -/
theorem hasseArf_of_subsingleton {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [Subsingleton ↥(A.decompositionSubgroup K)]
    [Finite ↥(A.decompositionSubgroup K)] :
    NK.Ramification.HasseArf (K := K) A := by
  refine hasseArf_of_tame A ?_
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  exact Subsingleton.elim _ _

end NK.Ramification
