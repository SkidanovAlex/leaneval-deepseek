import Submission.NK.Ramification.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Ramification

/-- **Consistency check.**  If the decomposition subgroup is trivial (for instance for the trivial
extension `L = K`), every ramification subgroup is everything: there is nothing to act by. -/
theorem ramificationSubgroup_eq_top_of_subsingleton {K L : Type*} [Field K] [Field L]
    [Algebra K L] (A : ValuationSubring L) [Subsingleton ↥(A.decompositionSubgroup K)] (i : ℕ) :
    NK.Ramification.ramificationSubgroup (K := K) A i = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro σ
  rw [mem_ramificationSubgroup_iff]
  intro x
  rw [Subsingleton.elim σ 1, one_smul, sub_self]
  exact zero_mem _

end NK.Ramification
