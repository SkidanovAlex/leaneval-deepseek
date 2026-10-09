import Submission.Commons.GroupTheory.Subgroup.card_inf_eq_gcd_of_isCyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.GroupTheory.SpecificGroups.Cyclic

/-- In a finite cyclic group, a subgroup is determined by its cardinality: if `A` and `B` have
the same number of elements then `A = B`.

Indeed, in a finite cyclic group an element `x` lies in a subgroup `H` exactly when
`x ^ Nat.card H = 1` (`Commons.GroupTheory.Subgroup.mem_iff_pow_card_eq_one`), so the
membership predicate of `H` is determined by `Nat.card H`. -/
theorem subgroup_eq_of_card_eq {C : Type*} [Group C] [Finite C] [IsCyclic C]
    (A B : Subgroup C) (h : Nat.card A = Nat.card B) : A = B := by
  ext x
  rw [Commons.GroupTheory.Subgroup.mem_iff_pow_card_eq_one A x,
    Commons.GroupTheory.Subgroup.mem_iff_pow_card_eq_one B x, h]

end Commons.GroupTheory.SpecificGroups.Cyclic
