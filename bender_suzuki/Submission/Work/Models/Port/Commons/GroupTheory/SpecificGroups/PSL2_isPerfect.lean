import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.Commutator.commutatorSet_PSL2_eq_univ

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.SpecificGroups

/-- **Purity of `PSL(2,F)`**: for a finite field `F` with at least `4` elements, the projective
special linear group `PSL(2,F)` equals its own commutator subgroup.

Indeed `commutator G = closure (commutatorSet G)`, and Ore's theorem for `PSL(2,F)`
(`commutatorSet_PSL2_eq_univ`) says that every element of `PSL(2,F)` is a commutator, so the
commutator set is all of `PSL(2,F)`. -/
theorem PSL2_isPerfect {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : 4 ≤ Nat.card F) : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  rw [Group.isPerfect_def, commutator_eq_closure,
    Commons.GroupTheory.Commutator.commutatorSet_PSL2_eq_univ (F := F) (by
      simpa [Nat.card_eq_fintype_card] using hF)]
  exact Subgroup.closure_univ

end Commons.GroupTheory.SpecificGroups
