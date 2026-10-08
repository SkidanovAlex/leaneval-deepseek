import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.Commutator.commutatorSet_SL2_eq_univ
import Submission.Work.Models.Port.Commons.GroupTheory.Commutator.commutatorSet_eq_univ_of_surjective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Commutator

/-- **Ore for `PSL(2,F)`**: every element of `PSL(2,F)` is a commutator, for a finite field `F`
with at least `4` elements.

Indeed `PSL(2,F)` is by definition the quotient `SL(2,F) / Z(SL(2,F))` of `SL(2,F)` (see
`Matrix.ProjectiveSpecialLinearGroup`), and the property "every element is a commutator" passes to
quotients (`commutatorSet_eq_univ_of_surjective`); on `SL(2,F)` it is
`commutatorSet_SL2_eq_univ`. -/
theorem commutatorSet_PSL2_eq_univ {F : Type*} [Field F] [Fintype F] (hF : 4 ≤ Fintype.card F) :
    commutatorSet (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = Set.univ :=
  commutatorSet_eq_univ_of_surjective
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))
    (QuotientGroup.mk'_surjective _)
    (commutatorSet_SL2_eq_univ (F := F) hF)

end Commons.GroupTheory.Commutator
