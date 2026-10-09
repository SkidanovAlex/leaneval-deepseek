import Mathlib
import Submission.Work.SSGRoute.local_tame_defs
import Submission.Work.SSGRoute.RamifiedPlacesAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The pointwise instances on `Ideal` made global

`Ideal.pointwiseDistribMulAction` and `Ideal.pointwiseMulSemiringAction` are registered as
instances only inside the `Pointwise` scope in Mathlib.  The statements of the level-index
lemmas mention `MulAction.stabilizer G P.asIdeal` for a prime ideal `P`, which needs these
instances; registering them here (for the modules of this directory) means such statements
elaborate without a local `open scoped Pointwise`.
-/

attribute [instance] Ideal.pointwiseDistribMulAction
attribute [instance] Ideal.pointwiseMulSemiringAction
