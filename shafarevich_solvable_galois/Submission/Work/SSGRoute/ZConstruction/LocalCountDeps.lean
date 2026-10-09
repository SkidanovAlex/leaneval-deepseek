/-
# Dependency bundle for the local counts of the level-`K` parity

This module only re-exports, for the lemmas about the `p`-power quotient `κˣ ⧸ (κˣ)^p` of the
completion `κ = K_𝔭` of a number field at a finite prime:

* the vocabulary of the local inputs (`NK.LocalInputs.Defs`: `localDegree`, `zetaIndicator`,
  `principalUnits`, `LocalFieldInputs`),
* the Kummer group `NK.LocalAnabelian.KummerGroup`,
* the group-theoretic multiplicativity of the `p`-power quotient
  (`Commons.NumberTheory.NumberField.Completion.natCard_quot_powMonoidHom_eq_mul`) and the count of
  the `n`-power quotient of a cyclic group,
* the description of the absolute local degree as `e · f`
  (`NK.LocalInputs.localDegree_eq_ramificationIdx_mul_inertiaDeg`).
-/
import Mathlib
import Submission.NK.LocalInputs.Defs
import Submission.NK.LocalAnabelian.Kummer.Defs
import Submission.NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg
import Submission.NK.LocalInputs.PowerQuotient.natCard_KummerGroup_eq_pow_of_principalUnits
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_powerQuotient_adicCompletion_rat_units
import Submission.Commons.GroupTheory.SpecificGroups.Cyclic.card_quotient_powMonoidHom
import Submission.Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
