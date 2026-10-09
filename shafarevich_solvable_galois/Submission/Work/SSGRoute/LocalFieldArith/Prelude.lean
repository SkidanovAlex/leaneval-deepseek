import Mathlib
import Submission.Work.Kummer.Defs
import Submission.NK.LocalInputs.PowerQuotient.Setup
import Submission.Commons.NumberTheory.NumberField.Completion.finiteIndex_principalUnits_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.exists_units_mul_uniformizer_zpow_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_powerQuotient_adicCompletion_rat_units
import Submission.Commons.NumberTheory.NumberField.charZero_adicCompletion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Shared imports for the local-field arithmetic of `𝒪_κˣ ⧸ (𝒪_κˣ)^p` in
`Work.SSGRoute.LocalFieldArith`.  This module contains no mathematics of its own; it exists so that
the lemmas of this directory can be stated over the `LogData`/`pu` vocabulary of
`NK.LocalInputs.PowerQuotient.Setup` and the group-theoretic API of the commons.
-/
