/-
# Import hub for the delegated completion-trace lemmas

This file only re-exports the `Mathlib`/`Commons` machinery and this lane's own local definitions
(`adicLocExp`, `adicExp`) needed by the lemmas delegated from
`FinitenessHM/count_le_adicLocExp.lean`.  It exists so that `depends_on` of the delegation tooling
(which resolves paths relative to `Submission/Work/`) can pull in the `Commons` imports.

No mathematics lives here.
-/
import Mathlib
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.adicCompletionExp
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.ValExp
import Submission.Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension
import Submission.Commons.NumberTheory.NumberField.Completion.module_free_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.exists_algEquiv_tensor_adicCompletion_prod
import Submission.Commons.NumberTheory.NumberField.Completion.exists_ringEquiv_tensor_adicCompletion_prod
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
