/-
Import hub for the `inertiaField_finrank` lane.

This module only re-exports the (Mathlib + `Submission.Commons` + `Work.Sha2Lib`) modules that the
lemmas requested for `Submission/Work/SSGRoute/TatePoitouRoute/FinitenessHM/inertiaField_finrank.lean`
need, so that they can be named in `depends_on` (which is interpreted relative to `Submission/Work/`).
-/
import Submission.Commons.NumberTheory.NumberField.Completion.exists_isPrimitiveRoot_lift_adicCompletionB
import Submission.Commons.NumberTheory.NumberField.Completion.exists_ringEquiv_adicCompletion_of_residue_ringEquiv
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.card_residueField_adicCompletionIntegers_eq_pow_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.liesOver_maximalIdeal_adicCompletionIntegers
import Submission.Work.Sha2Lib.inertiaDeg_cyclotomic_level
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
