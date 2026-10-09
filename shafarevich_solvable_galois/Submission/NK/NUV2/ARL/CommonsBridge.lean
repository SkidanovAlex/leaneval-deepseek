import Submission.Commons.NumberTheory.NumberField.Completion.norm_range_of_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension
import Submission.Commons.RingTheory.Norm.residue_norm_eq
import Submission.Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! A bridge module gathering the (Galois-free parts of the) commons library on `q`-adic
completions that the local-norm unramified development needs. -/
