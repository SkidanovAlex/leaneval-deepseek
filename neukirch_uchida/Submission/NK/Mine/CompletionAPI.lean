-- Re-exports of the completion/decomposition-group API of the `Submission.NeukirchUchida`
-- development and the commons, so that lemmas delegated into `Submission/Work/` can be stated
-- in its vocabulary (`adicCompletionAlgebra`, `placeOf`, the local Galois group of a completion).
import Submission.NeukirchUchida.Local.PlaceFromValuation
import Submission.NeukirchUchida.Local.Transitivity
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional
import Submission.NeukirchUchida.PlaceSystem

namespace NK.Mine

open scoped Pointwise in
/-- The **decomposition group** of a place `A` of `K'` over a number field `K`, as a subgroup of
the absolute Galois group: the stabiliser of `A` (equivalently `{g | A.comap g = A}`).

This is `Submission.NeukirchUchida.decompositionGroup` exposed with its field arguments explicit,
so that statements in `Submission/Work/` can mention it without opening the scoped `Pointwise`
instances for the action of `AlgEquiv` on `ValuationSubring`. -/
def decompositionGroupOf (K : Type*) [Field K] [NumberField K] (K' : Type*) [Field K']
    [Algebra K K'] (A : ValuationSubring K') : Subgroup Gal(K'/K) :=
  MulAction.stabilizer Gal(K'/K) A

end NK.Mine
