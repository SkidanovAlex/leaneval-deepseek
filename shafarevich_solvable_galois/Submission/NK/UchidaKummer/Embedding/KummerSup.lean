import Mathlib.Order.CompletePartialOrder
import Mathlib.NumberTheory.NumberField.Basic
import Submission.NK.UchidaKummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.UchidaKummer.Embedding

open scoped Classical

/-- The compositum, over the primes of `T`, of the Kummer fields `L(b_P^{1/ℓ})` inside `K'`. -/
noncomputable def kummerSup {L K' : Type*} [Field L] [NumberField L] [Field K'] [Algebra L K']
    (ℓ : ℕ) (T : Finset (NK.Chebotarev.PrimeIdeal L)) (b : NK.Chebotarev.PrimeIdeal L → Lˣ) :
    IntermediateField L K' :=
  T.sup (fun P => NK.LocalAnabelian.kummerField (K' := K') ℓ (b P))

end NK.UchidaKummer.Embedding
