import Submission.Work.ORLyndon.CLDirect.cldDefs
import Submission.Work.ORLyndon.foxD_multiple_of_mem_normalClosure

/-!
# `presentAlg` of the Fox derivative of a conjugate of the relator

`Work.ORLyndon.CLDirect.presentAlg_foxD_conj`: the pushed-forward Fox derivative vector of
`f * r * f⁻¹` is `f̄ • (∂r/∂x)`.  It is a two-line corollary of the general conjugation step
`Work.ORLyndon.presentAlg_foxD_conj` in `foxD_multiple_of_mem_normalClosure.lean` (unit D1 of
`CASE2INPUT_LEAD.md`).
-/

set_option autoImplicit false

namespace Work.ORLyndon.CLDirect

open MonoidAlgebra

universe u v

variable {X : Type u} [DecidableEq X] {K : Type v} [Field K]

/-- For a conjugate `f r f⁻¹` of the relator, the pushed-forward Fox derivative is `f̄ (∂r/∂x)`. -/
theorem presentAlg_foxD_conj (r f : FreeGroup X) (x : X) :
    Work.ORLyndon.presentAlg K r (Work.ORLyndon.foxD (K := K) x (f * r * f⁻¹)) =
      MonoidAlgebra.of K _ (Work.ORLyndon.presentRho r f) * Work.ORLyndon.relatorVec K r x := by
  have hβ : Work.ORLyndon.presentAlg K r (Work.ORLyndon.foxD (K := K) x r) =
      1 * Work.ORLyndon.relatorVec K r x := by
    rw [one_mul, Work.ORLyndon.relatorVec_apply]
  have h := Work.ORLyndon.presentAlg_foxD_conj (K := K) r x f r 1 hβ
    (Work.ORLyndon.presentRho_relator r)
  rw [h, Work.ORLyndon.presentAlg_of, mul_one]

end Work.ORLyndon.CLDirect
