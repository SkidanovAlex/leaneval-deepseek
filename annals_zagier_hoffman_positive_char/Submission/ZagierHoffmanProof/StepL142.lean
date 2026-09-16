import Submission.ZagierHoffmanProof.StepL141
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L142: the iterate commutation `BCq ∘ BCqIter n = BCqIter n ∘ BCq`
(SESSION 259s)

The one-off type-level lemma that unlocks the (a3-A) definition of the b-side
descent (PLAN SESSION 259r): `BCqIter` peels inside-out
(`BCqIter (n+1) R = BCqIter n (BCq R)`, `rfl`), while `BCq` of the iterate is the
outside-in form; this commutation reconciles the two.
Proof: induction on `n` generalizing `R`; the succ case is two
`RelData.BCqIter_succ` rewrites (both `rfl`) followed by the induction
hypothesis at `R := BCq R`.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ `BCq` commutes with the iterate: `BCq (BCqIter n R) = BCqIter n (BCq R)`. -/
theorem BCq_BCqIter_commute (n : ℕ) (R : RelData F) :
    RelData.BCq F (RelData.BCqIter F n R) = RelData.BCqIter F n (RelData.BCq F R) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
      rw [RelData.BCqIter_succ, RelData.BCqIter_succ]
      exact ih (RelData.BCq F R)

end ZagierHoffmanPositiveChar
