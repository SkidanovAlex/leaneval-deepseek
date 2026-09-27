import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.charValDefs

/-!
# The endpoint correction factor for the walk-count induction (`Work.EQ.walk_count`)

`wtRho a γ n m` is the "endpoint correction" attached to a walk of the fan walk that starts in
the state `n` and ends in the state `m`.  It is designed so that the weight of a word `l` with
`stAux l n = m` satisfies

`wtAux a l n ≤ γ ^ (l.count false) * wtRho a γ n m`,

which is proved by structural induction on `l` (`Work.EQ.walk_count`).  The induction is driven
by the two identities
* `wtRho a γ n m = (upW a n / γ) * wtRho a γ (n+1) m` for `n + 1 ≤ m` (an up-step `n → n+1`),
* `wtRho a γ (n+1) m = wtRho a γ n m * dnW a (n + 1)` for `m ≤ n` (a down-step `n+1 → n`),
together with `upW a n * dnW a (n+1) ≤ γ`, the extreme property which makes every up-step pay
one factor `γ`; `wtRho a γ n n = 1`, so a *closed* walk at `n` obeys `wtAux a l n ≤ γ ^ (l.count false)`.
-/

namespace Work.EQ

/-- Endpoint correction of a walk from state `n` to state `m`: the product of the (scaled) up
weights along a rise, resp. of the down weights along a fall. -/
noncomputable def wtRho (a γ : ℝ) (n m : ℕ) : ℝ :=
  if n ≤ m then ∏ j ∈ Finset.Ico n m, upW a j / γ else ∏ j ∈ Finset.Ico m n, dnW a (j + 1)

end Work.EQ
