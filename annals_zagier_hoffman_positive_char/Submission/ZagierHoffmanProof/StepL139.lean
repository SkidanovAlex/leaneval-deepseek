import Submission.ZagierHoffmanProof.StepL138
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L139: the (b) a-side footing — the all-q front's prefix sum (SESSION 259i)

The G5 a-side weight lemma (template `g5c1_aSide_weight`, StepL78) computes
`weight (D.depA i) (D.cA i) = (k−1)·q + weight (R0.cA i')` (the iterate prepends
k−1 copies of q) and then needs, with the config's `hwtA`, the arithmetic
    (k−1)·q + (psum s r − psum s (k−1)) = weight r s,
i.e. `psum s (k−1) = (k−1)·q` — which is exactly the all-q-front hypothesis
`hallq` folded up.  This module supplies that fold:
  • ★ `maink_g5_psum_front`: `psum s (k−1) = (k−1) * Nat.card F`.
NOTE (the symbolic-count ιA trap, cf. SESSION 259h): the a-side weight statement
must quantify over `i : D.ιA` and exclude `RelData.iterIdx F (k−1) (toData R0) u`
(`D.ιA` is only propositionally `R0.ιA` for symbolic count), and the iterate's
cA values are read off with `RelData.BCqIter_cA_value` (first k−1 entries = q,
then the base tuple) — the count-1 template's `dsimp … ; rfl` does not survive.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

omit [Field F] [Finite F] [DecidableEq (RatFunc F)] in
/-- ★ The all-q front folds up: `psum s (k−1) = (k−1)·q`. -/
lemma maink_g5_psum_front (r : ℕ) (s : Fin r → ℕ+) (k : ℕ)
    (hallq : ∀ x : ℕ, x < k - 1 → pad0 s x = Nat.card F) :
    psum s (k - 1) = (k - 1) * Nat.card F := by
  change (∑ j ∈ Finset.range (k - 1), pad0 s j) = (k - 1) * Nat.card F
  rw [Finset.sum_congr rfl (fun j hj => hallq j (Finset.mem_range.mp hj))]
  simp

end ZagierHoffmanPositiveChar
