import Mathlib
import Submission.Work.BW.ulcm_le_three_pow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary definitions for Hanson's bound on `lcm(1,…,n)` in logarithmic form

This file collects the definitions used by `Submission/Work/BW/log_ulcm_le.lean`
(the Hanson bound `log (ulcm k) ≤ 1.1 * k` for `k ≥ 19`).

Everything here is definitional: the Sylvester sequence `syl` and the log-weight `Lw`
come from `Submission.Work.BW.ulcm_le_three_pow`.
-/

namespace Work.BW

open Finset

/-- The set of *active* Sylvester indices for `n`: those `i ≤ n` with `syl i ≤ n`.
These are exactly the indices whose factorial occurs nontrivially in Hanson's integer
`n ! / ∏_{i ≤ n} ⌊n / syl i⌋ !`. -/
def sylAct (n : ℕ) : Finset ℕ := (Finset.range (n + 1)).filter (fun i => syl i ≤ n)

/-- The number of active Sylvester indices, i.e. `#{i : syl i ≤ n}`. -/
def sylK (n : ℕ) : ℕ := (sylAct n).card

@[simp] lemma sylAct_def (n : ℕ) :
    sylAct n = (Finset.range (n + 1)).filter (fun i => syl i ≤ n) := rfl

lemma sylK_eq (n : ℕ) : sylK n = ((Finset.range (n + 1)).filter (fun i => syl i ≤ n)).card := rfl

end Work.BW
