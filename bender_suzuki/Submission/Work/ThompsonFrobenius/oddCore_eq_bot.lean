import Mathlib
import Submission.Work.ThompsonFrobenius.Minimal
import Submission.Work.ThompsonFrobenius.Structure
import Submission.Work.ThompsonFrobenius.isSolvable_of_minimal_oddCore_ne_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ThompsonFrobenius`: the odd core of a minimal counterexample is trivial

In a minimal counterexample to Thompson's theorem the largest normal odd-order subgroup `O(Q)`
(the blueprint's `oddCore`) is trivial: otherwise `isSolvable_of_minimal_oddCore_ne_bot` would make
`Q` solvable, contradicting `IsMinimalCounterexample.not_solvable`.
-/

set_option autoImplicit false

namespace Work.ThompsonFrobenius

/-- In a minimal counterexample, `O(Q) = ⊥`. -/
theorem oddCore_eq_bot (hFT : Submission.Blueprint.FeitThompsonProp) {Q : Type} [Group Q]
    [Finite Q] {α : MulAut Q} (h : IsMinimalCounterexample Q α) :
    Submission.Blueprint.oddCore Q = ⊥ := by
  by_contra hne
  have hbelow' : ∀ (K : Type) [Group K] [Finite K] (β : MulAut K), Nat.card K < Nat.card Q →
      (orderOf β).Prime → Work.NPC.Fpf.IsFpf β → Group.IsSolvable K := by
    intro K _ _ β hlt hp hf
    haveI : Group.IsNilpotent K := h.below K β hlt hp hf
    exact IsNilpotent.to_isSolvable
  exact IsMinimalCounterexample.not_solvable h
    (isSolvable_of_minimal_oddCore_ne_bot hFT h.orderOf_prime h.fpf hbelow' hne)

end Work.ThompsonFrobenius
