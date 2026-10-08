import Submission.Work.Endgame.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `O(G) = 1` in a simple group of even order

`oddCore G` is defined in `Submission.Blueprint.Interfaces` as the supremum of the normal
subgroups of odd order.  Its only use in the endgame is the following: in a *simple* group of even
order the family of normal odd-order subgroups degenerates to `{⊥}`, so `oddCore G = ⊥`.  Indeed a
normal subgroup of odd order is `⊥` or `⊤` by simplicity, and `⊤` would make `|G|` odd.

Note that no finiteness hypothesis is needed: the argument is purely about the defining
supremum of an empty-ish family.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.Endgame

/-- In a simple group of even order, `O(G) = O_{2'}(G) = 1`: every normal subgroup of odd order
is trivial (`⊤` would force `|G|` odd), so the defining supremum is that of `{⊥}`. -/
theorem oddCore_eq_bot_of_isSimpleGroup_of_even {G : Type*} [Group G] [IsSimpleGroup G]
    (h : Even (Nat.card G)) : oddCore G = ⊥ := by
  have hnotodd : ¬ Odd (Nat.card G) := Nat.not_odd_iff_even.mpr h
  have hset : {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)} = {⊥} := by
    ext N
    constructor
    · rintro ⟨hN, hNo⟩
      rcases hN.eq_bot_or_eq_top with h1 | h1
      · exact h1
      · subst h1
        rw [Subgroup.card_top] at hNo
        exact absurd hNo hnotodd
    · intro hN
      rw [Set.mem_singleton_iff] at hN
      subst hN
      exact ⟨Subgroup.normal_bot, by rw [Subgroup.card_bot]; exact odd_one⟩
  change sSup {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)} = ⊥
  rw [hset, sSup_singleton]

end Work.Endgame
