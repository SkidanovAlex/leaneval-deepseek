import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

/-- The maximum order of an abelian subgroup of a finite subgroup `P` is attained: there is an
abelian `A ≤ P` with `Nat.card A = maxAbelianOrder P`.  (`maxAbelianOrder P` is defined as the
supremum of the orders of the abelian subgroups of `P`; since `P` is finite this set of orders is
bounded — by `Nat.card P` — and contains `1`, so its supremum is a member.) -/
theorem maxAbelianOrder_attained {G : Type*} [Group G] (P : Subgroup G) [Finite P] :
    ∃ A : Subgroup G, A ≤ P ∧ IsMulCommutative A ∧ Nat.card A = Work.PGroup.maxAbelianOrder P := by
  -- the set whose supremum defines `maxAbelianOrder`
  have hne : ({n : ℕ | ∃ A : Subgroup G, A ≤ P ∧ IsMulCommutative A ∧ Nat.card A = n}).Nonempty := by
    refine ⟨1, ⊥, bot_le, ?_, ?_⟩
    · exact IsMulCommutative.of_comm (fun a b => Subsingleton.elim _ _)
    · exact Subgroup.card_bot
  have hbdd : BddAbove ({n : ℕ | ∃ A : Subgroup G, A ≤ P ∧ IsMulCommutative A ∧ Nat.card A = n}) := by
    refine ⟨Nat.card P, ?_⟩
    rintro n ⟨A, hA, -, hcard⟩
    rw [← hcard]
    exact Nat.card_le_card_of_injective (fun x : A => ⟨x.1, hA x.2⟩)
      (fun x y h => Subtype.ext (congrArg (Subtype.val : ↥P → G) h))
  have hmem := Nat.sSup_mem hne hbdd
  simp only [Set.mem_ofPred_eq] at hmem
  obtain ⟨A, hA, hcom, hcard⟩ := hmem
  exact ⟨A, hA, hcom, hcard⟩

end Work.PGroup
