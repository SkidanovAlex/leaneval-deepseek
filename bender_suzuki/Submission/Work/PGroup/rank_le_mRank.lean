import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

theorem rank_le_mRank {G : Type*} [Group G] {p : ℕ} (E : Subgroup G) [Finite G]
    (hE : Work.PGroup.IsElementaryAbelian p E) : Group.rank E ≤ Work.PGroup.mRank p G := by
  -- Every elementary abelian subgroup `F ≤ G` has `Group.rank F ≤ Nat.card G`, so the set
  -- of ranks appearing in the definition of `mRank` is bounded above.
  have hle : ∀ F : Subgroup G, Group.rank F ≤ Nat.card G := by
    intro F
    have : Fintype F := Fintype.ofFinite F
    calc Group.rank F ≤ (Finset.univ : Finset F).card :=
          Group.rank_le (by simp)
      _ = Nat.card F := by rw [Finset.card_univ, Nat.card_eq_fintype_card]
      _ ≤ Nat.card G := Subgroup.card_le_card_group F
  have hbdd : BddAbove {n : ℕ | ∃ F : Subgroup G, IsElementaryAbelian p F ∧ Group.rank F = n} :=
    ⟨Nat.card G, fun n hn => by rcases hn with ⟨F, -, rfl⟩; exact hle F⟩
  -- `Group.rank E` itself belongs to that set, whence the bound by its supremum.
  exact le_csSup hbdd ⟨E, hE, rfl⟩

end Work.PGroup
