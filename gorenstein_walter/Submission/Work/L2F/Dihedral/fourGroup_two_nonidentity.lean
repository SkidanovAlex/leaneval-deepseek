import Mathlib

set_option linter.style.haveILetI false

namespace Work.L2F.Dihedral

/-- A subgroup of order `4` contains at least two distinct nonidentity elements: its
nonidentity part has cardinality `4 - 1 = 3`. -/
lemma fourGroup_two_nonidentity {G : Type*} [Group G] (V : Subgroup G) (hV : Nat.card V = 4) :
    ∃ u w : V, u ≠ 1 ∧ w ≠ 1 ∧ u ≠ w := by
  classical
  have hfin : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; norm_num)
  haveI : Fintype V := Fintype.ofFinite V
  -- the nonidentity elements form a finset of cardinality `4 - 1 = 3`
  have hcard : ((Finset.univ : Finset V).erase 1).card = 3 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ (1 : V)), Finset.card_univ]
    rw [← Nat.card_eq_fintype_card, hV]
  have h2 : 1 < ((Finset.univ : Finset V).erase 1).card := by omega
  obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp h2
  exact ⟨u, w, (Finset.mem_erase.mp hu).1, (Finset.mem_erase.mp hw).1, huw⟩

end Work.L2F.Dihedral
