import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.Order.CompletePartialOrder

open scoped Pointwise

namespace Commons.GroupTheory.GroupAction

/-- If `g • B = D`, then membership in `B` is equivalent to membership of `g • x` in `D`. -/
lemma mem_iff_smul_mem_of_smul_eq {G X : Type*} [Group G] [MulAction G X]
    {B D : Set X} {g : G} (h : g • B = D) : ∀ x : X, x ∈ B ↔ g • x ∈ D := by
  intro x
  rw [← h]
  exact (Set.smul_mem_smul_set_iff (a := g) (x := x) (s := B)).symm

theorem block_pair_of_not_preprimitive_four {G X : Type*} [Group G] [MulAction G X]
    [Finite X] [MulAction.IsPretransitive G X]
    (hcard : Nat.card X = 4) (h : ¬ MulAction.IsPreprimitive G X) :
    ∃ B C : Set X, MulAction.IsBlock G B ∧ MulAction.IsBlock G C ∧ Set.ncard B = 2 ∧
      Set.ncard C = 2 ∧ Disjoint B C ∧ B ∪ C = Set.univ ∧
      (∀ g : G, (∀ x : X, x ∈ B ↔ g • x ∈ B) ∨ (∀ x : X, x ∈ B ↔ g • x ∈ C)) := by
  -- Extract a block which is not trivial.
  have hexists : ∃ B : Set X, MulAction.IsBlock G B ∧ ¬ MulAction.IsTrivialBlock B := by
    by_contra hcon
    rw [not_exists] at hcon
    exact h (MulAction.IsPreprimitive.mk (fun {B} hB => by
      by_contra hnt
      exact hcon B ⟨hB, hnt⟩))
  obtain ⟨B, hB, hBtriv⟩ := hexists
  rw [MulAction.IsTrivialBlock, not_or] at hBtriv
  obtain ⟨hBnsub, hBne_univ⟩ := hBtriv
  have hBne : B.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h0
    exact hBnsub (by rw [h0]; exact Set.subsingleton_empty)
  -- The block has exactly two elements.
  have hB2le : 2 ≤ B.ncard := by
    by_contra hlt
    exact hBnsub (Set.ncard_le_one_iff_subsingleton.mp (by omega))
  have hBlt4 : B.ncard < 4 := by
    rw [← hcard]; exact Set.ncard_lt_card hBne_univ
  have hBdvd : B.ncard ∣ 4 := by
    simpa [hcard] using hB.ncard_dvd_card hBne
  have hBcard : B.ncard = 2 := by
    have h23 : B.ncard = 2 ∨ B.ncard = 3 := by omega
    rcases h23 with hh | hh
    · exact hh
    · exfalso; rw [hh] at hBdvd; norm_num at hBdvd
  -- The complement has two elements as well.
  have hBc_card : Bᶜ.ncard = 2 := by
    rw [Set.ncard_compl B, hBcard]
    omega
  -- Each translate of `B` is `B` or its complement.
  have hsplit : ∀ g : G, g • B = B ∨ g • B = Bᶜ := by
    intro g
    rcases hB.smul_eq_or_disjoint g with h' | hdisj
    · exact Or.inl h'
    · right
      refine Set.eq_of_subset_of_ncard_le ?_ ?_
      · rw [Set.subset_compl_iff_disjoint_right]; exact hdisj
      · rw [Set.ncard_compl B, Set.ncard_smul_set, hBcard]
        omega
  -- The complement is a block.
  have hBc_block : MulAction.IsBlock G Bᶜ := by
    rw [MulAction.isBlock_iff_smul_eq_or_disjoint]
    intro g
    rw [Set.smul_set_compl]
    rcases hsplit g with h' | h'
    · left; rw [h']
    · right; rw [h', compl_compl]; exact disjoint_compl_right
  refine ⟨B, Bᶜ, hB, hBc_block, hBcard, hBc_card, disjoint_compl_right, ?_, ?_⟩
  · simp
  · intro g
    rcases hsplit g with h' | h'
    · exact Or.inl (mem_iff_smul_mem_of_smul_eq h')
    · exact Or.inr (mem_iff_smul_mem_of_smul_eq h')

end Commons.GroupTheory.GroupAction