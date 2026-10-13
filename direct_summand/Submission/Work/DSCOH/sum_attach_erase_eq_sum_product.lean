import Mathlib

namespace Work.DSCOH

theorem sum_attach_erase_eq_sum_product {α : Type*} [DecidableEq α] {X : Type*} [AddCommMonoid X]
    (s : Finset α) (G : (i : α) → i ∈ s → (j : α) → j ∈ s.erase i → X) :
    (∑ i ∈ s.attach, ∑ j ∈ (s.erase i.1).attach, G i.1 i.2 j.1 j.2) =
      ∑ p ∈ s ×ˢ s,
        (if h : p.1 ∈ s ∧ p.2 ∈ s.erase p.1 then G p.1 h.1 p.2 h.2 else 0) := by
  classical
  -- Collapse the dependent membership proofs into a single guarded function.
  let g : α → α → X := fun i j => if h : i ∈ s ∧ j ∈ s.erase i then G i h.1 j h.2 else 0
  have hL : (∑ i ∈ s.attach, ∑ j ∈ (s.erase i.1).attach, G i.1 i.2 j.1 j.2)
          = ∑ i ∈ s, ∑ j ∈ s.erase i, g i j := by
    have h1 : (∑ i ∈ s.attach, ∑ j ∈ (s.erase i.1).attach, G i.1 i.2 j.1 j.2)
            = ∑ i ∈ s.attach, ∑ j ∈ (s.erase i.1).attach, g i.1 j.1 := by
      apply Finset.sum_congr rfl; intro i hi
      apply Finset.sum_congr rfl; intro j hj
      simp only [g]
      rw [dite_eq_left (show i.1 ∈ s ∧ j.1 ∈ s.erase i.1 from ⟨i.2, j.2⟩)]
    rw [h1]
    have h2 : (∑ i ∈ s.attach, ∑ j ∈ (s.erase i.1).attach, g i.1 j.1)
            = ∑ i ∈ s.attach, ∑ j ∈ s.erase i.1, g i.1 j := by
      apply Finset.sum_congr rfl; intro i hi
      exact Finset.sum_attach (s.erase i.1) (g i.1)
    rw [h2]
    exact Finset.sum_attach s (fun x => ∑ j ∈ s.erase x, g x j)
  have hR : (∑ p ∈ s ×ˢ s,
        (if h : p.1 ∈ s ∧ p.2 ∈ s.erase p.1 then G p.1 h.1 p.2 h.2 else 0))
          = ∑ i ∈ s, ∑ j ∈ s, g i j := by
    rw [Finset.sum_product]
  have hfin : (∑ i ∈ s, ∑ j ∈ s.erase i, g i j) = ∑ i ∈ s, ∑ j ∈ s, g i j := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Finset.sum_erase s (by
      simp only [g]
      exact dite_eq_right (by intro h; exact (Finset.mem_erase.mp h.2).1 rfl))
  rw [hL, hR, hfin]

end Work.DSCOH
