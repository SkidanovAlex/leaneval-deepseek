import Mathlib
import Submission.Work.KT.WhiteheadSetup

namespace Work.KT

namespace Whitehead

/-- Product of `1 + G p` over a list, when the values `G p` pairwise multiply to zero. -/
private lemma list_prod_one_add_comp {α β : Type*} [Semiring α] (G : β → α) (l : List β)
    (h : ∀ a ∈ l, ∀ b ∈ l, G a * G b = 0) :
    (l.map (fun p => 1 + G p)).prod = 1 + (l.map G).sum := by
  have h' : ∀ x ∈ l.map G, ∀ y ∈ l.map G, x * y = 0 := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
    exact h a ha b hb
  have hh := list_prod_one_add_of_pairwise_mul_eq_zero (l := l.map G) h'
  rw [List.map_map] at hh
  exact hh

end Whitehead

theorem whitehead_prod_lower {R : Type} [Ring R] {n : ℕ} (Y : Matrix (Fin n) (Fin n) R) :
    ((Finset.univ : Finset (Fin n × Fin n)).toList.map
      (fun p => (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
        + Matrix.single (Sum.inr p.1) (Sum.inl p.2) (Y p.1 p.2))).prod
      = (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 Y 1 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) := by
  have hpair : ∀ a ∈ (Finset.univ : Finset (Fin n × Fin n)).toList,
      ∀ b ∈ (Finset.univ : Finset (Fin n × Fin n)).toList,
      ((Matrix.single (Sum.inr a.1) (Sum.inl a.2) (Y a.1 a.2) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) *
        (Matrix.single (Sum.inr b.1) (Sum.inl b.2) (Y b.1 b.2) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R))
        = (0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) := by
    intro a _ b _
    exact Matrix.single_mul_single_of_ne (Y a.1 a.2) (Sum.inr a.1) (Sum.inl a.2)
      (Sum.inr b.1) Sum.inl_ne_inr (Y b.1 b.2)
  calc
    ((Finset.univ : Finset (Fin n × Fin n)).toList.map
        (fun p => (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
          + Matrix.single (Sum.inr p.1) (Sum.inl p.2) (Y p.1 p.2))).prod
        = 1 + ((Finset.univ : Finset (Fin n × Fin n)).toList.map
            (fun p => Matrix.single (Sum.inr p.1) (Sum.inl p.2) (Y p.1 p.2))).sum :=
          Whitehead.list_prod_one_add_comp _ _ hpair
    _ = 1 + Matrix.fromBlocks 0 0 Y 0 := by
          rw [Whitehead.finset_sum_toList, Whitehead.sum_single_inr_inl_fromBlocks]
    _ = Matrix.fromBlocks 1 0 Y 1 := by
          rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_add]
          simp

end Work.KT
