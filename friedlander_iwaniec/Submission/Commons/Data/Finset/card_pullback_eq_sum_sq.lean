import Mathlib

namespace Commons.Data.Finset

theorem card_pullback_eq_sum_sq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (B : Finset α) (t : Finset β) (ht : ∀ a ∈ B, f a ∈ t) :
    ((B.product B).filter (fun pq : α × α => f pq.1 = f pq.2)).card
      = ∑ b ∈ t, ((B.filter (fun a => f a = b)).card) ^ 2 := by
  have hset : (B ×ˢ B).filter (fun pq : α × α => f pq.1 = f pq.2)
      = t.biUnion (fun b => (B.filter (fun a => f a = b)) ×ˢ (B.filter (fun a => f a = b))) := by
    ext pq
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_product]
    constructor
    · rintro ⟨⟨ha1, ha2⟩, heq⟩
      exact ⟨f pq.1, ht pq.1 ha1, ⟨ha1, rfl⟩, ha2, heq.symm⟩
    · rintro ⟨b, _hb, ⟨ha1, h1⟩, ⟨ha2, h2⟩⟩
      exact ⟨⟨ha1, ha2⟩, by rw [h1, h2]⟩
  rw [show B.product B = B ×ˢ B from rfl, hset]
  rw [Finset.card_biUnion (fun b1 _hb1 b2 _hb2 hne => by
    show Disjoint ((B.filter fun a => f a = b1) ×ˢ (B.filter fun a => f a = b1))
      ((B.filter fun a => f a = b2) ×ˢ (B.filter fun a => f a = b2))
    rw [Finset.disjoint_iff_ne]
    rintro ⟨a1, a2⟩ hx ⟨c1, c2⟩ hy heq
    simp only [Finset.mem_product, Finset.mem_filter] at hx hy
    have h1 : a1 = c1 := congrArg Prod.fst heq
    exact absurd (by rw [← hx.1.2, h1, hy.1.2]) hne)]
  apply Finset.sum_congr rfl
  intro b _hb
  rw [Finset.card_product]
  ring

end Commons.Data.Finset
