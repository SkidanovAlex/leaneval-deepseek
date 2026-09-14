import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Card

namespace Commons.Data.Set

theorem ncard_le_sum_fiber {α β : Type*} (P : Set (α × β)) (hPfin : P.Finite) (s : Finset α) (f : α → ℕ) (hs : ∀ p ∈ P, p.1 ∈ s) (hf : ∀ a ∈ s, (({b : β | (a, b) ∈ P} : Set β)).ncard ≤ f a) : P.ncard ≤ s.sum f := by
  classical
  have hmain : hPfin.toFinset.card
      = ∑ a ∈ s, (hPfin.toFinset.filter (fun p => p.1 = a)).card :=
    Finset.card_eq_sum_card_fiberwise (t := s) (f := fun p : α × β => p.1) (by
      intro p hp
      exact hs p ((Set.Finite.mem_toFinset hPfin).mp hp))
  rw [Set.ncard_eq_toFinset_card _ hPfin, hmain]
  refine Finset.sum_le_sum fun a ha => ?_
  have hfin : ({b : β | (a, b) ∈ P} : Set β).Finite := by
    have hset : ({b : β | (a, b) ∈ P} : Set β) = Prod.snd '' (P ∩ {p : α × β | p.1 = a}) := by
      ext b
      constructor
      · intro hb
        exact ⟨(a, b), ⟨hb, rfl⟩, rfl⟩
      · rintro ⟨p, ⟨hpP, hp1⟩, rfl⟩
        simp only [Set.mem_ofPred_eq] at hp1 ⊢
        rwa [← hp1]
    rw [hset]
    exact (hPfin.subset Set.inter_subset_left).image Prod.snd
  have hinj : Set.InjOn Prod.snd ((hPfin.toFinset.filter (fun p => p.1 = a)) : Set (α × β)) := by
    intro p hp q hq hpq
    simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
    exact Prod.ext (by rw [hp.2, hq.2]) hpq
  have hsub : (((hPfin.toFinset.filter (fun p => p.1 = a)).image Prod.snd : Finset β) : Set β)
      ⊆ {b : β | (a, b) ∈ P} := by
    intro b hb
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_filter] at hb
    obtain ⟨p, ⟨hpP, hp1⟩, hpb⟩ := hb
    rw [← hpb, ← hp1]
    exact (Set.Finite.mem_toFinset hPfin).mp hpP
  calc (hPfin.toFinset.filter (fun p => p.1 = a)).card
      = ((hPfin.toFinset.filter (fun p => p.1 = a)).image Prod.snd).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ = (((hPfin.toFinset.filter (fun p => p.1 = a)).image Prod.snd : Finset β) : Set β).ncard := by
        rw [Set.ncard_coe_finset]
    _ ≤ ({b : β | (a, b) ∈ P} : Set β).ncard := Set.ncard_le_ncard hsub hfin
    _ ≤ f a := hf a ha

end Commons.Data.Set