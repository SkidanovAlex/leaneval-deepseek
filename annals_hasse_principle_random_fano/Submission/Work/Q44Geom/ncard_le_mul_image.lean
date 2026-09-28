import Mathlib

namespace Work.Q44Geom

/-- Counting over the fibres of a map: if `G` is finite and every fibre of `φ` meets `G` in at most `K` points, then `#G ≤ K · #(φ '' G)`. -/
lemma ncard_le_mul_image {α β : Type*} {G : Set α} (hG : G.Finite) (φ : α → β) (K : ℕ)
    (hfiber : ∀ b : β, (G ∩ φ ⁻¹' {b}).ncard ≤ K) : G.ncard ≤ K * (φ '' G).ncard := by
  classical
  set s := hG.toFinset with hs_def
  have hs : (s : Set α) = G := hG.coe_toFinset
  have hs' : ∀ x : α, x ∈ s ↔ x ∈ G := fun x => by rw [← Finset.mem_coe, hs]
  have hfiber' : ∀ b : β, (s.filter (fun a => φ a = b)).card ≤ K := by
    intro b
    have hset : ((s.filter (fun a => φ a = b)) : Set α) = G ∩ φ ⁻¹' {b} := by
      ext x
      simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_singleton_iff, hs']
    rw [← Set.ncard_coe_finset (s.filter (fun a => φ a = b)), hset]
    exact hfiber b
  have hcard : s.card = ∑ b ∈ s.image φ, (s.filter (fun a => φ a = b)).card :=
    Finset.card_eq_sum_card_image φ s
  have hbound : ∑ b ∈ s.image φ, (s.filter (fun a => φ a = b)).card ≤ (s.image φ).card * K := by
    calc ∑ b ∈ s.image φ, (s.filter (fun a => φ a = b)).card
        ≤ ∑ b ∈ s.image φ, K := Finset.sum_le_sum (fun b _ => hfiber' b)
      _ = (s.image φ).card * K := by
            rw [Finset.sum_const, smul_eq_mul]
  have himg : (s.image φ).card = (φ '' G).ncard := by
    have hthis : (((s.image φ) : Finset β) : Set β) = φ '' G := by
      ext y
      simp only [Finset.mem_coe, Finset.mem_image, Set.mem_image, hs']
    rw [← Set.ncard_coe_finset (s.image φ), hthis]
  calc G.ncard = s.card := by rw [← hs, Set.ncard_coe_finset]
    _ = ∑ b ∈ s.image φ, (s.filter (fun a => φ a = b)).card := hcard
    _ ≤ (s.image φ).card * K := hbound
    _ = (φ '' G).ncard * K := by rw [himg]
    _ = K * (φ '' G).ncard := by rw [mul_comm]

end Work.Q44Geom
