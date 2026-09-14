import Mathlib.GroupTheory.OrderOfElement

namespace Commons.GroupTheory.OrderOf

/-- If an element `g` of a finite group has order equal to the cardinality of the group,
then every element of the group is a power of `g` with exponent below the group order. -/
theorem exists_pow_lt_card_eq_of_orderOf_eq_card {G : Type*} [Group G] [Fintype G] (g : G)
    (h : orderOf g = Fintype.card G) : ∀ x : G, ∃ k : ℕ, k < Fintype.card G ∧ g ^ k = x := by
  classical
  intro x
  -- The set of powers g ^ k with k < orderOf g.
  let s : Finset G := (Finset.range (orderOf g)).image (fun k => g ^ k)
  have hinj : Set.InjOn (fun k : ℕ => g ^ k) (↑(Finset.range (orderOf g)) : Set ℕ) := by
    simpa [Finset.coe_range] using (pow_injOn_Iio_orderOf (x := g))
  have hcard : s.card = Fintype.card G := by
    rw [← h]
    dsimp [s]
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hs : s = Finset.univ := Finset.eq_univ_of_card s hcard
  have hxs : x ∈ s := by rw [hs]; simp
  rw [Finset.mem_image] at hxs
  rcases hxs with ⟨k, hkr, hkpow⟩
  refine ⟨k, ?_, hkpow⟩
  have hklt : k < orderOf g := Finset.mem_range.mp hkr
  rwa [h] at hklt

end Commons.GroupTheory.OrderOf