import Mathlib

namespace Work.WilkiesH.Count

lemma card_le_card_of_subsingleton_cover {α : Type*} {C : Finset (Set α)} {X : Set α}
    (hsub : ∀ κ ∈ C, κ.Subsingleton) (hcover : ∀ x ∈ X, ∃ κ ∈ C, x ∈ κ) {T : Finset α}
    (hT : (↑T : Set α) ⊆ X) : T.card ≤ C.card := by
  classical
  -- Pick, for each point of `X`, a member of `C` containing it.
  let f : α → Set α := fun t => if h : t ∈ X then Classical.choose (hcover t h) else ∅
  have hf_mem : ∀ t ∈ T, f t ∈ C := by
    intro t ht
    have hX : t ∈ X := hT (Finset.mem_coe.mpr ht)
    simp only [f, dite_eq_left hX]
    exact (Classical.choose_spec (hcover t hX)).1
  have hf_self : ∀ t ∈ T, t ∈ f t := by
    intro t ht
    have hX : t ∈ X := hT (Finset.mem_coe.mpr ht)
    simp only [f, dite_eq_left hX]
    exact (Classical.choose_spec (hcover t hX)).2
  -- `f` is injective on `T`, since each member of `C` is a subsingleton.
  have hinj : Set.InjOn f ↑T := by
    intro x hx y hy hxy
    have hxT : x ∈ T := Finset.mem_coe.mp hx
    have hyT : y ∈ T := Finset.mem_coe.mp hy
    have hsubx : (f x).Subsingleton := hsub (f x) (hf_mem x hxT)
    have hy_fx : y ∈ f x := by rw [hxy]; exact hf_self y hyT
    exact hsubx (hf_self x hxT) hy_fx
  have hsub2 : T.image f ⊆ C := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    exact hf_mem t ht
  calc T.card = (T.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ C.card := Finset.card_le_card hsub2

end Work.WilkiesH.Count
