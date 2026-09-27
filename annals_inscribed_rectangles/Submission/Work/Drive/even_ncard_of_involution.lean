import Mathlib

namespace Work.Drive

/-- **Fixed-point-free involutions pair up a finite set.**
If a finite `Finset t` is mapped into itself by `f`, and `f` is an involution on `t`
with no fixed points on `t`, then `t.card` is even: `t` splits into the two-element
orbits `{x, f x}`. Proved by strong induction on `t.card`, peeling off one orbit. -/
private theorem finset_even_card_of_involution {α : Type*} (f : α → α) :
    ∀ t : Finset α, (∀ x ∈ t, f x ∈ t) → (∀ x ∈ t, f (f x) = x) →
      (∀ x ∈ t, f x ≠ x) → Even t.card := by
  classical
  intro t
  induction t using Finset.strongInductionOn with
  | _ t ih =>
    intro hmaps hinv hfix
    rcases Finset.eq_empty_or_nonempty t with h | ⟨x, hx⟩
    · rw [h, Finset.card_empty]; exact ⟨0, rfl⟩
    · -- peel off the orbit `{x, f x}` and apply the induction hypothesis
      have hfx_mem : f x ∈ t := hmaps x hx
      have hfxx : f x ≠ x := hfix x hx
      have hfx_erase : f x ∈ t.erase x := Finset.mem_erase.mpr ⟨hfxx, hfx_mem⟩
      set u := (t.erase x).erase (f x) with hu
      have hmem_u : ∀ y, y ∈ u ↔ y ∈ t ∧ y ≠ x ∧ y ≠ f x := by
        intro y; rw [hu, Finset.mem_erase, Finset.mem_erase]; tauto
      have hu_sub : u ⊆ t := by
        intro y hy; exact ((hmem_u y).mp hy).1
      have hx_not_u : x ∉ u := by
        intro hcon; exact ((hmem_u x).mp hcon).2.1 rfl
      have hu_ne : u ≠ t := by
        intro heq; exact hx_not_u (heq ▸ hx)
      have hu_ssub : u ⊂ t := Finset.ssubset_iff_subset_ne.mpr ⟨hu_sub, hu_ne⟩
      have ih_u : Even u.card := by
        apply ih u hu_ssub
        · intro y hy
          obtain ⟨hyt, hyx, hyfx⟩ := (hmem_u y).mp hy
          refine (hmem_u (f y)).mpr ⟨hmaps y hyt, ?_, ?_⟩
          · intro hfyx
            have hcon : f (f y) = f x := by rw [hfyx]
            rw [hinv y hyt] at hcon
            exact hyfx hcon
          · intro hfyfx
            have hcon : f (f y) = f (f x) := by rw [hfyfx]
            rw [hinv y hyt, hinv x hx] at hcon
            exact hyx hcon
        · intro y hy; exact hinv y ((hmem_u y).mp hy).1
        · intro y hy; exact hfix y ((hmem_u y).mp hy).1
      have hcard : u.card + 2 = t.card := by
        have h1 : u.card + 1 = (t.erase x).card := by
          rw [hu]; exact Finset.card_erase_add_one hfx_erase
        have h2 : (t.erase x).card + 1 = t.card := Finset.card_erase_add_one hx
        omega
      rw [← hcard]
      exact ih_u.add even_two

/-- A finite set equipped with a fixed-point-free involution has even cardinality. -/
theorem even_ncard_of_involution {α : Type*} {s : Set α} (hs : s.Finite) (f : α → α)
    (hmaps : ∀ x ∈ s, f x ∈ s) (hinv : ∀ x ∈ s, f (f x) = x) (hfix : ∀ x ∈ s, f x ≠ x) :
    Even s.ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card s hs]
  apply finset_even_card_of_involution f hs.toFinset
  · intro x hx
    exact (Set.Finite.mem_toFinset hs).mpr (hmaps x ((Set.Finite.mem_toFinset hs).mp hx))
  · intro x hx
    exact hinv x ((Set.Finite.mem_toFinset hs).mp hx)
  · intro x hx
    exact hfix x ((Set.Finite.mem_toFinset hs).mp hx)

end Work.Drive
