import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausTwoGroup

theorem exists_half_transversal {α : Type*} [Fintype α] (T : Finset α) (σ : α → α)
    (hσT : ∀ a ∈ T, σ a ∈ T) (hσ2 : ∀ a : α, σ (σ a) = a) (hfix : ∀ a ∈ T, σ a ≠ a) :
    ∃ S : Finset α, S ⊆ T ∧ S.card * 2 = T.card ∧ ∀ a ∈ S, σ a ∉ S := by
  classical
  -- A linear order on the finite type, obtained by transporting the order on `Fin _`.
  letI : LinearOrder α :=
    LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective
  -- `σ` is an involution, hence injective, on all of `α`.
  have hσinj : Function.Injective σ := (show Function.Involutive σ from hσ2).injective
  -- The transversal: the elements of `T` that are *smaller* than their image under `σ`.
  set S : Finset α := T.filter (fun a => a < σ a) with hS
  -- Its complement in `T`: the elements that are *larger* than their image.
  set S' : Finset α := T.filter (fun a => ¬ a < σ a) with hS'
  -- `T` is the disjoint union of `S` and `S'`, ...
  have hsum : S.card + S'.card = T.card := by
    have h := Finset.card_filter_add_card_filter_not (s := T) (p := fun a => a < σ a)
    rwa [← hS, ← hS'] at h
  -- ... and `σ` is a bijection `S ≃ S'`, so `S` and `S'` have the same size.
  have hS'eq : S' = S.image σ := by
    ext b
    simp only [hS', hS, Finset.mem_filter, Finset.mem_image]
    constructor
    · -- every `b ∈ S'` is the image of `σ b ∈ S`
      rintro ⟨hbT, hbnot⟩
      refine ⟨σ b, ?_, hσ2 b⟩
      refine ⟨hσT b hbT, ?_⟩
      rcases lt_trichotomy b (σ b) with h | h | h
      · exact absurd h hbnot
      · exact absurd h.symm (hfix b hbT)
      · rw [hσ2 b]; exact h
    · -- the image of an element of `S` lies in `S'`
      rintro ⟨a, ⟨haT, halt⟩, rfl⟩
      refine ⟨hσT a haT, ?_⟩
      rw [hσ2 a]
      exact not_lt.mpr (le_of_lt halt)
  have hcard' : S'.card = S.card := by
    rw [hS'eq, Finset.card_image_of_injective S hσinj]
  refine ⟨S, ?_, ?_, ?_⟩
  · rw [hS]; exact Finset.filter_subset _ _
  · rw [← hsum, hcard']; omega
  · -- `S` contains no pair `{a, σ a}`
    intro a ha ha'
    rw [hS] at ha ha'
    simp only [Finset.mem_filter] at ha ha'
    rw [hσ2 a] at ha'
    exact absurd ha'.2 (not_lt.mpr (le_of_lt ha.2))

end Work.ZassenhausTwoGroup
