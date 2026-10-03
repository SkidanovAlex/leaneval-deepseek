import Mathlib

namespace Work.A3

/-- A function on `ℤ` with finite support (vanishing off a finset) is the underlying
function of a `SimpleFunc`: its range is finite and its level sets are finite or
cofinite, hence measurable. -/
theorem exists_simpleFunc_eq_of_vanishes_off (s : Finset ℤ) (f : ℤ → ℂ) (h : ∀ x ∉ s, f x = 0) : ∃ F : MeasureTheory.SimpleFunc ℤ ℂ, (F : ℤ → ℂ) = f := by
  refine ⟨⟨f, ?_, ?_⟩, rfl⟩
  · -- every fibre is measurable: it is a finite set, possibly together with the
    -- complement of `s` (which is countable, hence measurable) in the case `x = 0`
    intro x
    have hset : f ⁻¹' {x} =
        ((s.filter (fun a => f a = x) : Finset ℤ) : Set ℤ) ∪
          (if x = 0 then (s : Set ℤ)ᶜ else ∅) := by
      ext a
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      by_cases ha : a ∈ s
      · simp [ha]
      · have hfa : f a = 0 := h a ha
        simp [ha, hfa, eq_comm]
    rw [hset]
    apply MeasurableSet.union
    · exact (s.filter (fun a => f a = x)).finite_toSet.measurableSet
    · by_cases hx : x = 0
      · rw [if_pos hx]; exact (s.finite_toSet.measurableSet).compl
      · rw [if_neg hx]; exact MeasurableSet.empty
  · -- the range of `f` is contained in `f '' s ∪ {0}`, hence finite
    have hsub : Set.range f ⊆ f '' (↑s : Set ℤ) ∪ {0} := by
      rintro y ⟨a, rfl⟩
      by_cases ha : a ∈ s
      · exact Or.inl ⟨a, ha, rfl⟩
      · exact Or.inr (by simp [h a ha])
    exact ((s.finite_toSet.image f).union (Set.finite_singleton 0)).subset hsub

end Work.A3
