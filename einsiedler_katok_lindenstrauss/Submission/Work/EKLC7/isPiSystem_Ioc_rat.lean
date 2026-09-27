import Mathlib

namespace Work.EKLC7

/-- The family of half-open intervals `Ioc a b` with **rational** endpoints is a π-system:
the intersection of `Ioc a b` and `Ioc c d` is `Ioc (max a c) (min b d)`, which again has
rational endpoints (and may be empty). -/
theorem isPiSystem_Ioc_rat :
    IsPiSystem {s : Set ℝ | ∃ a b : ℚ, s = Set.Ioc (a : ℝ) (b : ℝ)} := by
  intro s hs t ht _
  rcases hs with ⟨a, b, rfl⟩
  rcases ht with ⟨c, d, rfl⟩
  refine ⟨max a c, min b d, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ioc, Rat.cast_max, Rat.cast_min]
  constructor
  · rintro ⟨⟨ha, hb⟩, hc, hd⟩
    exact ⟨max_lt ha hc, le_min hb hd⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨lt_of_le_of_lt (le_max_left _ _) h1, le_trans h2 (min_le_left _ _)⟩,
           lt_of_le_of_lt (le_max_right _ _) h1, le_trans h2 (min_le_right _ _)⟩

end Work.EKLC7
