import Mathlib
import Submission.Work.WilC4.ULPMDev

namespace Work.WilC4

/-- If a continuous function `g` on `[a, b]` never takes a value in `Mid E`, then no value of
`Mid E` can lie strictly between `g a` and `g b`: such a value would be attained on `[a, b]` by
the intermediate value theorem. -/
theorem cbz_not_mid_between_of_image {E : Set ℝ} {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn g (Set.Icc a b))
    (havoid : ∀ t ∈ Set.Icc a b, g t ∉ Work.WilC4.Mid E) :
    ∀ x ∈ Work.WilC4.Mid E, ¬ (min (g a) (g b) < x ∧ x < max (g a) (g b)) := by
  intro x hx hmid
  obtain ⟨h1, h2⟩ := hmid
  have hxmem : x ∈ Set.uIcc (g a) (g b) := ⟨le_of_lt h1, le_of_lt h2⟩
  have hcont' : ContinuousOn g (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab]
  have himg : x ∈ g '' Set.uIcc a b := intermediate_value_uIcc hcont' hxmem
  obtain ⟨t, ht, hgt⟩ := himg
  rw [Set.uIcc_of_le hab] at ht
  exact havoid t ht (by rw [hgt]; exact hx)

end Work.WilC4
