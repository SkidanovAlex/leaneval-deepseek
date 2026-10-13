import Mathlib

namespace Work.WilkG4c

/-- **A continuous injective function on an interval maps an interior point to a value strictly
between the values at the endpoints.** -/
theorem mem_Ioo_min_max_of_injOn {f : ℝ → ℝ} {a b s : ℝ} (has : a < s) (hsb : s < b)
    (hcont : ContinuousOn f (Set.Icc a b)) (hinj : Set.InjOn f (Set.Icc a b)) :
    f s ∈ Set.Ioo (min (f a) (f b)) (max (f a) (f b)) := by
  have hab : a ≤ b := le_of_lt (lt_trans has hsb)
  have ha : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  have hb : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab
  have hs : s ∈ Set.Icc a b := ⟨le_of_lt has, le_of_lt hsb⟩
  rcases ContinuousOn.strictMonoOn_of_injOn_Icc' hab hcont hinj with hmono | hanti
  · exact ⟨lt_of_le_of_lt (min_le_left _ _) (hmono ha hs has),
           lt_of_lt_of_le (hmono hs hb hsb) (le_max_right _ _)⟩
  · exact ⟨lt_of_le_of_lt (min_le_right _ _) (hanti hs hb hsb),
           lt_of_lt_of_le (hanti ha hs has) (le_max_left _ _)⟩

end Work.WilkG4c
