import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.LocUnif

/-- A point of `Icc a b` that is not in the open interval `Ioo a b` is one of the two
endpoints. -/
private lemma mem_pair_of_mem_Icc_not_mem_Ioo {a b x : ℝ} (hx : x ∈ Set.Icc a b)
    (hx' : x ∉ Set.Ioo a b) : x ∈ ({a, b} : Set ℝ) := by
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  obtain ⟨hax, hxb⟩ := hx
  rcases eq_or_lt_of_le hax with h | h
  · exact Or.inl h.symm
  · exact Or.inr (le_antisymm hxb (le_of_not_gt fun hlt => hx' ⟨h, hlt⟩))

/-- A pair of finite sets has measure zero in `ℝ × ℝ`. -/
private lemma volume_pair_prod_univ (a b : ℝ) :
    MeasureTheory.volume (({a, b} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
  have h0 : MeasureTheory.volume ({a, b} : Set ℝ) = 0 := by
    rw [Set.insert_eq, MeasureTheory.measure_union_null_iff]
    exact ⟨Real.volume_singleton, Real.volume_singleton⟩
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, MeasureTheory.Measure.prod_prod, h0, zero_mul]

/-- A pair of finite sets has measure zero in `ℝ × ℝ`, vertical version. -/
private lemma volume_univ_prod_pair (c d : ℝ) :
    MeasureTheory.volume ((Set.univ : Set ℝ) ×ˢ ({c, d} : Set ℝ)) = 0 := by
  have h0 : MeasureTheory.volume ({c, d} : Set ℝ) = 0 := by
    rw [Set.insert_eq, MeasureTheory.measure_union_null_iff]
    exact ⟨Real.volume_singleton, Real.volume_singleton⟩
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ, MeasureTheory.Measure.prod_prod, h0, mul_zero]

theorem volume_box_sdiff_openBox (a b c d : ℝ) :
    MeasureTheory.volume ((Set.Icc a b ×ˢ Set.Icc c d : Set (ℝ × ℝ)) \
      (Set.Ioo a b ×ˢ Set.Ioo c d : Set (ℝ × ℝ))) = 0 := by
  refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_union_null
    (volume_pair_prod_univ a b) (volume_univ_prod_pair c d))
  rintro ⟨x, y⟩ ⟨⟨hx, hy⟩, hnot⟩
  rw [Set.mem_union]
  by_cases hxy : x ∈ Set.Ioo a b
  · right
    exact ⟨Set.mem_univ x,
      mem_pair_of_mem_Icc_not_mem_Ioo hy fun hy' => hnot ⟨hxy, hy'⟩⟩
  · left
    exact ⟨mem_pair_of_mem_Icc_not_mem_Ioo hx hxy, Set.mem_univ y⟩

end Work.FTS.StrongEps.LocUnif
