import Mathlib

namespace Work.Mostow

/-- A subgroup `S` of `ℝ` meeting every bounded interval in a finite set is
discrete: there is a gap `ε > 0` with no nonzero element of `S` in `(-ε, ε)`.

The proof takes `ε` to be the minimal absolute value of a nonzero element of
`S ∩ [-1,1]` (this set is finite by hypothesis); if there is no such element
then `ε = 1` works. -/
theorem discreteSubgroupGap (S : AddSubgroup ℝ)
    (hfin : ∀ R : ℝ, ((S : Set ℝ) ∩ Set.Icc (-R) R).Finite) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ S, |x| < ε → x = 0 := by
  have hT : ((S : Set ℝ) ∩ Set.Icc (-1:ℝ) 1).Finite := hfin 1
  by_cases h : ∃ x ∈ (S : Set ℝ) ∩ Set.Icc (-1:ℝ) 1, x ≠ 0
  · obtain ⟨a, ha, ha0⟩ := h
    have hSfin : ({x : ℝ | x ∈ S ∧ x ∈ Set.Icc (-1:ℝ) 1 ∧ x ≠ 0}).Finite :=
      hT.subset (by rintro x ⟨hxS, hxI, _⟩; exact ⟨hxS, hxI⟩)
    have hSne : ({x : ℝ | x ∈ S ∧ x ∈ Set.Icc (-1:ℝ) 1 ∧ x ≠ 0}).Nonempty :=
      ⟨a, ha.1, ha.2, ha0⟩
    obtain ⟨m, hm, hmin⟩ := Set.exists_min_image _ (fun x => |x|) hSfin hSne
    refine ⟨|m|, abs_pos.mpr hm.2.2, ?_⟩
    intro x hxS hxlt
    have hmle : |m| ≤ 1 := abs_le.mpr hm.2.1
    have hxle : |x| ≤ 1 := le_trans (le_of_lt hxlt) hmle
    have hxI : x ∈ Set.Icc (-1:ℝ) 1 := abs_le.mp hxle
    by_contra hx0
    have : |m| ≤ |x| := hmin x ⟨hxS, hxI, hx0⟩
    exact absurd hxlt (not_lt.mpr this)
  · refine ⟨1, one_pos, ?_⟩
    intro x hxS hxlt
    by_contra hx0
    refine h ⟨x, ⟨hxS, ?_⟩, hx0⟩
    exact abs_le.mp (le_of_lt hxlt)

end Work.Mostow
