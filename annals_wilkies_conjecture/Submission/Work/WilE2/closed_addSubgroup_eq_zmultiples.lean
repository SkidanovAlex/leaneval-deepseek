import Mathlib

namespace Work.WilE2

/-- The subgroup of integer multiples of `a` is unchanged when `a` is replaced by `-a`. -/
lemma zmultiples_neg_eq (a : ℝ) :
    AddSubgroup.zmultiples (-a) = AddSubgroup.zmultiples a := by
  refine le_antisymm ?_ ?_
  · rw [AddSubgroup.zmultiples_le]
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨-1, by simp⟩
  · rw [AddSubgroup.zmultiples_le]
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨-1, by simp⟩

/-- A closed additive subgroup of `ℝ` which is not all of `ℝ` and contains a positive
element is the group of integer multiples of some positive real number. -/
theorem closed_addSubgroup_eq_zmultiples (S : AddSubgroup ℝ) (hS : IsClosed (S : Set ℝ))
    (hT : ∃ T : ℝ, 0 < T ∧ T ∈ S) (hne : S ≠ ⊤) :
    ∃ a : ℝ, 0 < a ∧ S = AddSubgroup.zmultiples a := by
  -- An additive subgroup of `ℝ` is either dense or cyclic.
  rcases AddSubgroup.dense_or_cyclic S with hdense | ⟨a, ha⟩
  · -- A dense closed subgroup is everything, contradicting `hne`.
    exfalso
    apply hne
    have htop : (S : Set ℝ) = Set.univ := by
      rw [← hS.closure_eq]
      exact dense_iff_closure_eq.mp hdense
    exact SetLike.ext'_iff.mpr (by simpa using htop)
  · have hSzm : S = AddSubgroup.zmultiples a :=
      ha.trans (AddSubgroup.zmultiples_eq_closure a).symm
    -- The generator is nonzero, since `S` contains a positive element.
    have ha0 : a ≠ 0 := by
      intro h0
      obtain ⟨T, hTpos, hTmem⟩ := hT
      have hmem : T ∈ AddSubgroup.zmultiples (0 : ℝ) := by
        rw [← h0]
        rw [← hSzm]
        exact hTmem
      rw [AddSubgroup.zmultiples_zero_eq_bot] at hmem
      simp at hmem
      linarith
    -- Replace the generator by its absolute value, which is positive.
    rcases lt_trichotomy a 0 with hlt | heq | hgt
    · exact ⟨-a, by linarith, by rw [zmultiples_neg_eq]; exact hSzm⟩
    · exact absurd heq ha0
    · exact ⟨a, hgt, hSzm⟩

end Work.WilE2
