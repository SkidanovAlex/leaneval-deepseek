import Mathlib.Data.Finset.Range
import Submission.Work.BoseFixB2.DvApriori.BandDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB2.DvApriori

/-- If two subsets `S`, `T` of `range n` both contain the index `j` and are distinct,
then they differ at some index `i ≠ j`. -/
theorem exists_diff_slot {n : ℕ} (j : Fin n) {S T : Finset ℕ} (hS : S ⊆ Finset.range n)
    (hT : T ⊆ Finset.range n) (hjS : (j : ℕ) ∈ S) (hjT : (j : ℕ) ∈ T) (hST : S ≠ T) :
    ∃ i : Fin n, i ≠ j ∧ (((i : ℕ) ∈ S ∧ (i : ℕ) ∉ T) ∨ ((i : ℕ) ∈ T ∧ (i : ℕ) ∉ S)) := by
  -- Any element of the symmetric difference is `< n`, and is never `j` itself
  -- (because `j` lies in both sets).
  have keyS : ∀ {x : ℕ}, x ∈ S → x ∉ T → x < n ∧ x ≠ (j : ℕ) := by
    intro x hxS hxT
    exact ⟨Finset.mem_range.mp (hS hxS), fun h => hxT (h ▸ hjT)⟩
  have keyT : ∀ {x : ℕ}, x ∈ T → x ∉ S → x < n ∧ x ≠ (j : ℕ) := by
    intro x hxT hxS
    exact ⟨Finset.mem_range.mp (hT hxT), fun h => hxS (h ▸ hjS)⟩
  by_cases hsub : S ⊆ T
  · -- `S ⊆ T` but `S ≠ T`, so `T` is not contained in `S`.
    have hnot : ¬ T ⊆ S := fun h' => hST (Finset.Subset.antisymm hsub h')
    rw [Finset.not_subset] at hnot
    obtain ⟨x, hxT, hxS⟩ := hnot
    obtain ⟨hxlt, hxj⟩ := keyT hxT hxS
    exact ⟨⟨x, hxlt⟩, fun hi => hxj (congrArg Fin.val hi), Or.inr ⟨hxT, hxS⟩⟩
  · -- `S ⊄ T`: pick a witness.
    rw [Finset.not_subset] at hsub
    obtain ⟨x, hxS, hxT⟩ := hsub
    obtain ⟨hxlt, hxj⟩ := keyS hxS hxT
    exact ⟨⟨x, hxlt⟩, fun hi => hxj (congrArg Fin.val hi), Or.inl ⟨hxS, hxT⟩⟩

end Work.BoseFixB2.DvApriori
