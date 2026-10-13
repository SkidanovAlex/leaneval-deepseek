import Mathlib

namespace Work.DSCOH

/-- Every `β` in the set is bounded below by `-d`: the sum of the other coordinates is `≤ 0`
because each of them is `≤ -1 ≤ 0`, and the total sum is `-d`.  Above it is bounded by `-1`
by hypothesis, so the set is contained in the finite product of the intervals `[-d, -1]`. -/
theorem finite_beta_set {n d : ℕ} :
    Finite {β : Fin n → ℤ // (∀ i, β i ≤ -1) ∧ (∑ i, β i) = -(d : ℤ)} := by
  apply Set.Finite.to_subtype
  apply Set.Finite.subset (Set.Finite.pi' (fun _ : Fin n => Set.finite_Icc (-(d : ℤ)) (-1)))
  intro β hβ i
  obtain ⟨hle, hsum⟩ := hβ
  have hmem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin n)) β hmem
  have hS : ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, β j ≤ 0 := by
    calc ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, β j
        ≤ ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, (0 : ℤ) := by
          apply Finset.sum_le_sum
          intro j _
          exact le_trans (hle j) (by norm_num)
      _ = 0 := by simp
  refine ⟨?_, hle i⟩
  linarith [hsplit, hsum, hS]

end Work.DSCOH
