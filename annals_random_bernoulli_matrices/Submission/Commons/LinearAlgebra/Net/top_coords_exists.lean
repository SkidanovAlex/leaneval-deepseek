import Mathlib

set_option autoImplicit false

namespace Commons.LinearAlgebra.Net

open scoped BigOperators

/-- There is a subset of `Fin n` of cardinality `m`, when `m ≤ n`. -/
private lemma exists_finset_card_eq_of_le {n m : ℕ} (hm : m ≤ n) :
    ∃ J : Finset (Fin n), J.card = m := by
  refine ⟨(Finset.univ : Finset (Fin m)).image (Fin.castLE hm), ?_⟩
  rw [Finset.card_image_of_injective]
  · simp
  · exact Fin.castLE_injective hm

/-- For any finite sequence of reals indexed by `Fin n`, and any `m ≤ n`,
there is a subset of `m` indices whose coordinates dominate (in absolute
value) all coordinates outside the subset. -/
theorem top_coords_exists {n : ℕ} (x : Fin n → ℝ) (m : ℕ) (hm : m ≤ n) :
    ∃ I : Finset (Fin n),
      I.card = m ∧
      (∀ i : Fin n, i ∈ I → ∀ j : Fin n, j ∉ I → |x j| ≤ |x i|) := by
  -- Pick, among all m-element subsets, one maximizing the sum of |x|.
  -- An exchange argument shows that it dominates its complement.
  let fam : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = m)
  have hfam : fam.Nonempty := by
    rcases exists_finset_card_eq_of_le hm with ⟨J, hJ⟩
    refine ⟨J, ?_⟩
    simp [fam, hJ]
  rcases Finset.exists_max_image fam (fun J : Finset (Fin n) => ∑ t ∈ J, |x t|) hfam with
    ⟨I, hI_mem, hI_max⟩
  refine ⟨I, ?_, ?_⟩
  · simpa [fam] using hI_mem
  · intro i hi j hj
    by_contra h
    have hlt : |x i| < |x j| := lt_of_not_ge h
    have hj_ne : j ∉ I.erase i := by
      intro hjmem
      exact hj (Finset.mem_of_mem_erase hjmem)
    have hIcard : I.card = m := by simpa [fam] using hI_mem
    have hcard_erase : (I.erase i).card = m - 1 := by
      rw [Finset.card_erase_of_mem hi, hIcard]
    have hcardI' : (insert j (I.erase i)).card = m := by
      rw [Finset.card_insert_of_notMem hj_ne, hcard_erase]
      have hpos : 0 < I.card := Finset.card_pos.mpr ⟨i, hi⟩
      omega
    have hI'_mem : insert j (I.erase i) ∈ fam := by
      simpa [fam] using hcardI'
    have hsum_le : (∑ t ∈ insert j (I.erase i), |x t|) ≤ (∑ t ∈ I, |x t|) :=
      hI_max (insert j (I.erase i)) hI'_mem
    have hsum_le' :
        |x j| + (∑ t ∈ I.erase i, |x t|) ≤ (∑ t ∈ I.erase i, |x t|) + |x i| := by
      calc
        |x j| + (∑ t ∈ I.erase i, |x t|) = ∑ t ∈ insert j (I.erase i), |x t| := by
          rw [Finset.sum_insert hj_ne]
        _ ≤ ∑ t ∈ I, |x t| := hsum_le
        _ = (∑ t ∈ I.erase i, |x t|) + |x i| :=
          (Finset.sum_erase_add I (fun t => |x t|) hi).symm
    linarith

end Commons.LinearAlgebra.Net
