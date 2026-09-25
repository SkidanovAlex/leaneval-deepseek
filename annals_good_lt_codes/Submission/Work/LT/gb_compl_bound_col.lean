import Mathlib
import Submission.Work.LT.gb_wt_helpers

namespace Work.LT

/-- Combinatorial bound behind Kalachev--Panteleev Lemma 10: if `B` consists of the columns of `x`
of Hamming weight at most `α D / 2` (that is, `B = {j | hammingNorm (col x j) ≤ α D / 2}`), then the
number of the remaining columns is at most `2 |x| / (α D)`, and (using `|x| ≤ α² D² / 4`) also at
most `α D / 2`.  All expressions are cast to `ℝ`; `GB.wt x` is the Hamming weight of `x` and
`GB.col x j` is the `j`-th column. -/
theorem gb_compl_bound_col {D : ℕ} (α : ℝ) (hα : 0 < α) (hD : 0 < D)
    (x : Fin D × Fin D → ZMod 2) (hw : (GB.wt x : ℝ) ≤ α ^ 2 * (D : ℝ) ^ 2 / 4)
    (B : Finset (Fin D))
    (hB : ∀ j, j ∈ B ↔ (hammingNorm (GB.col x j) : ℝ) ≤ α * (D : ℝ) / 2) :
    (((Finset.univ \ B).card : ℕ) : ℝ) ≤ 2 * (GB.wt x : ℝ) / (α * D) ∧
      (((Finset.univ \ B).card : ℕ) : ℝ) ≤ α * (D : ℝ) / 2 := by
  have hαD : 0 < α * (D : ℝ) := mul_pos hα (by exact_mod_cast hD)
  -- `wt x` is the sum of the Hamming weights of the columns
  have hsum_nat : hammingNorm x = ∑ j : Fin D, hammingNorm (GB.col x j) := by
    rw [hammingNorm_prod_eq_sum_col]
    rfl
  have hsum : (GB.wt x : ℝ) = ∑ j : Fin D, (hammingNorm (GB.col x j) : ℝ) := by
    rw [GB.wt, hsum_nat]
    push_cast
    rfl
  -- every column outside `B` has Hamming weight at least `α D / 2`
  have hterm : ∀ j ∈ Finset.univ \ B,
      α * (D : ℝ) / 2 ≤ (hammingNorm (GB.col x j) : ℝ) := by
    intro j hj
    have hjnB : j ∉ B := (Finset.mem_sdiff.mp hj).2
    have hnot : ¬ ((hammingNorm (GB.col x j) : ℝ) ≤ α * (D : ℝ) / 2) :=
      fun h => hjnB ((hB j).mpr h)
    exact le_of_lt (not_le.mp hnot)
  have hbound : (((Finset.univ \ B).card : ℕ) : ℝ) * (α * (D : ℝ) / 2)
      ≤ ∑ j ∈ Finset.univ \ B, (hammingNorm (GB.col x j) : ℝ) := by
    have := Finset.card_nsmul_le_sum (Finset.univ \ B)
      (fun j => (hammingNorm (GB.col x j) : ℝ)) (α * (D : ℝ) / 2) hterm
    simpa [nsmul_eq_mul] using this
  have hle : ∑ j ∈ Finset.univ \ B, (hammingNorm (GB.col x j) : ℝ) ≤ (GB.wt x : ℝ) := by
    rw [hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
      (fun i _ _ => by positivity)
  have hcard_le : (((Finset.univ \ B).card : ℕ) : ℝ) * (α * (D : ℝ) / 2) ≤ (GB.wt x : ℝ) :=
    le_trans hbound hle
  have hhalf : 0 < α * (D : ℝ) / 2 := by positivity
  have h1 : (((Finset.univ \ B).card : ℕ) : ℝ) ≤ 2 * (GB.wt x : ℝ) / (α * (D : ℝ)) := by
    have h := (le_div_iff₀ hhalf).mpr hcard_le
    calc (((Finset.univ \ B).card : ℕ) : ℝ) ≤ (GB.wt x : ℝ) / (α * (D : ℝ) / 2) := h
      _ = 2 * (GB.wt x : ℝ) / (α * (D : ℝ)) := by
        rw [div_div_eq_mul_div]; ring
  have h2 : 2 * (GB.wt x : ℝ) / (α * (D : ℝ)) ≤ α * (D : ℝ) / 2 := by
    rw [div_le_iff₀ hαD]
    nlinarith [hw]
  exact ⟨h1, le_trans h1 h2⟩

end Work.LT
