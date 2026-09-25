import Mathlib
import Submission.Work.LT.gb_wt_helpers

namespace Work.LT

/-- Combinatorial bound behind Kalachev--Panteleev Lemma 10: if `A` consists of the rows of `x`
of Hamming weight at most `α D / 2` (that is, `A = {i | hammingNorm (row x i) ≤ α D / 2}`), then the
number of the remaining rows is at most `2 |x| / (α D)`, and (using `|x| ≤ α² D² / 4`) also at most
`α D / 2`.  All expressions are cast to `ℝ`; `GB.wt x` is the Hamming weight of `x` and
`GB.row x i` is the `i`-th row. -/
theorem gb_compl_bound_row {D : ℕ} (α : ℝ) (hα : 0 < α) (hD : 0 < D)
    (x : Fin D × Fin D → ZMod 2) (hw : (GB.wt x : ℝ) ≤ α ^ 2 * (D : ℝ) ^ 2 / 4)
    (A : Finset (Fin D))
    (hA : ∀ i, i ∈ A ↔ (hammingNorm (GB.row x i) : ℝ) ≤ α * (D : ℝ) / 2) :
    (((Finset.univ \ A).card : ℕ) : ℝ) ≤ 2 * (GB.wt x : ℝ) / (α * D) ∧
      (((Finset.univ \ A).card : ℕ) : ℝ) ≤ α * (D : ℝ) / 2 := by
  classical
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hαD : 0 < α * (D : ℝ) := mul_pos hα hDpos
  have hhalf : 0 < α * (D : ℝ) / 2 := by linarith
  -- The weight of `x` is the sum of the weights of its rows.
  have hsum_eq : (GB.wt x : ℝ) = ∑ i : Fin D, (hammingNorm (GB.row x i) : ℝ) := by
    simp only [GB.wt]
    rw [hammingNorm_prod_eq_sum]
    push_cast
    exact Finset.sum_congr rfl (fun i _ => rfl)
  -- Summing the row weights over the complement of `A` is at most the total weight.
  have hsum_le : ∑ i ∈ Finset.univ \ A, (hammingNorm (GB.row x i) : ℝ) ≤ (GB.wt x : ℝ) := by
    rw [hsum_eq]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset) ?_
    intro i _ _
    positivity
  -- Each remaining row has weight at least `α D / 2`.
  have hmem : ∀ i ∈ Finset.univ \ A, α * (D : ℝ) / 2 ≤ (hammingNorm (GB.row x i) : ℝ) := by
    intro i hi
    rw [Finset.mem_sdiff] at hi
    have hnot : ¬ ((hammingNorm (GB.row x i) : ℝ) ≤ α * (D : ℝ) / 2) :=
      fun hc => hi.2 ((hA i).mpr hc)
    exact le_of_lt (not_le.mp hnot)
  -- Hence `|Aᶜ| * (α D / 2) ≤ |x|`.
  have hcard : (((Finset.univ \ A).card : ℕ) : ℝ) * (α * (D : ℝ) / 2) ≤ (GB.wt x : ℝ) := by
    calc (((Finset.univ \ A).card : ℕ) : ℝ) * (α * (D : ℝ) / 2)
        = ∑ i ∈ Finset.univ \ A, (α * (D : ℝ) / 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ Finset.univ \ A, (hammingNorm (GB.row x i) : ℝ) := Finset.sum_le_sum hmem
      _ ≤ (GB.wt x : ℝ) := hsum_le
  constructor
  · -- `|Aᶜ| ≤ 2 |x| / (α D)`
    rw [le_div_iff₀ hαD]
    nlinarith [hcard]
  · -- `|Aᶜ| ≤ α D / 2`, using `|x| ≤ α² D² / 4 = (α D / 2)²`
    have hw2 : (GB.wt x : ℝ) ≤ (α * (D : ℝ) / 2) ^ 2 := by
      have hEq : α ^ 2 * (D : ℝ) ^ 2 / 4 = (α * (D : ℝ) / 2) ^ 2 := by ring
      rw [← hEq]; exact hw
    nlinarith [hcard, hw2, hhalf]

end Work.LT
