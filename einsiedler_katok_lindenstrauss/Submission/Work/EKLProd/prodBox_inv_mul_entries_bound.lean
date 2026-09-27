import Mathlib
import Submission.Work.EKLProd.ProdPlaqueDefs
import Submission.Work.EKLProd.prodBox_mul_inv_entries_bound

/-!
# Entrywise boundedness of `g'⁻¹ * g` for `g, g'` in the product box

The product box `prodBox T U ε = (V ε ∩ T) * (V ε ∩ U)` is a bounded set of matrices: writing
`g = t v` with `t, v ∈ V ε`, we have `|g i j| ≤ 3 (1+ε)²` and, since
`g⁻¹ = v⁻¹ t⁻¹`, `|(g⁻¹) i j| ≤ 3 (2 (1+ε)²)²` (using `inv_entry_le`).  Hence for `g, g'` in
the box the entries of `g'⁻¹ * g` are bounded by `3 · (3 (2 (1+ε)²)²) · (3 (1+ε)²)`.

This is the companion of `prodBox_mul_inv_entries_bound` (which bounds the right translate
`a · g₀⁻¹`); here the two box elements are on the two sides of the inverse.
-/

namespace Work.EKLProd

open Work.EKLContract

/-- Every entry of an element of the product box is bounded by `3 (1+ε)²`. -/
lemma prodBox_entry_le {T U : Subgroup SL3} {ε : ℝ} (hε : 0 < ε)
    {g : SL3} (hg : g ∈ prodBox T U ε) (i j : Fin 3) :
    |g i j| ≤ 3 * (1 + ε) ^ 2 := by
  obtain ⟨t, ⟨htV, _⟩, v, ⟨hvV, _⟩, rfl⟩ := hg
  have h := abs_mul_entries_le (b := 1 + ε) (d := 1 + ε) (by positivity) (by positivity)
    (fun i j => abs_entry_le_of_mem_V htV i j)
    (fun i j => abs_entry_le_of_mem_V hvV i j) i j
  have heq : 3 * ((1 + ε) * (1 + ε)) = 3 * (1 + ε) ^ 2 := by ring
  linarith [h, heq]

/-- Every entry of the inverse of an element of the product box is bounded by
`3 (2 (1+ε)²)²`. -/
lemma prodBox_inv_entry_le {T U : Subgroup SL3} {ε : ℝ} (hε : 0 < ε)
    {g : SL3} (hg : g ∈ prodBox T U ε) (i j : Fin 3) :
    |(g⁻¹) i j| ≤ 3 * (2 * (1 + ε) ^ 2) ^ 2 := by
  obtain ⟨t, ⟨htV, _⟩, v, ⟨hvV, _⟩, rfl⟩ := hg
  rw [mul_inv_rev]
  have h := abs_mul_entries_le (b := 2 * (1 + ε) ^ 2) (d := 2 * (1 + ε) ^ 2)
    (by positivity) (by positivity)
    (fun i j => inv_entry_le hε hvV i j)
    (fun i j => inv_entry_le hε htV i j) i j
  have heq : 3 * ((2 * (1 + ε) ^ 2) * (2 * (1 + ε) ^ 2)) = 3 * (2 * (1 + ε) ^ 2) ^ 2 := by
    ring
  linarith [h, heq]

theorem prodBox_inv_mul_entries_bound {T U : Subgroup Work.EKLContract.SL3} {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ g ∈ Work.EKLProd.prodBox T U ε, ∀ g' ∈ Work.EKLProd.prodBox T U ε,
      ∀ i j : Fin 3,
        |((g'⁻¹ * g : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C := by
  refine ⟨3 * ((3 * (2 * (1 + ε) ^ 2) ^ 2) * (3 * (1 + ε) ^ 2)), ?_⟩
  intro g hg g' hg' i j
  exact abs_mul_entries_le (b := 3 * (2 * (1 + ε) ^ 2) ^ 2) (d := 3 * (1 + ε) ^ 2)
    (by positivity) (by positivity)
    (fun i j => prodBox_inv_entry_le hε hg' i j)
    (fun i j => prodBox_entry_le hε hg i j) i j

end Work.EKLProd
