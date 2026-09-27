import Mathlib
import Submission.Work.EKLProd.prodBox_inv_mul_entries_bound

namespace Work.EKLProd

/-- The product box `prodBox T U ε` is entrywise bounded, both for its elements and for the
entries of their inverses.  Explicitly the constant
`max (3 (1+ε)²) (3 (2 (1+ε)²)²)` works: elements of the box are products of two elements of
`V ε`, hence have entries bounded by `3 (1+ε)²` (`prodBox_entry_le`), while the inverse is the
product of the inverses of the two factors, whose entries are each bounded by `2 (1+ε)²`
(`prodBox_inv_entry_le`). -/
theorem prodBox_entries_bound {T U : Subgroup Work.EKLContract.SL3} {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, (∀ g ∈ Work.EKLProd.prodBox T U ε, ∀ i j : Fin 3,
        |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C) ∧
      (∀ g ∈ Work.EKLProd.prodBox T U ε, ∀ i j : Fin 3,
        |((g⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C) := by
  refine ⟨max (3 * (1 + ε) ^ 2) (3 * (2 * (1 + ε) ^ 2) ^ 2), ?_, ?_⟩
  · intro g hg i j
    exact le_trans (prodBox_entry_le hε hg i j) (le_max_left _ _)
  · intro g hg i j
    exact le_trans (prodBox_inv_entry_le hε hg i j) (le_max_right _ _)

end Work.EKLProd
