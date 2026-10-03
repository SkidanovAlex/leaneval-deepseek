import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.RankAPI.rk_le_right
import Submission.Work.ORHughesFree.RankAPI.rk_submatrix

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-- If the columns of a matrix are supported inside the range of an injective map
`g : Fin t → Fin K`, then the rank of the matrix is at most `t`.

Writing `M' = M.submatrix id g` for the `N × t` matrix of the selected columns, the
hypothesis says exactly that `M` is obtained from `M'` by reintroducing its columns at the
positions prescribed by `g` and filling the remaining columns with zeroes; in matrix terms
`M = M' * rowSel g`.  Hence `rk M ≤ rk M'` by (SMat2), and `rk M' ≤ t` because `M'` has only
`t` columns. -/
theorem rk_le_card_of_colSupport {R : Type*} [Ring R] (rk : SylvesterRank R) {N K t : ℕ}
    (g : Fin t → Fin K) (hg : Function.Injective g) (M : Matrix (Fin N) (Fin K) R)
    (hM : ∀ j, j ∉ Set.range g → ∀ i, M i j = 0) : rk.rk N K M ≤ t := by
  -- `rowSel g` is the `t × K` matrix with a `1` in position `(j, g j)`; its transpose
  -- reintroduces the selected columns at the positions prescribed by `g`.
  have hMB : M = M.submatrix id g * RankAPI.rowSel (R := R) g := by
    ext i j
    rw [Matrix.mul_apply]
    by_cases hj : j ∈ Set.range g
    · -- Column `j = g i'` is selected by the unique index `i'`.
      obtain ⟨i', hi'⟩ := hj
      rw [Finset.sum_eq_single i']
      · simp [Matrix.submatrix_apply, RankAPI.rowSel, hi']
      · intro b _ hb
        have hne : g b ≠ j := fun h => hb (hg (by rw [h, hi']))
        simp [RankAPI.rowSel, hne]
      · intro h; exact absurd (Finset.mem_univ i') h
    · -- Columns outside the range are zero, and contribute nothing to the product.
      have hsum : (∑ b, M.submatrix id g i b * RankAPI.rowSel (R := R) g b j) = 0 := by
        rw [Finset.sum_eq_zero]
        intro b _
        have hne : g b ≠ j := fun h => hj ⟨b, h⟩
        simp [RankAPI.rowSel, hne]
      rw [hsum, hM j hj i]
  rw [hMB]
  calc rk.rk N K (M.submatrix id g * RankAPI.rowSel (R := R) g)
      ≤ rk.rk N t (M.submatrix id g) := rk.rk_mul_le_left _ _
    _ ≤ t := RankAPI.rk_le_right rk _

end Work.ORHughesFree.NaturalExtension
