import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.RankAPI.rk_le_left
import Submission.Work.ORHughesFree.RankAPI.rk_submatrix

namespace Work.ORHughesFree.NaturalExtension

/-- If the rows of a matrix are supported inside the range of an injective map
`g : Fin t → Fin N`, then the rank of the matrix is at most `t`.

Writing `M' = M.submatrix g id` for the `t × K` matrix of the selected rows, the hypothesis
says exactly that `M` is obtained from `M'` by reintroducing its rows at the positions
prescribed by `g` and filling the remaining rows with zeroes; in matrix terms
`M = colSel g * M'`.  Hence `rk M ≤ rk M'` by (SMat2), and `rk M' ≤ t` because `M'` has only
`t` rows. -/
theorem rk_le_card_of_rowSupport {R : Type*} [Ring R] (rk : SylvesterRank R) {N K t : ℕ}
    (g : Fin t → Fin N) (hg : Function.Injective g) (M : Matrix (Fin N) (Fin K) R)
    (hM : ∀ i, i ∉ Set.range g → ∀ j, M i j = 0) : rk.rk N K M ≤ t := by
  -- `colSel g` is the `N × t` matrix with a `1` in position `(g j, j)`; it reintroduces the
  -- selected rows at the positions prescribed by `g`.
  have hC : RankAPI.colSel (R := R) g * (M.submatrix g id) = M := by
    ext i j
    rw [Matrix.mul_apply]
    by_cases hi : i ∈ Set.range g
    · -- Row `i = g a` is selected by the unique index `a`.
      obtain ⟨a, rfl⟩ := hi
      rw [Finset.sum_eq_single a]
      · simp [RankAPI.colSel]
      · intro b _ hb
        have hne : ¬ (g a = g b) := fun h => hb (hg h).symm
        simp [RankAPI.colSel, hne]
      · intro h; exact absurd (Finset.mem_univ a) h
    · -- Rows outside the range are zero, and contribute nothing to the product.
      have hne : ∀ a : Fin t, ¬ (i = g a) := fun a h => hi ⟨a, h.symm⟩
      have hterm : ∀ a : Fin t,
          RankAPI.colSel (R := R) g i a * M.submatrix g id a j = 0 := by
        intro a
        rw [RankAPI.colSel]
        simp [hne a]
      rw [Finset.sum_eq_zero (fun a _ => hterm a)]
      exact (hM i hi j).symm
  calc rk.rk N K M = rk.rk N K (RankAPI.colSel (R := R) g * (M.submatrix g id)) := by rw [hC]
    _ ≤ rk.rk t K (M.submatrix g id) := rk.rk_mul_le_right _ _
    _ ≤ t := RankAPI.rk_le_left rk _

end Work.ORHughesFree.NaturalExtension
