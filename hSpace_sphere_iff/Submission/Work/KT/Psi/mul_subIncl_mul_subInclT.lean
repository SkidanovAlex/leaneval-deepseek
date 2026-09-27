import Mathlib
import Submission.Work.KT.Psi.SubIncl

namespace Work.KT.Psi

open Matrix

/-- Left absorption identity: if `N` vanishes on all pairs `(i,k)` with `¬ (pr i ∧ pr k)`, then
right multiplication by the inclusion matrix `subIncl A pr` followed by its transpose returns `N`.
Indeed `(N * subIncl A pr * (subIncl A pr)ᵀ) i k` is the sum of `N i k` over the (unique) index
`l : {i // pr i}` with `(l : ι) = k`; when `pr k` holds this is `N i k`, and otherwise `N i k = 0`
by hypothesis. -/
theorem mul_subIncl_mul_subInclT {A : Type} [Ring A] {ι : Type} [Fintype ι] [DecidableEq ι]
    {pr : ι → Prop} [DecidablePred pr] (N : Matrix ι ι A)
    (hdiag : ∀ i j : ι, ¬ (pr i ∧ pr j) → N i j = 0) :
    N * Work.KT.Psi.subIncl A pr * Matrix.transpose (Work.KT.Psi.subIncl A pr) = N := by
  ext i k
  rw [Matrix.mul_apply]
  by_cases hk : pr k
  · rw [Finset.sum_eq_single (⟨k, hk⟩ : {i // pr i})]
    · rw [mul_subIncl_apply, subIncl_transpose_apply, if_pos rfl, mul_one]
    · intro l _ hl
      have hne : ¬ ((l : ι) = k) := fun h => hl (Subtype.ext h)
      rw [mul_subIncl_apply, subIncl_transpose_apply, if_neg hne, mul_zero]
    · intro h; exact absurd (Finset.mem_univ (⟨k, hk⟩ : {i // pr i})) h
  · rw [hdiag i k (fun h => hk h.2), Finset.sum_eq_zero]
    intro l _
    have hne : ¬ ((l : ι) = k) := fun h => hk (h ▸ l.2)
    rw [mul_subIncl_apply, subIncl_transpose_apply, if_neg hne, mul_zero]

end Work.KT.Psi
