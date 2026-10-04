import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Pinch

open Finset

/-- The scalar curvature of the Kulkarni–Nomizu product:
`scal (A ∧ B) = 2 * (tr A * tr B - tr (A B))`. -/
theorem scalAlg_knProd (n : ℕ) (A B : Fin n → Fin n → ℝ) :
    Submission.Diff.Alg.scalAlg (Work.Diff.Alg.Pinch.knProd A B) =
      2 * ((∑ i, A i i) * (∑ j, B j j) - ∑ i, ∑ j, A i j * B j i) := by
  simp only [Submission.Diff.Alg.scalAlg, Work.Diff.Alg.Pinch.knProd]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- The four contracted pieces: `∑ᵢⱼ AᵢᵢBⱼⱼ = tr A · tr B`, the two middle pieces are both
  -- `∑ᵢⱼ AᵢⱼBⱼᵢ` (by symmetry of summation), and `∑ᵢⱼ AⱼⱼBᵢᵢ = tr A · tr B` again.
  have hPQ : (∑ x, ∑ x_1, A x x * B x_1 x_1) = (∑ i, A i i) * (∑ j, B j j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  have hS : (∑ x, ∑ x_1, A x_1 x * B x x_1) = (∑ i, ∑ j, A i j * B j i) := by
    rw [Finset.sum_comm]
  have hQP : (∑ x, ∑ x_1, A x_1 x_1 * B x x) = (∑ i, A i i) * (∑ j, B j j) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  rw [hPQ, hS, hQP]
  ring

end Work.Diff.Alg.Pinch
