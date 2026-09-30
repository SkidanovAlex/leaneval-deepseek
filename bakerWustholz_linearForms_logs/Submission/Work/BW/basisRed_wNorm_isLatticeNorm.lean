import Mathlib
import Submission.Work.BW.basisRed_defs
import Submission.Work.BW.wNorm_add_le
import Submission.Work.BW.wNorm_smul
import Submission.Work.BW.wNorm_eq_zero
import Submission.Work.BW.wNorm_finite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `wNorm A c` is a lattice norm

This file assembles the elementary properties proved in the companion modules
(`wNorm_nonneg`, `wNorm_smul`, `wNorm_add_le`, `wNorm_eq_zero`, `wNorm_finite`)
into the statement that the weighted `ℓ¹`-norm of the image under an integer
matrix `A` with nonzero determinant is a lattice norm in the sense of
`Work.BW.IsLatticeNorm`.
-/

namespace Work.BW

/-- `wNorm A c` is nonnegative whenever the weights are. -/
theorem wNorm_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i) (x : Fin n → ℝ) : 0 ≤ wNorm A c x := by
  unfold wNorm
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hc i) (abs_nonneg _))

theorem basisRed_wNorm_isLatticeNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det ≠ 0)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) :
    Work.BW.IsLatticeNorm (Work.BW.wNorm A c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact wNorm_nonneg A c (fun i => le_of_lt (hc i)) x
  · intro x
    exact wNorm_eq_zero A hA c hc x
  · intro t x
    exact wNorm_smul A c t x
  · intro x y
    exact wNorm_add_le A c (fun i => le_of_lt (hc i)) x y
  · intro t
    exact wNorm_finite A hA c hc t

end Work.BW
