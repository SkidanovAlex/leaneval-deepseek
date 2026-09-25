import Mathlib
import Submission.Work.LT.gb_rank_defs

namespace Work.LT

/-- (file `Submission/Work/LT/gb_dot_matVec_transpose.lean`, inside `namespace Work.LT` / `namespace GB`, importing `Submission.Work.LT.gb_rank_defs`) The transpose is the adjoint of multiplication by `x` for the dot product: `⟨xᵀ u, v⟩ = ⟨u, x v⟩`.  Here `GB.dot u v = ∑ i, u i * v i` and `GB.matVec x v = fun i => ∑ j, x (i,j) * v j`. -/
lemma gb_dot_matVec_transpose {D : ℕ} (x : Fin D × Fin D → ZMod 2) (u v : Fin D → ZMod 2) :
    GB.dot (GB.matVec (GB.matTranspose x) u) v = GB.dot u (GB.matVec x v) := by
  -- Both sides unfold to a double sum over the entries of `x`; the two sums
  -- differ only by the interchange of the two summation indices and the
  -- commutativity of multiplication in `ZMod 2`.
  simp only [GB.dot, GB.matVec, GB.matTranspose, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

end Work.LT
