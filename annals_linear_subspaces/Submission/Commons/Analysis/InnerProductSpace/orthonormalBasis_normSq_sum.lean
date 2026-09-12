import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators

namespace Commons.Analysis.InnerProductSpace

/-- For an orthonormal basis `b` of a real inner product space `E`, the square of the norm
of `x` equals the sum of the squares of its coordinates in the basis. -/
lemma orthonormalBasis_normSq_sum {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (x : E) :
    ‖x‖ ^ 2 = ∑ i : ι, (b.repr x i) ^ 2 := by
  calc
    ‖x‖ ^ 2 = ∑ i : ι, ‖(inner ℝ (b i) x)‖ ^ 2 := (b.sum_sq_norm_inner_right x).symm
    _ = ∑ i : ι, (inner ℝ (b i) x) ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro i _
      simp [sq_abs]
    _ = ∑ i : ι, (b.repr x i) ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro i _
      congr 1
      rw [b.repr_apply_apply]

end Commons.Analysis.InnerProductSpace