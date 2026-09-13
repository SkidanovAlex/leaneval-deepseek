import Mathlib.Analysis.InnerProductSpace.Dual

namespace Commons.Analysis.InnerProductSpace

open scoped RealInnerProductSpace in
open scoped BigOperators in
theorem norm_sq_eq_sum_sq_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E) (f : E →L[ℝ] ℝ) :
    ‖f‖ ^ 2 = ∑ k : ι, (f (v k)) ^ 2 :=
  v.norm_dual f

end Commons.Analysis.InnerProductSpace