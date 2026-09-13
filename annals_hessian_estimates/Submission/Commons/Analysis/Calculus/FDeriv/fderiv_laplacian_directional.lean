import Mathlib.Analysis.InnerProductSpace.Laplacian
import Submission.Commons.Analysis.Calculus.FDeriv.secondPartial_directional_deriv
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_three_swap

open scoped Topology

namespace Commons.Analysis.Calculus.FDeriv

open scoped RealInnerProductSpace in
open scoped BigOperators in
theorem fderiv_laplacian_directional {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E) {s : Set E}
    {u : E → ℝ} {x : E} (hs : IsOpen s) (hx : x ∈ s) (hu : ContDiffOn ℝ 3 u s) (i : ι) :
    fderiv ℝ (fun z => (Laplacian.laplacian u) z) x (v i) =
      ∑ j : ι, (iteratedFDeriv ℝ 3 u x) ![v j, v j, v i] := by
  have hxmem : s ∈ 𝓝 x := hs.mem_nhds hx
  have huAt : ContDiffAt ℝ 3 u x := hu.contDiffAt hxmem
  -- The Laplacian is the sum of the second partial derivatives along an orthonormal basis.
  have hlap : (fun z => (Laplacian.laplacian u) z)
      = fun z => ∑ j : ι, (iteratedFDeriv ℝ 2 u z) ![v j, v j] := by
    funext z
    simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u v]
  rw [hlap, fderiv_fun_sum]
  · -- Differentiate the finite sum term by term and evaluate at `v i`.
    rw [sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    -- `fderiv` of the second partial derivative is the third derivative, then permute arguments.
    rw [secondPartial_directional_deriv hs hx hu (v j) (v j) (v i)]
    exact (iteratedFDeriv_three_swap hs hx hu (v i) (v j) (v j)).1.trans
      (iteratedFDeriv_three_swap hs hx hu (v j) (v i) (v j)).2
  · -- Each summand is differentiable at `x`.
    intro j _
    exact ((huAt.iteratedFDeriv_right (m := 1) (i := 2) (by norm_num)).differentiableAt
      one_ne_zero).continuousMultilinear_apply_const ![v j, v j]

end Commons.Analysis.Calculus.FDeriv