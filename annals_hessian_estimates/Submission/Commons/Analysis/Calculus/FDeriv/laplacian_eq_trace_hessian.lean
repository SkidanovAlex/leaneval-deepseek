import Mathlib
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_apply_second_partial
import Submission.Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials

namespace Commons.Analysis.Calculus.FDeriv

open scoped RealInnerProductSpace in
theorem laplacian_eq_trace_hessian {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {s : Set E} {u : E → ℝ} {x : E} (hs : IsOpen s) (hx : x ∈ s)
    (hu : ContDiffOn ℝ 2 u s) (v : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E) :
    (Laplacian.laplacian u) x = LinearMap.trace ℝ E
      ((InnerProductSpace.continuousLinearMapOfBilin
        (fderivWithin ℝ (fderivWithin ℝ u s) s x)) : E →ₗ[ℝ] E) := by
  rw [laplacian_eq_sum_second_partials v u x, LinearMap.trace_eq_sum_inner _ v]
  apply Finset.sum_congr rfl
  intro i _
  show ((bilinearIteratedFDerivTwo ℝ u x) (v i)) (v i) =
    ⟪v i, (InnerProductSpace.continuousLinearMapOfBilin
        (fderivWithin ℝ (fderivWithin ℝ u s) s x)) (v i)⟫
  rw [real_inner_comm, hessianWithin_apply_second_partial v hs hx hu i i,
      bilinearIteratedFDerivTwo_eq_iteratedFDeriv]

end Commons.Analysis.Calculus.FDeriv
