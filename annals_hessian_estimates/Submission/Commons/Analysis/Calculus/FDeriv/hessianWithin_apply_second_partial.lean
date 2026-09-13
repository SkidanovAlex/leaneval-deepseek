import Mathlib
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_eq_hessian
import Submission.Commons.Analysis.Calculus.FDeriv.hessianMatrix_apply_second_partial

namespace Commons.Analysis.Calculus.FDeriv

open scoped RealInnerProductSpace in
theorem hessianWithin_apply_second_partial {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]
    (v : OrthonormalBasis ι ℝ E) {s : Set E} {u : E → ℝ} {y : E} (hs : IsOpen s) (hy : y ∈ s)
    (hu : ContDiffOn ℝ 2 u s) (i j : ι) :
    ⟪(InnerProductSpace.continuousLinearMapOfBilin
        (fderivWithin ℝ (fderivWithin ℝ u s) s y)) (v i), v j⟫ =
      (iteratedFDeriv ℝ 2 u y) ![v i, v j] := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  rw [hessianWithin_eq_hessian (hs.mem_nhds hy)]
  rw [hessianMatrix_apply_second_partial, bilinearIteratedFDerivTwo_eq_iteratedFDeriv]

end Commons.Analysis.Calculus.FDeriv
