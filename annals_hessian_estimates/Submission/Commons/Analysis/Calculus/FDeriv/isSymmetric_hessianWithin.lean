import Mathlib
import Submission.Commons.Analysis.Calculus.FDeriv.isSymmetric_hessian
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_eq_hessian

namespace Commons.Analysis.Calculus.FDeriv

theorem isSymmetric_hessianWithin {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {s : Set E} {u : E → ℝ} {x : E} (hs : IsOpen s) (hx : x ∈ s)
    (hu : ContDiffOn ℝ 2 u s) :
    (InnerProductSpace.continuousLinearMapOfBilin
      (fderivWithin ℝ (fderivWithin ℝ u s) s x)).IsSymmetric := by
  rw [hessianWithin_eq_hessian (hs.mem_nhds hx)]
  exact isSymmetric_hessian hs hx hu

end Commons.Analysis.Calculus.FDeriv
