import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Dual

namespace Commons.Analysis.Calculus.FDeriv

/-- The Hessian of a `C²` function on an open set is symmetric, in the sense that the
symmetric bilinear form `fderiv ℝ (fderiv ℝ u) x` gives rise to a symmetric operator. -/
theorem isSymmetric_hessian {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {u : E → ℝ} {s : Set E} {x : E} (hs : IsOpen s) (hx : x ∈ s)
    (hu : ContDiffOn ℝ 2 u s) :
    (InnerProductSpace.continuousLinearMapOfBilin (fderiv ℝ (fderiv ℝ u) x)).IsSymmetric := by
  -- The second derivative of a `C²` function is symmetric.
  have hx2 : ContDiffAt ℝ 2 u x := hu.contDiffAt (hs.mem_nhds hx)
  have h : IsSymmSndFDerivAt ℝ u x := hx2.isSymmSndFDerivAt (by simp)
  intro v w
  -- `continuousLinearMapOfBilin` identifies the bilinear form with the operator it represents.
  change inner ℝ (InnerProductSpace.continuousLinearMapOfBilin (fderiv ℝ (fderiv ℝ u) x) v) w =
    inner ℝ v (InnerProductSpace.continuousLinearMapOfBilin (fderiv ℝ (fderiv ℝ u) x) w)
  rw [InnerProductSpace.continuousLinearMapOfBilin_apply, real_inner_comm,
    InnerProductSpace.continuousLinearMapOfBilin_apply]
  exact h v w

end Commons.Analysis.Calculus.FDeriv