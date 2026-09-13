import Mathlib
import Submission.Commons.Analysis.Calculus.FDeriv.hessianWithin_apply_second_partial
import Submission.Commons.Analysis.InnerProductSpace.eigen_basis_inner_apply

namespace Commons.Analysis.Calculus.FDeriv

open scoped RealInnerProductSpace in
open scoped BigOperators in
theorem iteratedFDeriv_two_eigen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {u : E → ℝ} {s : Set E} {x : E}
    (hs : IsOpen s) (hx : x ∈ s) (hu : ContDiffOn ℝ 2 u s)
    {T : E →L[ℝ] E} (hT : T.IsSymmetric) (hn : Module.finrank ℝ E = 4)
    (hTdef : T = InnerProductSpace.continuousLinearMapOfBilin
      (fderivWithin ℝ (fderivWithin ℝ u s) s x))
    (i j : Fin 4) :
    (iteratedFDeriv ℝ 2 u x) ![(hT.eigenvectorBasis hn) i, (hT.eigenvectorBasis hn) j] =
      hT.eigenvalues hn i * (if i = j then 1 else 0) := by
  -- The second iterated derivative is the Hessian quadratic form evaluated on the pair,
  -- which in turn is the inner product of the Hessian operator applied to the first vector.
  have h := hessianWithin_apply_second_partial (hT.eigenvectorBasis hn) hs hx hu i j
  rw [← hTdef] at h
  rw [← h]
  -- The eigenvector basis diagonalises the operator: `T (v i) = λ i • v i`.
  have hTv : T ((hT.eigenvectorBasis hn) i) =
      (hT.eigenvalues hn i : ℝ) • (hT.eigenvectorBasis hn) i :=
    hT.apply_eigenvectorBasis hn i
  rw [hTv, inner_smul_left, (hT.eigenvectorBasis hn).inner_eq_ite i j]
  simp

end Commons.Analysis.Calculus.FDeriv
