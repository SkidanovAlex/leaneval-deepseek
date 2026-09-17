import Mathlib.Analysis.InnerProductSpace.ExteriorPower
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_det_smul
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal

set_option linter.unusedVariables false

open scoped BigOperators

namespace Commons.Analysis.InnerProductSpace

/-- The norm of the top-degree exterior power of a family `u` of `d` vectors in
`EuclideanSpace ℝ (Fin d)` equals the absolute value of the determinant of the matrix
whose columns are the coordinates of the `u j` in the standard basis. -/
lemma norm_iMulti_eq_abs_det {d : ℕ} (u : Fin d → EuclideanSpace ℝ (Fin d))
    (hu : LinearIndependent ℝ u) :
    ‖exteriorPower.ιMulti ℝ d u‖ =
      |(Matrix.of (fun (i j : Fin d) => (u j) i)).det| := by
  classical
  -- `e` is the standard orthonormal basis of `EuclideanSpace ℝ (Fin d)`
  let e : Fin d → EuclideanSpace ℝ (Fin d) :=
    fun i => (EuclideanSpace.basisFun (Fin d) ℝ) i
  -- `A` is the coordinate matrix of `u` in the standard basis:  A i j = (u j) i
  let A : Matrix (Fin d) (Fin d) ℝ := Matrix.of (fun (i j : Fin d) => (u j) i)
  -- The standard basis is orthonormal.
  have horth : Orthonormal ℝ e := by
    dsimp [e]
    exact (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal
  -- Each `u j` is the linear combination of the standard basis vectors `e i` with
  -- coefficients `A i j`.
  have hcoord : ∀ j : Fin d,
      u j = (Finset.univ : Finset (Fin d)).sum (fun i : Fin d => A i j • e i) := by
    intro j
    calc
      u j = ∑ i : Fin d,
          ((EuclideanSpace.basisFun (Fin d) ℝ).repr (u j)).ofLp i •
            ((EuclideanSpace.basisFun (Fin d) ℝ) i) := by
        exact (OrthonormalBasis.sum_repr (EuclideanSpace.basisFun (Fin d) ℝ) (u j)).symm
      _ = ∑ i : Fin d, (u j).ofLp i • e i := by
        simp [e]
      _ = ∑ i : Fin d, A i j • e i := by rfl
  -- Wedge products transform by the determinant
  have hwedge : exteriorPower.ιMulti ℝ d u =
      A.det • exteriorPower.ιMulti ℝ d e := by
    exact Commons.LinearAlgebra.ExteriorPower.iMulti_det_smul (E := EuclideanSpace ℝ (Fin d))
      (u := e) (A := A) (w := u) (hw := hcoord)
  -- The norm of the top exterior power of an orthonormal family is one.
  have hnorm_e : ‖exteriorPower.ιMulti ℝ d e‖ = 1 := by
    have hsq : ‖exteriorPower.ιMulti ℝ d e‖ ^ 2 = 1 := by
      calc
        ‖exteriorPower.ιMulti ℝ d e‖ ^ 2 =
            inner ℝ (exteriorPower.ιMulti ℝ d e) (exteriorPower.ιMulti ℝ d e) := by
          exact (real_inner_self_eq_norm_sq (exteriorPower.ιMulti ℝ d e)).symm
        _ = (Matrix.gram ℝ e).det := by
          rw [exteriorPower.inner_ιMulti_self]
        _ = (1 : Matrix (Fin d) (Fin d) ℝ).det := by
          rw [Matrix.gram_eq_one_iff_orthonormal.mpr horth]
        _ = 1 := by simp
    have hnonneg : 0 ≤ ‖exteriorPower.ιMulti ℝ d e‖ := norm_nonneg _
    rcases (sq_eq_one_iff.mp hsq) with h | h
    · exact h
    · linarith
  calc
    ‖exteriorPower.ιMulti ℝ d u‖ =
        ‖A.det • exteriorPower.ιMulti ℝ d e‖ := by rw [hwedge]
    _ = ‖A.det‖ * ‖exteriorPower.ιMulti ℝ d e‖ := by rw [norm_smul]
    _ = |A.det| * ‖exteriorPower.ιMulti ℝ d e‖ := by rw [Real.norm_eq_abs]
    _ = |A.det| * 1 := by rw [hnorm_e]
    _ = |A.det| := by simp
    _ = |(Matrix.of (fun (i j : Fin d) => (u j) i)).det| := by
      simp [A]

end Commons.Analysis.InnerProductSpace