import Mathlib
import Submission.Work.Mostow.detInterpExpansion

/-!
# Setup for the smooth no-retraction theorem

Definitions used in `Work.Mostow.noRetractionSmooth`: the standard orthonormal basis of
`ℝⁿ = EuclideanSpace ℝ (Fin n)`, the matrix of a continuous linear endomorphism in that basis,
and the coordinate projections onto the coordinates in a finite set.
-/

namespace Work.Mostow

open Metric Matrix

noncomputable section

/-- `E n` is `ℝⁿ` with its Euclidean structure. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The standard orthonormal basis of `ℝⁿ`, as a plain `Module.Basis`. -/
def stdBasis (n : ℕ) : Module.Basis (Fin n) ℝ (E n) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

/-- The matrix (in the standard basis) of a continuous linear endomorphism of `ℝⁿ`. -/
def matOf_NoRetractionDefs (n : ℕ) (A : E n →L[ℝ] E n) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix (stdBasis n) (stdBasis n) (A : E n →ₗ[ℝ] E n)

/-- The diagonal matrix with `1` exactly at the coordinates in `s`.  It is the matrix of the
orthogonal projection onto the span of the coordinates in `s`. -/
def projMat (n : ℕ) (s : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => if i ∈ s then (1 : ℝ) else 0)

/-- The continuous linear endomorphism of `ℝⁿ` with matrix `projMat n s`. -/
def projOp (n : ℕ) (s : Finset (Fin n)) : E n →L[ℝ] E n :=
  (Matrix.toLin (stdBasis n) (stdBasis n) (projMat n s)).toContinuousLinearMap

@[simp] lemma matOf_add (n : ℕ) (A B : E n →L[ℝ] E n) :
    matOf_NoRetractionDefs n (A + B) = matOf_NoRetractionDefs n A + matOf_NoRetractionDefs n B :=
  (LinearMap.toMatrix (stdBasis n) (stdBasis n)).map_add A B

@[simp] lemma matOf_sub (n : ℕ) (A B : E n →L[ℝ] E n) :
    matOf_NoRetractionDefs n (A - B) = matOf_NoRetractionDefs n A - matOf_NoRetractionDefs n B :=
  (LinearMap.toMatrix (stdBasis n) (stdBasis n)).map_sub A B

@[simp] lemma matOf_mul (n : ℕ) (A B : E n →L[ℝ] E n) :
    matOf_NoRetractionDefs n (A * B) = matOf_NoRetractionDefs n A * matOf_NoRetractionDefs n B := by
  have h : ((A * B : E n →L[ℝ] E n) : E n →ₗ[ℝ] E n) =
      (A : E n →ₗ[ℝ] E n) * (B : E n →ₗ[ℝ] E n) := rfl
  rw [matOf_NoRetractionDefs, h, LinearMap.toMatrix_mul]
  rfl

@[simp] lemma matOf_one (n : ℕ) : matOf_NoRetractionDefs n (1 : E n →L[ℝ] E n) = 1 := by
  have h : ((1 : E n →L[ℝ] E n) : E n →ₗ[ℝ] E n) = 1 := rfl
  rw [matOf_NoRetractionDefs, h, LinearMap.toMatrix_one]

@[simp] lemma matOf_smul (n : ℕ) (c : ℝ) (A : E n →L[ℝ] E n) :
    matOf_NoRetractionDefs n (c • A) = c • matOf_NoRetractionDefs n A :=
  (LinearMap.toMatrix (stdBasis n) (stdBasis n)).map_smul c A

@[simp] lemma matOf_projOp (n : ℕ) (s : Finset (Fin n)) : matOf_NoRetractionDefs n (projOp n s) = projMat n s := by
  rw [matOf_NoRetractionDefs, projOp, LinearMap.coe_toContinuousLinearMap]
  exact LinearMap.toMatrix_toLin _ _ _

lemma matOf_det (n : ℕ) (A : E n →L[ℝ] E n) :
    (matOf_NoRetractionDefs n A).det = LinearMap.det (A : E n →ₗ[ℝ] E n) :=
  LinearMap.det_toMatrix (stdBasis n) (A : E n →ₗ[ℝ] E n)

lemma matOf_zero (n : ℕ) : matOf_NoRetractionDefs n (0 : E n →L[ℝ] E n) = 0 := by
  have h : ((0 : E n →L[ℝ] E n) : E n →ₗ[ℝ] E n) = 0 := rfl
  rw [matOf_NoRetractionDefs, h, map_zero]

lemma matOf_injective (n : ℕ) {A B : E n →L[ℝ] E n} (h : matOf_NoRetractionDefs n A = matOf_NoRetractionDefs n B) : A = B := by
  have h2 : (LinearMap.toMatrix (stdBasis n) (stdBasis n)).symm (matOf_NoRetractionDefs n A)
      = (LinearMap.toMatrix (stdBasis n) (stdBasis n)).symm (matOf_NoRetractionDefs n B) := by rw [h]
  simpa [matOf_NoRetractionDefs] using h2

/-- The determinant of a continuous linear endomorphism of `ℝⁿ` is the determinant of its matrix
in the standard basis (defeq form of `matOf_det`). -/
lemma det_eq_matOf_det (n : ℕ) (A : E n →L[ℝ] E n) : A.det = (matOf_NoRetractionDefs n A).det :=
  (matOf_det n A).symm

lemma det_one_clm (n : ℕ) : (1 : E n →L[ℝ] E n).det = 1 := by
  rw [det_eq_matOf_det, matOf_one, Matrix.det_one]

lemma projOp_empty (n : ℕ) : projOp n ∅ = 0 := by
  refine matOf_injective n ?_
  rw [matOf_projOp, matOf_zero]
  ext i j
  simp [projMat]

lemma projOp_univ (n : ℕ) : projOp n Finset.univ = 1 := by
  refine matOf_injective n ?_
  rw [matOf_projOp, matOf_one]
  ext i j
  simp [projMat]

/-- `detInterpExpansion` phrased with `projMat`. -/
theorem detInterpExpansion' (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    Matrix.det ((1 - t) • (1 : Matrix (Fin n) (Fin n) ℝ) + t • M)
      = ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
          t ^ s.card * (1 - t) ^ (n - s.card) *
            Matrix.det (projMat n s * M + (1 - projMat n s)) := by
  simpa only [projMat] using detInterpExpansion n M t

/-- The row-wise multilinear expansion of `det ((1 - t) • 1 + t • A)`, transported to the level of
continuous linear endomorphisms of `ℝⁿ`. -/
theorem det_interp_op (n : ℕ) (A : E n →L[ℝ] E n) (t : ℝ) :
    ((1 - t) • (1 : E n →L[ℝ] E n) + t • A).det
      = ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
          t ^ s.card * (1 - t) ^ (n - s.card) * (projOp n s * A + (1 - projOp n s)).det := by
  have hmat : matOf_NoRetractionDefs n ((1 - t) • (1 : E n →L[ℝ] E n) + t • A)
      = (1 - t) • (1 : Matrix (Fin n) (Fin n) ℝ) + t • matOf_NoRetractionDefs n A := by
    rw [matOf_add, matOf_smul, matOf_smul, matOf_one]
  rw [det_eq_matOf_det, hmat, detInterpExpansion']
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  rw [← matOf_projOp n s, ← matOf_mul, ← matOf_one, ← matOf_sub, ← matOf_add,
    ← det_eq_matOf_det]

/-- The coefficient functions in the expansion of `det ((1 - t) • 1 + t • (fderiv f))`. -/
def phi_NoRetractionDefs (n : ℕ) (f : E n → E n) (s : Finset (Fin n)) : E n → ℝ :=
  fun x => (projOp n s * fderiv ℝ f x + (1 - projOp n s)).det

theorem continuous_phi (n : ℕ) (f : E n → E n) (hf : ContDiff ℝ 1 f) (s : Finset (Fin n)) :
    Continuous (phi_NoRetractionDefs n f s) := by
  have h1 : Continuous fun x : E n => fderiv ℝ f x :=
    hf.continuous_fderiv (by norm_num)
  have h2 : Continuous fun A : E n →L[ℝ] E n => projOp n s * A + (1 - projOp n s) :=
    (((ContinuousLinearMap.compL ℝ (E n) (E n) (E n)) (projOp n s)).continuous).add
      continuous_const
  exact ContinuousLinearMap.continuous_det.comp (h2.comp h1)

lemma phi_empty (n : ℕ) (f : E n → E n) : phi_NoRetractionDefs n f ∅ = fun _ => 1 := by
  funext x
  rw [phi_NoRetractionDefs, projOp_empty]
  simp [det_eq_matOf_det, matOf_one]

end

end Work.Mostow
