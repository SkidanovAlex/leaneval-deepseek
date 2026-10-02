import Submission.Work.ThomBordism.PontryaginThom.matrix_orthogonalProjection
import Submission.Work.ThomBordism.PontryaginThom.FramesRange

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# The orthogonal complement of the plane of a frame

The transition functions of the complement bundle (`ComplementBundle.lean`) glue with the
*coordinate* complement `range (complInj S)` of `Complement.lean`, which depends on the chart index
`S`; the splitting `TV ⊕ ν ≅ ε^{k+8}` of `Splitting.lean` needs in addition that the insertion `I`
is valued in a complement that is the **same subspace in every chart** (`Pi_agree`).  The canonical
such complement is the *orthogonal* complement of the plane.

This file provides it, in coordinates on `ℝ^{8+k}`: for a frame `A : Fin 8 → Euc (8+k)`,

* `frameMat A : Matrix (Fin (8+k)) (Fin 8) ℝ` is its matrix, with
  `frameMat A *ᵥ v = coeffMap A v`;
* `orthMat A = A (AᵀA)⁻¹ Aᵀ` (`matrix_orthogonalProjection`) is the orthogonal projection onto the
  plane, `orthProj A` its linear map, and `orthInj A = 1 - orthProj A` the insertion of the
  orthogonal complement;
* `orthProj A` fixes the plane (`orthProj_coeffMap`), hence `orthInj A` kills it
  (`orthInj_coeffMap`), and `ker (orthInj A) = range (coeffMap A)` (`ker_orthInj`).

Because `orthInj A` depends only on the *plane* (through the standard inner product), the insertion
`I_S = orthInj A ∘ complInj S` is chart-independent on the plane — the two-line identity
`u - complInj S (planeProj A S h u) ∈ range (coeffMap A)` gives `orthInj A (I_S (P_S u)) = orthInj A u`
for every `S`, which is `Pi_agree` for the data of the assembly.
-/

open scoped Topology

namespace Work.ThomBordism.PontryaginThom

open Work.ThomBordism.Grassmann

noncomputable section

variable {k : ℕ}

/-- The `(8+k) × 8` matrix of a frame, in the standard coordinates of `ℝ^{8+k}`. -/
def frameMat (A : Fin 8 → Euc (8 + k)) : Matrix (Fin (8 + k)) (Fin 8) ℝ :=
  fun r l => eucToFun (8 + k) (A l) r

/-- The entries of `mulVec` for a rectangular matrix (notation-free). -/
theorem mulVec_apply_sum' {l m : ℕ} (M : Matrix (Fin l) (Fin m) ℝ) (v : Fin m → ℝ)
    (i : Fin l) : M.mulVec v i = ∑ j, M i j * v j := rfl

/-- `mulVec` of a product (notation-free). -/
theorem mulVec_mulVec_eq {l m n : ℕ} (M : Matrix (Fin l) (Fin m) ℝ)
    (N : Matrix (Fin m) (Fin n) ℝ) (v : Fin n → ℝ) :
    (M * N).mulVec v = M.mulVec (N.mulVec v) := by
  funext i
  simp only [mulVec_apply_sum', Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- The matrix of the frame acts by `coeffMap`. -/
theorem frameMat_mulVec_eq_coeffMap (A : Fin 8 → Euc (8 + k)) (v : Fin 8 → ℝ) :
    (frameMat A).mulVec v = coeffMap A v := by
  funext r
  rw [coeffMap_apply, mulVec_apply_sum']
  simp only [frameMat, eucToFun_apply, EuclideanSpace.coe_proj]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- An independent frame has injective coordinate map. -/
theorem coeffMap_injective_of_linearIndependent (A : Fin 8 → Euc (8 + k))
    (hA : LinearIndependent ℝ A) : Function.Injective (coeffMap A) := by
  intro v w hvw
  have h0 : coeffMap A (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have h1 : (∑ l, (v - w) l • A l) = 0 := by
    have := congrArg (funToEuc (8 + k)) h0
    simpa only [coeffMap_eq_sum, map_zero, funToEuc_eucToFun] using this
  have h2 := (Fintype.linearIndependent_iff.mp hA) (v - w) h1
  funext l
  have := h2 l
  simp only [Pi.sub_apply] at this
  exact sub_eq_zero.mp this

/-- The matrix of an independent frame has injective `mulVec`. -/
theorem frameMat_mulVec_injective (A : Fin 8 → Euc (8 + k)) (hA : LinearIndependent ℝ A) :
    Function.Injective (frameMat A).mulVec := by
  intro v w hvw
  refine coeffMap_injective_of_linearIndependent A hA ?_
  rw [← frameMat_mulVec_eq_coeffMap, ← frameMat_mulVec_eq_coeffMap, hvw]

/-- **The orthogonal projection onto the plane of a frame**, as a matrix
(`A (AᵀA)⁻¹ Aᵀ`). -/
def orthMat (A : Fin 8 → Euc (8 + k)) : Matrix (Fin (8 + k)) (Fin (8 + k)) ℝ :=
  frameMat A * (Matrix.transpose (frameMat A) * frameMat A)⁻¹ * Matrix.transpose (frameMat A)

/-- The orthogonal projection onto the plane of a frame, as a linear map. -/
def orthProj (A : Fin 8 → Euc (8 + k)) : (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin (8 + k) → ℝ) :=
  (orthMat A).mulVecLin

/-- The insertion of the orthogonal complement of the plane of a frame. -/
def orthInj (A : Fin 8 → Euc (8 + k)) : (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin (8 + k) → ℝ) :=
  LinearMap.id - orthProj A

theorem orthMat_mul_frameMat (A : Fin 8 → Euc (8 + k)) (hA : LinearIndependent ℝ A) :
    orthMat A * frameMat A = frameMat A :=
  (matrix_orthogonalProjection (frameMat A) (frameMat_mulVec_injective A hA)).1

theorem orthMat_idem (A : Fin 8 → Euc (8 + k)) (hA : LinearIndependent ℝ A) :
    orthMat A * orthMat A = orthMat A :=
  (matrix_orthogonalProjection (frameMat A) (frameMat_mulVec_injective A hA)).2.1

theorem orthMat_transpose (A : Fin 8 → Euc (8 + k)) (hA : LinearIndependent ℝ A) :
    Matrix.transpose (orthMat A) = orthMat A :=
  (matrix_orthogonalProjection (frameMat A) (frameMat_mulVec_injective A hA)).2.2.1

theorem transpose_frameMat_mul_orthInj (A : Fin 8 → Euc (8 + k)) (hA : LinearIndependent ℝ A) :
    Matrix.transpose (frameMat A) * (1 - orthMat A) = 0 :=
  (matrix_orthogonalProjection (frameMat A) (frameMat_mulVec_injective A hA)).2.2.2

/-- The orthogonal projection fixes the plane. -/
theorem orthProj_coeffMap (A : Fin 8 → Euc (8 + k)) (hA : LinearIndependent ℝ A)
    (v : Fin 8 → ℝ) : orthProj A (coeffMap A v) = coeffMap A v := by
  have h1 : (orthMat A).mulVec ((frameMat A).mulVec v) = (frameMat A).mulVec v := by
    rw [← mulVec_mulVec_eq, orthMat_mul_frameMat A hA]
  rw [orthProj, Matrix.mulVecLin_apply, ← frameMat_mulVec_eq_coeffMap A v, h1]

/-- The insertion of the orthogonal complement kills the plane. -/
theorem orthInj_coeffMap (A : Fin 8 → Euc (8 + k)) (hA : LinearIndependent ℝ A)
    (v : Fin 8 → ℝ) : orthInj A (coeffMap A v) = 0 := by
  rw [orthInj, LinearMap.sub_apply, LinearMap.id_apply, orthProj_coeffMap A hA v, sub_self]

/-- The range of the orthogonal projection is contained in the plane. -/
theorem range_orthProj_le (A : Fin 8 → Euc (8 + k)) :
    LinearMap.range (orthProj A) ≤ LinearMap.range (coeffMap A) := by
  rintro w ⟨u, rfl⟩
  refine ⟨((Matrix.transpose (frameMat A) * frameMat A)⁻¹).mulVec
    ((Matrix.transpose (frameMat A)).mulVec u), ?_⟩
  rw [orthProj, Matrix.mulVecLin_apply, orthMat, mulVec_mulVec_eq, mulVec_mulVec_eq,
    frameMat_mulVec_eq_coeffMap]

/-- The kernel of the insertion of the orthogonal complement is the plane. -/
theorem ker_orthInj (A : Fin 8 → Euc (8 + k)) (hA : LinearIndependent ℝ A) :
    LinearMap.ker (orthInj A) = LinearMap.range (coeffMap A) := by
  apply le_antisymm
  · intro u hu
    rw [LinearMap.mem_ker] at hu
    have hu' : u = orthProj A u := by
      rw [orthInj, LinearMap.sub_apply, LinearMap.id_apply] at hu
      exact sub_eq_zero.mp hu
    rw [hu']
    exact range_orthProj_le A ⟨u, rfl⟩
  · rintro w ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    exact orthInj_coeffMap A hA v

/-- The Gram matrix of an independent frame is invertible. -/
theorem isUnit_gram_det (A : Fin 8 → Euc (8 + k)) (hA : LinearIndependent ℝ A) :
    IsUnit ((Matrix.transpose (frameMat A) * frameMat A).det) := by
  have hPos : ((Matrix.transpose (frameMat A) * frameMat A) : Matrix (Fin 8) (Fin 8) ℝ).PosDef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.PosDef.conjTranspose_mul_self (frameMat A) (frameMat_mulVec_injective A hA)
  exact (Matrix.isUnit_iff_isUnit_det _).mp hPos.isUnit

/-- **The frame coordinates of a vector**: the least-squares coordinates of the orthogonal
projection of the vector onto the plane of the frame (`(AᵀA)⁻¹Aᵀ`). -/
def frameCoords (A : Fin 8 → Euc (8 + k)) : (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin 8 → ℝ) :=
  ((Matrix.transpose (frameMat A) * frameMat A)⁻¹).mulVecLin.comp
    (Matrix.transpose (frameMat A)).mulVecLin

/-- The frame coordinates of a plane vector are its coordinates in the frame. -/
theorem frameCoords_coeffMap (A : Fin 8 → Euc (8 + k)) (hA : LinearIndependent ℝ A)
    (v : Fin 8 → ℝ) : frameCoords A (coeffMap A v) = v := by
  have h1 : (Matrix.transpose (frameMat A)).mulVec ((frameMat A).mulVec v)
      = (Matrix.transpose (frameMat A) * frameMat A).mulVec v :=
    (mulVec_mulVec_eq _ _ _).symm
  rw [frameCoords, LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
    ← frameMat_mulVec_eq_coeffMap A v, h1, ← mulVec_mulVec_eq,
    Matrix.nonsing_inv_mul _ (isUnit_gram_det A hA)]
  simp

/-- The plane vector of the frame coordinates is the orthogonal projection. -/
theorem coeffMap_frameCoords (A : Fin 8 → Euc (8 + k)) (hA : LinearIndependent ℝ A)
    (u : Fin (8 + k) → ℝ) : coeffMap A (frameCoords A u) = orthProj A u := by
  rw [frameCoords, LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply,
    ← frameMat_mulVec_eq_coeffMap, orthProj, Matrix.mulVecLin_apply, orthMat,
    mulVec_mulVec_eq, mulVec_mulVec_eq]

end

end Work.ThomBordism.PontryaginThom