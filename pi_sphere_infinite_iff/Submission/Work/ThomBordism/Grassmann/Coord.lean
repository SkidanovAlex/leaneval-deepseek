import Submission.Work.ThomBordism.Grassmann.Frame
import Submission.Work.ThomBordism.Grassmann.Linear

set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The transition functions of the tautological bundle

The translation of a `k × k` matrix into a continuous linear endomorphism of `Amb k = ℝ^k`
(`Work.ThomBordism.Grassmann.matLin`), its basic functoriality (`matLin_mul`, `matLin_one`), the
continuity of the matrix inverse on the open set `det ≠ 0`, and the resulting continuity of the
transition function `coordChangeAux` of the chart `U_S` to the chart `U_T`.

The transition function of the tautological bundle from the chart `S` to the chart `T` is the
composite
`p_T ∘ (p_S)⁻¹ : ℝ^S ≅ ℝ^k`,
whose matrix is `frameMatrix T f * (frameMatrix S f)⁻¹`; it is defined (with the junk value `0`
outside the overlap) as `coordChangeAux S T`.
-/

namespace Work.ThomBordism.Grassmann

open scoped Topology

noncomputable section

variable {k m : ℕ}

/-! ## Matrices as continuous linear endomorphisms of `ℝ^k` -/

/-- The **continuous linear endomorphism of `Amb k = ℝ^k` given by a matrix `M`**: the transpose
convention is immaterial here, but this is `v ↦ M.mulVec v`, i.e. `(M v)_i = ∑ j, M i j v j`. -/
def matLin (M : Matrix (Fin k) (Fin k) ℝ) : Amb k →L[ℝ] Amb k :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (M.mulVec (WithLp.ofLp v))
      map_add' := by
        intro v w
        ext i
        simp only [WithLp.ofLp_add, Matrix.mulVec_apply, Matrix.row_apply, dotProduct,
          Pi.add_apply]
        rw [Finset.sum_congr rfl fun x _ => mul_add (M i x) (v.ofLp x) (w.ofLp x),
          Finset.sum_add_distrib]
      map_smul' := by
        intro c v
        ext i
        simp only [WithLp.ofLp_smul, Matrix.mulVec_apply, Matrix.row_apply, dotProduct,
          Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring }

@[simp] theorem matLin_apply (M : Matrix (Fin k) (Fin k) ℝ) (v : Amb k) :
    matLin M v = WithLp.toLp 2 (M.mulVec (WithLp.ofLp v)) := rfl

/-- `matLin` is additive in the matrix. -/
theorem matLin_add (M N : Matrix (Fin k) (Fin k) ℝ) : matLin (M + N) = matLin M + matLin N := by
  ext v i
  simp only [matLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_add, Matrix.mulVec_apply,
    Matrix.row_apply, dotProduct, ContinuousLinearMap.add_apply, Pi.add_apply, Matrix.add_apply]
  rw [Finset.sum_congr rfl fun x _ => add_mul (M i x) (N i x) (v.ofLp x),
    Finset.sum_add_distrib]

/-- `matLin` is homogeneous in the matrix. -/
theorem matLin_smul (c : ℝ) (M : Matrix (Fin k) (Fin k) ℝ) :
    matLin (c • M) = c • matLin M := by
  ext v i
  simp only [matLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul, Matrix.mulVec_apply,
    Matrix.row_apply, dotProduct, ContinuousLinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.smul_apply]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- `matLin` is a linear map of the matrix. -/
def matLinLM : Matrix (Fin k) (Fin k) ℝ →ₗ[ℝ] (Amb k →L[ℝ] Amb k) where
  toFun := matLin
  map_add' := matLin_add
  map_smul' := matLin_smul

/-- `matLin` depends continuously on the matrix. -/
theorem continuous_matLin : Continuous (fun M : Matrix (Fin k) (Fin k) ℝ => matLin M) :=
  (matLinLM (k := k)).continuous_of_finiteDimensional

/-- `matLin` is multiplicative. -/
theorem matLin_mul (M N : Matrix (Fin k) (Fin k) ℝ) :
    matLin (M * N) = (matLin M).comp (matLin N) := by
  ext v
  simp [matLin_apply, Matrix.mulVec_mulVec]

@[simp] theorem matLin_one : matLin (1 : Matrix (Fin k) (Fin k) ℝ) = 1 := by
  ext v
  simp [matLin_apply, Matrix.one_mulVec]

/-! ## Continuity of the matrix inverse -/

theorem continuousOn_matrix_inv (k : ℕ) :
    ContinuousOn (fun M : Matrix (Fin k) (Fin k) ℝ => M⁻¹) {M | M.det ≠ 0} := by
  intro M hM
  refine (continuousAt_matrix_inv M ?_).continuousWithinAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ hM

end

end Work.ThomBordism.Grassmann
