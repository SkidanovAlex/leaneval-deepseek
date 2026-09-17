import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Matrix.PosDef

open Matrix

namespace Commons.LinearAlgebra.Matrix

set_option maxHeartbeats 1600000

/-- For a real matrix, `star` (conjugate transpose) coincides with the transpose. -/
private lemma star_eq_transpose_real {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : star M = Mᵀ := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

/-- The determinant of the linear map attached to a real matrix is the determinant of the matrix. -/
private lemma det_toEuclideanLin {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) :
    LinearMap.det (Matrix.toEuclideanLin M) = M.det := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact LinearMap.det_toLin _ M

/-- `(M x) ⬝ᵥ (M x) = x ⬝ᵥ (Mᵀ M x)` for a real square matrix `M`. -/
private lemma dotProduct_self_mulVec {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    (M *ᵥ v) ⬝ᵥ (M *ᵥ v) = v ⬝ᵥ (Mᵀ *ᵥ (M *ᵥ v)) := by
  rw [Matrix.dotProduct_mulVec v Mᵀ (M *ᵥ v), Matrix.vecMul_transpose]

/-- The squared norm of `toEuclideanLin M x` is the quadratic form of `Mᵀ M`. -/
private lemma norm_sq_toEuclideanLin {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖Matrix.toEuclideanLin M x‖ ^ 2 = x.ofLp ⬝ᵥ (Mᵀ *ᵥ (M *ᵥ x.ofLp)) := by
  have h1 : ‖Matrix.toEuclideanLin M x‖ ^ 2 = (M *ᵥ x.ofLp) ⬝ᵥ (M *ᵥ x.ofLp) := by
    rw [EuclideanSpace.norm_sq_eq, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.ofLp_toLpLin 2 2 M x, Matrix.toLin'_apply, Real.norm_eq_abs, sq, abs_mul_abs_self]
  rw [h1, dotProduct_self_mulVec]

theorem exists_linearMap_norm_sq_eq_sqrt_det {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosDef) :
    ∃ φ : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d),
      (∀ x : EuclideanSpace ℝ (Fin d), ‖φ x‖ ^ 2 = ∑ i, x i * (A.mulVec (fun j => x j)) i) ∧
      |LinearMap.det φ| = Real.sqrt A.det := by
  classical
  -- Build a real matrix `M` with `Mᵀ * M = A` from the spectral theorem.
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin d) (Fin d) ℝ, Mᵀ * M = A := by
    let U : Matrix (Fin d) (Fin d) ℝ := hA.isHermitian.eigenvectorUnitary
    let e : Fin d → ℝ := hA.isHermitian.eigenvalues
    let s : Fin d → ℝ := fun i => Real.sqrt (RCLike.ofReal (e i))
    refine ⟨diagonal s * star U, ?_⟩
    have hspec : A = U * diagonal (RCLike.ofReal ∘ e) * star U := by
      have h := hA.isHermitian.spectral_theorem
      rw [Unitary.conjStarAlgAut_apply] at h
      exact h
    have hsstar : star s = s := by
      funext i; simp [s]
    have hss : (fun i => s i * s i) = (RCLike.ofReal ∘ e) := by
      funext i
      simp only [Function.comp_apply, s]
      rw [Real.mul_self_sqrt (RCLike.ofReal_nonneg.mpr (le_of_lt (hA.eigenvalues_pos i)))]
    have hMT : (diagonal s * star U)ᵀ = star (diagonal s * star U) :=
      (star_eq_transpose_real _).symm
    have hM' : (diagonal s * star U)ᵀ = U * diagonal s := by
      rw [hMT, star_mul, star_star, star_eq_transpose_real, Matrix.diagonal_transpose]
    calc (diagonal s * star U)ᵀ * (diagonal s * star U)
        = (U * diagonal s) * (diagonal s * star U) := by rw [hM']
      _ = U * (diagonal s * diagonal s) * star U := by noncomm_ring
      _ = U * diagonal (RCLike.ofReal ∘ e) * star U := by
            rw [Matrix.diagonal_mul_diagonal, hss]
      _ = A := hspec.symm
  -- Determinant identity.
  have hsq : M.det * M.det = A.det := by
    have h := congrArg Matrix.det hM
    rwa [Matrix.det_mul, Matrix.det_transpose] at h
  have habs : |M.det| = Real.sqrt A.det := by
    rw [← hsq, Real.sqrt_mul_self_eq_abs]
  refine ⟨Matrix.toEuclideanLin M, fun x => ?_, ?_⟩
  · rw [norm_sq_toEuclideanLin, Matrix.mulVec_mulVec, hM]
    rw [dotProduct]
  · rw [det_toEuclideanLin, habs]

end Commons.LinearAlgebra.Matrix