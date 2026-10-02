import Mathlib
import Submission.Work.ThomBordism.PontryaginThom.Orthogonal

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Topology

namespace Work.ThomBordism.PontryaginThom

open Work.ThomBordism.Grassmann

noncomputable section

/-- **The Gram matrix `Aᵀ A` of a real matrix with injective `mulVec` has nonzero determinant.**
It is positive definite (`Matrix.PosDef.conjTranspose_mul_self`), hence invertible. -/
theorem gram_det_ne_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : Function.Injective A.mulVec) : (Matrix.transpose A * A).det ≠ 0 := by
  have hPos : (Matrix.transpose A * A : Matrix (Fin n) (Fin n) ℝ).PosDef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.PosDef.conjTranspose_mul_self A hA
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hPos.isUnit)

/-- The matrix of a continuous family of frames of `ℝ^{8+k}` is continuous. -/
theorem continuous_frameMat_family {X : Type*} [TopologicalSpace X] {k : ℕ}
    (F : X → Fin 8 → Euc (8 + k)) (hF : Continuous F) :
    Continuous fun x => frameMat (F x) := by
  refine continuous_matrix fun r l => ?_
  exact (continuous_apply r).comp
    ((eucToFun (8 + k)).continuous.comp ((continuous_apply l).comp hF))

/-- **The orthogonal projection matrix depends continuously on a continuous independent family of
frames.**  Where the frame is independent the Gram matrix `AᵀA` is invertible, and matrix inversion
is continuous on invertible matrices (`continuousOn_matrix_inv`); `orthMat` is a product of
continuous factors. -/
theorem continuous_orthMat_family {X : Type*} [TopologicalSpace X] {k : ℕ}
    (F : X → Fin 8 → Euc (8 + k)) (hF : Continuous F)
    (hind : ∀ x, LinearIndependent ℝ (F x)) :
    Continuous fun x => orthMat (F x) := by
  have hG : Continuous fun x => frameMat (F x) := continuous_frameMat_family F hF
  have hGram : Continuous fun x =>
      Matrix.transpose (frameMat (F x)) * frameMat (F x) :=
    hG.matrix_transpose.matrix_mul hG
  have hdet : ∀ x, (Matrix.transpose (frameMat (F x)) * frameMat (F x)).det ≠ 0 :=
    fun x => gram_det_ne_zero (frameMat (F x))
      (frameMat_mulVec_injective (F x) (hind x))
  have hinv : Continuous fun x =>
      (Matrix.transpose (frameMat (F x)) * frameMat (F x))⁻¹ := by
    have h := (continuousOn_matrix_inv 8).comp (hGram.continuousOn (s := Set.univ))
      (fun x _ => hdet x)
    rwa [continuousOn_univ] at h
  exact (hG.matrix_mul hinv).matrix_mul hG.matrix_transpose

/-- The value of `orthProj` on a basis vector is the corresponding column of `orthMat`. -/
theorem orthProj_single {k : ℕ} (A : Fin 8 → Euc (8 + k)) (j : Fin (8 + k)) :
    orthProj A (Pi.single j 1) = fun r => orthMat A r j := by
  rw [orthProj, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  funext r
  exact Matrix.col_apply (orthMat A) j r

theorem continuousOn_orthProjCLM {X : Type} [TopologicalSpace X] {k : ℕ}
    (F : X → Fin 8 → Work.ThomBordism.PontryaginThom.Euc (8 + k)) (s : Set X)
    (hF : ContinuousOn F s) (hind : ∀ x ∈ s, LinearIndependent ℝ (F x)) :
    ContinuousOn (fun x =>
      LinearMap.toContinuousLinearMap (Work.ThomBordism.PontryaginThom.orthProj (F x))) s := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun p : s =>
    LinearMap.toContinuousLinearMap (orthProj (F p.1)))
  rw [continuous_toContinuousLinearMap_iff]
  intro j
  have hmat : Continuous fun p : s => orthMat (F p.1) :=
    continuous_orthMat_family (fun p : s => F p.1) hF.domRestrict
      (fun p => hind p.1 p.2)
  rw [show (fun p : s => orthProj (F p.1) (Pi.single j 1))
      = fun p : s => fun r => orthMat (F p.1) r j from
    funext fun p => orthProj_single (F p.1) j]
  exact continuous_pi_iff.mpr fun r => hmat.matrix_elem r j

end

end Work.ThomBordism.PontryaginThom
