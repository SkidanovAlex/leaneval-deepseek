import Mathlib
import Submission.Work.Thom.exists_path_GL_pos

set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom

open Matrix

theorem exists_path_GL_pos_linear (n : ℕ)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hdet : 0 < LinearMap.det A.toLinearMap) :
    ∃ γ : C(unitInterval, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
      γ 0 = A ∧ γ 1 = 1 ∧ ∀ t : unitInterval, Function.Bijective (γ t) := by
  classical
  let b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let M : Matrix (Fin n) (Fin n) ℝ := LinearMap.toMatrix b b A.toLinearMap
  have hMlin : Matrix.toLin b b M = A.toLinearMap := toLin_toMatrix b b A.toLinearMap
  have hMdet : 0 < M.det := by
    rw [← LinearMap.det_toLin b M, hMlin]
    exact hdet
  obtain ⟨γ, hγ0, hγ1, hγinv⟩ := exists_path_GL_pos n M hMdet
  let Φ : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    ((LinearMap.toContinuousLinearMap :
        (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) ≃ₗ[ℝ]
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))).toLinearMap).comp
      (Matrix.toLin b b).toLinearMap
  have hΦcont : Continuous Φ := LinearMap.continuous_of_finiteDimensional Φ
  have hΦapply : ∀ N, ⇑(Φ N) = ⇑(Matrix.toLin b b N) := fun N => rfl
  have hΦM : Φ M = A := by
    show LinearMap.toContinuousLinearMap ((Matrix.toLin b b) M) = A
    rw [hMlin]
    exact (LinearMap.toContinuousLinearMap_eq_iff_eq_toLinearMap A.toLinearMap A).2 rfl
  have hΦ1 : Φ 1 = 1 := by
    show LinearMap.toContinuousLinearMap ((Matrix.toLin b b) 1) = 1
    rw [toLin_one, LinearMap.toContinuousLinearMap_eq_iff_eq_toLinearMap]
    ext x; simp
  refine ⟨⟨fun t => Φ (γ t), hΦcont.comp γ.continuous⟩, ?_, ?_, ?_⟩
  · show Φ (γ 0) = A
    rw [hγ0, hΦM]
  · show Φ (γ 1) = 1
    rw [hγ1, hΦ1]
  · intro t
    change Function.Bijective (⇑(Φ (γ t)))
    rw [hΦapply (γ t)]
    have h := (Matrix.toLinearEquiv b (γ t) (hγinv t)).bijective
    rwa [funext (fun x => Matrix.toLinearEquiv_apply b (γ t) (hγinv t) x)] at h

end Work.Thom
