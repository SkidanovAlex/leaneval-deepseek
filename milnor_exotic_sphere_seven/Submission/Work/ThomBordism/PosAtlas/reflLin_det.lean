import Mathlib
import Submission.Work.ThomBordism.PosAtlas.Defs
import Submission.Work.Thom.Orientation.Reflection

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.PosAtlas

/-- The determinant of the coordinate reflection `reflCoord` of `Fin 9 → ℝ` (negating the
coordinate `1`) is `-1`: it is a product of the identity in the other coordinates and of
`-id` in the coordinate `1`. -/
theorem reflCoord_lin_det :
    LinearMap.det ((reflCoord : (Fin 9 → ℝ) ≃ₗ[ℝ] (Fin 9 → ℝ)) :
      (Fin 9 → ℝ) →ₗ[ℝ] (Fin 9 → ℝ)) = -1 := by
  have hfun : ((reflCoord : (Fin 9 → ℝ) ≃ₗ[ℝ] (Fin 9 → ℝ)) :
      (Fin 9 → ℝ) →ₗ[ℝ] (Fin 9 → ℝ))
      = LinearMap.pi (fun i : Fin 9 =>
          (if i = 1 then (-LinearMap.id) else LinearMap.id) ∘ₗ LinearMap.proj i) := by
    apply LinearMap.ext
    intro v
    funext i
    rw [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.coe_proj]
    have hv : ((reflCoord : (Fin 9 → ℝ) →ₗ[ℝ] (Fin 9 → ℝ)) v) = reflCoordFun v :=
      reflCoord_apply v
    rw [hv]
    by_cases hi : i = 1
    · subst hi
      rw [reflCoordFun_one]
      simp
    · rw [reflCoordFun_apply_of_ne _ hi]
      simp [hi]
  rw [hfun, LinearMap.det_pi]
  have hprod : ∀ i : Fin 9, LinearMap.det
      (if i = 1 then (-LinearMap.id : ℝ →ₗ[ℝ] ℝ) else LinearMap.id) =
      (if i = 1 then (-1 : ℝ) else 1) := by
    intro i
    by_cases hi : i = 1
    · subst hi
      rw [if_pos rfl, if_pos rfl]
      show LinearMap.det (-LinearMap.id : ℝ →ₗ[ℝ] ℝ) = -1
      rw [show (-LinearMap.id : ℝ →ₗ[ℝ] ℝ) = (-1 : ℝ) • LinearMap.id from by ext; simp]
      rw [LinearMap.det_smul, LinearMap.det_id, Module.finrank_self]
      norm_num
    · rw [if_neg hi, if_neg hi, LinearMap.det_id]
  rw [Finset.prod_congr rfl (fun i _ => hprod i)]
  rw [Finset.prod_eq_single (1 : Fin 9) (fun b _ hb => by simp [hb])
        (fun h => absurd (Finset.mem_univ _) h)]
  simp

theorem reflLin_det :
    LinearMap.det ((Work.ThomBordism.PosAtlas.reflLin :
      EuclideanSpace ℝ (Fin 9) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 9)) :
      EuclideanSpace ℝ (Fin 9) →ₗ[ℝ] EuclideanSpace ℝ (Fin 9)) < 0 := by
  let e : (Fin 9 → ℝ) →ₗ[ℝ] E9 :=
    (((EuclideanSpace.equiv (Fin 9) ℝ).symm).toLinearEquiv : (Fin 9 → ℝ) →ₗ[ℝ] E9)
  let f : E9 →ₗ[ℝ] (Fin 9 → ℝ) :=
    (((EuclideanSpace.equiv (Fin 9) ℝ)).toLinearEquiv : E9 →ₗ[ℝ] (Fin 9 → ℝ))
  have hconj : ((reflLin : E9 ≃ₗ[ℝ] E9) : E9 →ₗ[ℝ] E9) =
      e ∘ₗ ((reflCoord : (Fin 9 → ℝ) ≃ₗ[ℝ] (Fin 9 → ℝ)) :
        (Fin 9 → ℝ) →ₗ[ℝ] (Fin 9 → ℝ)) ∘ₗ f := by
    apply LinearMap.ext
    intro v
    rfl
  rw [hconj]
  have hle : LinearMap.det (e ∘ₗ ((reflCoord : (Fin 9 → ℝ) ≃ₗ[ℝ] (Fin 9 → ℝ)) :
      (Fin 9 → ℝ) →ₗ[ℝ] (Fin 9 → ℝ)) ∘ₗ f) = -1 := by
    have h := LinearMap.det_conj ((reflCoord : (Fin 9 → ℝ) ≃ₗ[ℝ] (Fin 9 → ℝ)) :
      (Fin 9 → ℝ) →ₗ[ℝ] (Fin 9 → ℝ)) (((EuclideanSpace.equiv (Fin 9) ℝ)).toLinearEquiv.symm)
    rw [reflCoord_lin_det] at h
    exact h
  rw [hle]
  norm_num

end Work.ThomBordism.PosAtlas
