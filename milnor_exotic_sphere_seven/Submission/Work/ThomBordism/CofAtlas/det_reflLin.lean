import Mathlib
import Submission.Work.ThomBordism.CofAtlas.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.CofAtlas

/-- The determinant of the coordinate-negation of the `1`-st coordinate of `Fin 9 → ℝ` is `-1`. -/
theorem det_reflCoord :
    LinearMap.det (reflCoord : (Fin 9 → ℝ) →ₗ[ℝ] (Fin 9 → ℝ)) = -1 := by
  rw [← LinearMap.det_toMatrix' (reflCoord : (Fin 9 → ℝ) →ₗ[ℝ] (Fin 9 → ℝ))]
  have hmat : LinearMap.toMatrix' (reflCoord : (Fin 9 → ℝ) →ₗ[ℝ] (Fin 9 → ℝ)) =
      Matrix.diagonal (fun i : Fin 9 => if i = 1 then (-1 : ℝ) else 1) := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    show reflCoordFun (Pi.single j 1) i =
      Matrix.diagonal (fun i : Fin 9 => if i = 1 then (-1 : ℝ) else 1) i j
    rw [reflCoordFun, Function.update_apply, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  rw [hmat, Matrix.det_diagonal]
  rw [Finset.prod_eq_single (1 : Fin 9)]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ (1 : Fin 9)) h

/-- The reflection `reflLin` of `ℝ⁹` has the same determinant as the coordinate negation
`reflCoord` of `Fin 9 → ℝ` (the two are conjugate under `EuclideanSpace.equiv`). -/
theorem det_reflLin_eq_det_reflCoord :
    LinearMap.det (reflLin : E9 →ₗ[ℝ] E9) =
      LinearMap.det (reflCoord : (Fin 9 → ℝ) →ₗ[ℝ] (Fin 9 → ℝ)) := by
  let e : (Fin 9 → ℝ) ≃ₗ[ℝ] E9 := ((EuclideanSpace.equiv (Fin 9) ℝ).toLinearEquiv).symm
  have key := LinearEquiv.det_conj (R := ℝ) (M := Fin 9 → ℝ) (M' := E9)
    (f := reflCoord) (e := e)
  have h1 : (e.symm.trans reflCoord).trans e = reflLin := by ext x; rfl
  rw [h1] at key
  have key2 : ((LinearEquiv.det reflLin : ℝˣ) : ℝ) =
      ((LinearEquiv.det reflCoord : ℝˣ) : ℝ) :=
    congrArg (fun u : ℝˣ => (u : ℝ)) key
  simpa [LinearEquiv.coe_det] using key2

theorem det_reflLin :
    LinearMap.det (Work.ThomBordism.CofAtlas.reflE.toLinearMap
      : EuclideanSpace ℝ (Fin 9) →ₗ[ℝ] EuclideanSpace ℝ (Fin 9)) = -1 := by
  have hcoe : (reflE.toLinearMap : E9 →ₗ[ℝ] E9) = (reflLin : E9 →ₗ[ℝ] E9) := rfl
  rw [hcoe, det_reflLin_eq_det_reflCoord, det_reflCoord]

end Work.ThomBordism.CofAtlas
