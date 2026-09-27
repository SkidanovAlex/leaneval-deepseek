import Mathlib
import Submission.Work.KT.Fund.kappa_hopf_defs

namespace Work.KT.Fund

open _root_.Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X]

/-- On the boundary circle `cHeight = √(1-‖z‖²)` vanishes. -/
private lemma bdryRestrict_cHeight : bdryRestrict X (cHeight X) = 0 := by
  ext p
  simp only [ContinuousMap.zero_apply, bdryRestrict_apply, cHeight, ContinuousMap.coe_mk]
  have hv : (((sphIncl p.2 : Ball ℂ) : ℂ)) = (p.2 : ℂ) := rfl
  rw [hv, norm_coe_sph p.2]
  norm_num

/-- On the boundary circle the normalising factor `(1 + cHeight)⁻¹` is `1`. -/
private lemma bdryRestrict_cHeightInv : bdryRestrict X (cHeightInv X) = 1 := by
  have h := congrArg (bdryRestrict X) (hUnit_inv_mul X)
  rw [map_mul, map_one] at h
  rw [map_add, map_one, bdryRestrict_cHeight X, add_zero, mul_one] at h
  exact h

/-- The lift `g = c/(1+s)` of the circle coordinate restricts on the boundary to `z`. -/
lemma bdryRestrict_gFun : bdryRestrict X (gFun X) = (zUnit X : C(X × Sph ℂ, ℂ)) := by
  have hbdr_cCoord : bdryRestrict X (cCoord X) = (zUnit X : C(X × Sph ℂ, ℂ)) := by
    ext p; rfl
  rw [gFun, map_mul, hbdr_cCoord, bdryRestrict_cHeightInv X, mul_one]

/-- The `1 × 1` entry of the scalar unit `zUnitMat` is the coordinate unit `z`. -/
private lemma zUnitMat_zero_zero :
    (zUnitMat X : Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ)) 0 0
      = (zUnit X : C(X × Sph ℂ, ℂ)) := by
  show (Matrix.diagonal (fun _ : Fin 1 => (zUnit X : C(X × Sph ℂ, ℂ)))) 0 0 = _
  rw [Matrix.diagonal_apply_eq]

theorem kappa_hopf_F0lift (X : Type) [TopologicalSpace X] :
    (F0 X).map (fun f => bdryRestrict X f)
      = (zUnitMat X : Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ)) := by
  apply Matrix.ext
  intro i j
  fin_cases i; fin_cases j
  rw [Matrix.map_apply]
  show bdryRestrict X (gFun X)
      = (zUnitMat X : Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ)) 0 0
  rw [zUnitMat_zero_zero X]
  exact bdryRestrict_gFun X

end

end Work.KT.Fund
