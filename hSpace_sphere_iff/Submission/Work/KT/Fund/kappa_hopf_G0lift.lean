import Mathlib
import Submission.Work.KT.Fund.kappa_hopf_defs

/-!
# `Work.KT.Fund.kappa_hopf_G0lift` — `G₀` restricts to `z⁻¹` on the boundary circle

The upper-disc lift of the coordinate `z` is `F₀ = !![g]` with `g = c/(1+s)` (`c` the disc
coordinate, `s = √(1-‖c‖²)` the height); the lower-disc lift of `z⁻¹` is `G₀ = !![star g]`.
Since `F₀` restricts to `z` on the boundary circle (`Work.KT.Fund.kappa_hopf_F0lift`), the
lower lift `G₀ = star F₀` restricts there to `star z = z⁻¹`.  This is the second half of the
clutching data for the Hopf line bundle used in `Work.KT.Fund.kappa_hopf`.

The proof is an explicit pointwise computation on `X × S¹`: the height `s` vanishes on the
boundary (`cHeight_bdry`), hence `1 + s = 1` is invertible with inverse `1`
(`cHeightInv_bdry`), so `g = c/(1+s)` becomes the coordinate `z = p.2`
(`gFun_bdry`); finally `star z = z⁻¹` because `‖z‖ = 1` (`Complex.inv_eq_conj`).
-/

namespace Work.KT.Fund

open _root_.Matrix

noncomputable section

variable (X : Type) [TopologicalSpace X]

/-- The `1 × 1` scalar matrix ring homomorphism, viewed as a monoid homomorphism so that
`Units.map` may be applied to it. -/
private def scMatHom : C(X × Sph ℂ, ℂ) →* Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ) :=
  (Matrix.scalar (Fin 1) : C(X × Sph ℂ, ℂ) →+* Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ))

private lemma zUnitMat_eq_map : zUnitMat X = Units.map (scMatHom X) (zUnit X) := rfl

/-- The height `s = √(1-‖c‖²)` vanishes on the boundary circle. -/
private lemma cHeight_bdry (p : X × Sph ℂ) : cHeight X (p.1, sphIncl p.2) = 0 := by
  rw [cHeight]
  simp only [ContinuousMap.coe_mk]
  rw [show (((sphIncl p.2 : Ball ℂ)) : ℂ) = (p.2 : ℂ) from rfl, norm_coe_sph p.2]
  norm_num

/-- `1 + s = 1` on the boundary circle, so its inverse is `1`. -/
private lemma cHeightInv_bdry (p : X × Sph ℂ) : cHeightInv X (p.1, sphIncl p.2) = 1 := by
  have h := congrFun (congrArg DFunLike.coe (hUnit_inv_mul X)) (p.1, sphIncl p.2)
  simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply, ContinuousMap.one_apply] at h
  rw [cHeight_bdry X p, add_zero] at h
  simpa using h

/-- The lift `g = c/(1+s)` restricts to the coordinate `z = p.2` on the boundary circle. -/
private lemma gFun_bdry (p : X × Sph ℂ) : gFun X (p.1, sphIncl p.2) = (p.2 : ℂ) := by
  rw [gFun, ContinuousMap.mul_apply]
  rw [show cCoord X (p.1, sphIncl p.2) = (p.2 : ℂ) from rfl, cHeightInv_bdry X p, mul_one]

/-- On the boundary circle the lower lift `G₀ = star g` restricts to `z⁻¹`. -/
private lemma bdryRestrict_star_gFun :
    bdryRestrict X (star (gFun X)) = (↑((zUnit X)⁻¹) : C(X × Sph ℂ, ℂ)) := by
  ext p
  rw [bdryRestrict_apply, ContinuousMap.star_apply, gFun_bdry X p]
  rw [show (↑((zUnit X)⁻¹) : C(X × Sph ℂ, ℂ)) p = ((p.2 : ℂ))⁻¹ from rfl]
  rw [show star ((p.2 : ℂ)) = ((p.2 : ℂ))⁻¹ from by
    rw [Complex.inv_eq_conj (norm_coe_sph p.2)]
    rfl]

/-- The inverse of the coordinate unit matrix is the `1 × 1` matrix with entry `z⁻¹`. -/
private lemma zUnitMat_inv_eq :
    ((zUnitMat X)⁻¹ : Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ))
      = !![(↑((zUnit X)⁻¹) : C(X × Sph ℂ, ℂ))] := by
  rw [Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit]
  rw [show (↑((zUnitMat X)⁻¹) : Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ))
      = ↑(Units.map (scMatHom X) ((zUnit X)⁻¹)) from by
    rw [show (zUnitMat X)⁻¹ = Units.map (scMatHom X) ((zUnit X)⁻¹) from by
      rw [zUnitMat_eq_map X]
      exact (map_inv (Units.map (scMatHom X)) (zUnit X)).symm]]
  rw [Units.coe_map]
  rw [show (scMatHom X) (↑((zUnit X)⁻¹)) = (Matrix.scalar (Fin 1) : C(X × Sph ℂ, ℂ) →+*
      Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ)) (↑((zUnit X)⁻¹)) from rfl, Matrix.scalar_apply]
  ext i j
  fin_cases i; fin_cases j
  simp

theorem kappa_hopf_G0lift (X : Type) [TopologicalSpace X] :
    (G0 X).map (fun f => bdryRestrict X f)
      = ((zUnitMat X)⁻¹ : Matrix (Fin 1) (Fin 1) C(X × Sph ℂ, ℂ)) := by
  rw [zUnitMat_inv_eq X]
  rw [show (G0 X).map (fun f => bdryRestrict X f) = !![bdryRestrict X (star (gFun X))] from by
    rw [show G0 X = !![star (gFun X)] from rfl]
    ext i j
    fin_cases i; fin_cases j
    rfl]
  rw [bdryRestrict_star_gFun X]

end

end Work.KT.Fund
