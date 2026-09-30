import Mathlib
import Submission.Work.Homology.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The integral homology of the additive circle `ℝ/ℤ`

`AddCircle (1 : ℝ) = ℝ/ℤ` is the circle, so its integral singular homology is `ℤ` in degrees
`0` and `1` and vanishes otherwise:

```
Work.PieceHomology.intHomology_addCircle :
  H_k(AddCircle 1; ℤ) ≅ ℤ   for k = 0, 1,      ≅ 0  otherwise.
```

The proof is a transport of the sphere computation `Work.Homology.singHomology_sphere`
(`H_k(Sⁿ; ℤ) ≅ ℤ` for `k = 0, n`, zero otherwise) along the homeomorphism
`AddCircle 1 ≃ₜ S¹`, which factors as

* `AddCircle.homeomorphCircle` (Mathlib): `ℝ/ℤ ≃ₜ Circle`, the unit circle in `ℂ`, and
* `circleSphereHomeo` below: the unit circle in `ℂ` ≃ the unit sphere of
  `EuclideanSpace ℝ (Fin 2)`, induced by the linear isometry equivalence
  `Complex.orthonormalBasisOneI.repr : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)` (which maps
  `Metric.sphere 0 1` onto `Metric.sphere 0 1` by `LinearIsometryEquiv.image_sphere`).
-/

open CategoryTheory

namespace Work.PieceHomology

noncomputable section

/-- The unit circle in `ℂ` is homeomorphic to the unit sphere of `EuclideanSpace ℝ (Fin 2)`,
through the linear isometry equivalence `ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)` given by the
orthonormal basis `1, I`; an isometry equivalence maps `Metric.sphere 0 1` onto itself. -/
def circleSphereHomeo :
    Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 where
  toFun x := ⟨Complex.orthonormalBasisOneI.repr x, by
    have hx := x.2
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx ⊢
    exact (Complex.orthonormalBasisOneI.repr.norm_map x).trans hx⟩
  invFun y := ⟨Complex.orthonormalBasisOneI.repr.symm y, by
    have hy := y.2
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hy ⊢
    exact (Complex.orthonormalBasisOneI.repr.symm.norm_map y).trans hy⟩
  left_inv x := Subtype.ext (Complex.orthonormalBasisOneI.repr.symm_apply_apply (x : ℂ))
  right_inv y :=
    Subtype.ext (Complex.orthonormalBasisOneI.repr.apply_symm_apply (y : EuclideanSpace ℝ (Fin 2)))
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact Complex.orthonormalBasisOneI.repr.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact Complex.orthonormalBasisOneI.repr.symm.continuous.comp continuous_subtype_val

/-- **The additive circle is the `1`-sphere**: `ℝ/ℤ ≃ₜ S¹`, as the composite of the canonical
homeomorphism `AddCircle T ≃ₜ Circle` (`AddCircle.homeomorphCircle`) with `circleSphereHomeo`. -/
def addCircleSphHomeo :
    (TopCat.of (AddCircle (1 : ℝ))) ≃ₜ Work.Homology.Sph 1 :=
  (AddCircle.homeomorphCircle one_ne_zero).trans circleSphereHomeo

/-- **The integral homology of the circle** `AddCircle (1 : ℝ) = ℝ/ℤ`: it is `ℤ` in degrees `0`
and `1` and vanishes in all other degrees. -/
theorem intHomology_addCircle (k : ℕ) :
    Nonempty (LeanEval.Topology.intHomology k (TopCat.of (AddCircle (1 : ℝ))) ≅
      (if k = 0 ∨ k = 1 then ModuleCat.of ℤ ℤ else ModuleCat.of ℤ PUnit)) := by
  obtain ⟨e⟩ := Work.Homology.intHomology_iso_of_homeomorph k addCircleSphHomeo
  obtain ⟨f⟩ := Work.Homology.singHomology_sphere 1 k (by norm_num)
  exact ⟨e ≪≫ eqToIso (Work.Homology.intHomology_eq k (Work.Homology.Sph 1)) ≪≫ f⟩

end

end Work.PieceHomology
