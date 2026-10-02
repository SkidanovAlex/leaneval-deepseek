import Mathlib
import Submission.Work.CharacteristicClasses.S3Ops
import Submission.Work.Cohomology.sphereSelfDegree_functor

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The degree of a self-map of `S³`, in the quaternionic model

The degree machinery of `Submission/Work/Cohomology/Degree.lean` is set up for the sphere
`Sⁿ ⊆ EuclideanSpace ℝ (Fin (n+1))`.  The characteristic-class chapter works in the quaternionic
model `S3 = Submission.Milnor.QS3 = {q : ℍ // ‖q‖ = 1}`, because that is where quaternion
multiplication (the group structure of `Sp(1)`) is available.  This file transports the degree to
that model:

* `s3Homeo` — the linear isometry `ℍ ≅ ℝ⁴` restricts to a homeomorphism `S3 ≅ S³ ⊆ ℝ⁴`;
* `s3HomologyIso` — the resulting isomorphism `H₃(S3; ℤ) ≅ ℤ`;
* `s3SelfDegree` — the degree of a self-map of `S3`, defined exactly as
  `Work.Cohomology.sphereSelfDegree` but for `S3`.

The structural properties (identity, composition, homotopy invariance, constants, and the
H-space additivity `deg (q ↦ f q * g q) = deg f + deg g`, the *Hopf formula*) are proved in the
files `qs3SelfDegree_*` of this directory.

Note (used repeatedly later): the degree does not depend on the *choice* of the isomorphism
`H₃(S3; ℤ) ≅ ℤ`, since replacing `e` by `-e` flips both the generator and the evaluation — so
`deg (f) = e (f_* (e⁻¹ 1))` is canonically determined by `H₃(S3; ℤ) ≅ ℤ` alone.
-/

namespace Work.CharacteristicClasses

open scoped Topology
open Metric

noncomputable section

/-- The linear isometry `ℍ ≃ₗᵢ[ℝ] ℝ⁴` restricts to a homeomorphism of the unit spheres. -/
def s3Homeo : S3 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 where
  toFun x := ⟨Quaternion.linearIsometryEquivTuple (x : Quaternion ℝ), by
    rw [Metric.mem_sphere, dist_zero_right, Quaternion.linearIsometryEquivTuple.norm_map]
    exact Submission.Milnor.norm_coe x⟩
  invFun y := ⟨Quaternion.linearIsometryEquivTuple.symm (y : EuclideanSpace ℝ (Fin 4)), by
    rw [Metric.mem_sphere, dist_zero_right, Quaternion.linearIsometryEquivTuple.symm.norm_map]
    simpa [Metric.mem_sphere, dist_zero_right] using y.2⟩
  left_inv x := Subtype.ext (Quaternion.linearIsometryEquivTuple.symm_apply_apply (x : Quaternion ℝ))
  right_inv y :=
    Subtype.ext (Quaternion.linearIsometryEquivTuple.apply_symm_apply (y : EuclideanSpace ℝ (Fin 4)))
  continuous_toFun :=
    Continuous.subtype_mk
      (Quaternion.linearIsometryEquivTuple.continuous.comp continuous_subtype_val)
      (fun x => by
        simp only [Function.comp_apply]
        rw [Metric.mem_sphere, dist_zero_right, Quaternion.linearIsometryEquivTuple.norm_map]
        exact Submission.Milnor.norm_coe x)
  continuous_invFun :=
    Continuous.subtype_mk
      (Quaternion.linearIsometryEquivTuple.symm.continuous.comp continuous_subtype_val)
      (fun y => by
        simp only [Function.comp_apply]
        rw [Metric.mem_sphere, dist_zero_right, Quaternion.linearIsometryEquivTuple.symm.norm_map]
        simpa [Metric.mem_sphere, dist_zero_right] using y.2)

/-- The third homology of `S3` (the quaternionic `S³`) is infinite cyclic. -/
noncomputable def s3HomologyIso :
    (Work.Cohomology.singularChains ℤ (TopCat.of S3)).homology 3 ≅ ModuleCat.of ℤ ℤ :=
  CategoryTheory.Iso.trans
    (Work.Cohomology.homologyIso_of_homotopyEquiv s3Homeo.toHomotopyEquiv 3).some
    (Work.Cohomology.sphereHomologyTop 3 (by norm_num)).some

/-- The chosen generator `[S³]` of `H₃(S3; ℤ) ≅ ℤ`. -/
noncomputable def s3HomologyGen :
    (Work.Cohomology.singularChains ℤ (TopCat.of S3)).homology 3 :=
  s3HomologyIso.inv.hom (1 : ℤ)

/-- **The degree of a self-map of `S³`** (quaternionic model): measure the induced map on the
third homology, using the chosen isomorphism `s3HomologyIso : H₃(S3; ℤ) ≅ ℤ`. -/
noncomputable def s3SelfDegree (f : TopCat.of S3 ⟶ TopCat.of S3) : ℤ :=
  s3HomologyIso.hom
    (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of S3) (TopCat.of S3) f) 3 s3HomologyGen)

/-- **The degree of a continuous self-map of `S³`**, in the form used throughout the chapter. -/
noncomputable def chern2 (f : C(S3, S3)) : ℤ := s3SelfDegree (TopCat.ofHom f)

end

end Work.CharacteristicClasses
