import Mathlib
import Submission.Work.CharacteristicClasses.Degree
import Submission.Work.Cohomology.Compat.prodSphereAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.CharacteristicClasses

open scoped Topology
open CategoryTheory

noncomputable section

/-- **A constant self-map of `S³` induces zero on `H₃`.**  A constant map of `S³` factors through
the one-point space `PUnit`, whose third homology vanishes, so the map it induces on `H₃` is zero
(`Work.Cohomology.Compat.homologyMap_eq_zero_of_factor`). -/
lemma homologyMap_const_s3_eq_zero (c : S3) :
    HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of S3) (TopCat.of S3)
        (TopCat.ofHom (ContinuousMap.const S3 c))) 3 = 0 := by
  let g : TopCat.of S3 ⟶ TopCat.of PUnit := TopCat.ofHom (ContinuousMap.const S3 PUnit.unit)
  let h : TopCat.of PUnit ⟶ TopCat.of S3 := TopCat.ofHom (ContinuousMap.const (TopCat.of PUnit) c)
  have hfac : g ≫ h = TopCat.ofHom (ContinuousMap.const S3 c) := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl
  exact Work.Cohomology.Compat.homologyMap_eq_zero_of_factor _ g h hfac 3
    (Work.Cohomology.homologyPUnit ℤ 3 (by omega))

/-- **The degree of a constant self-map of `S³` is zero.**  Hint: a constant map factors through a
point and `H₃(point; ℤ) = 0`; there is already
`Work.Cohomology.homologyMap_const_eq_zero` in `Submission/Work/Cohomology/prodSphereAux.lean`
(`homologyMap (chainMap … (const …)) n = 0` for `1 ≤ n`).  Beware of the definitional mismatch
between `ContinuousMap.const S3 c` and `ContinuousMap.const ↑(TopCat.of S3) c`: a `change`/`show`
may be needed, and `maxHeartbeats` may have to be raised. -/
theorem chern2_const (c : Work.CharacteristicClasses.S3) :
    Work.CharacteristicClasses.chern2 (ContinuousMap.const Work.CharacteristicClasses.S3 c) = 0 := by
  rw [chern2, s3SelfDegree, homologyMap_const_s3_eq_zero c]
  simp

end

end Work.CharacteristicClasses
