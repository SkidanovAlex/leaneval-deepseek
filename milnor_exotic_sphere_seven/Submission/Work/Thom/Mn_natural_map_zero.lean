import Mathlib
import Submission.Work.Thom.ProdMapTools
import Submission.Work.Thom.CohMap_oneH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom

/-- **Naturality of the rank-zero model class in the base along an arbitrary continuous map.**

The rank-zero model class `Mn 0 B` is the unique class of the pair `(B × ℝ⁰, B × S⁰)` which
forgets to the unit class `1 ∈ H⁰(B × ℝ⁰)` (`Work.Thom.Mn_zero_spec`).  Pulling it back along the
base change `prodMapA g ℝ⁰ : B' × ℝ⁰ → B × ℝ⁰` therefore only has to be checked after applying the
forgetful map `relToAbs`, where it becomes the naturality of the unit class,
`Work.Thom.CohMap_oneH`. -/
theorem Mn_natural_map_zero {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    (g : C(B', B)) :
    (Work.Thom.relCohMap (Work.Thom.prodMapA g (EuclideanSpace ℝ (Fin 0)))
      (Work.Thom.Sph B' 0) (Work.Thom.Sph B 0) (fun _ h => h) ℤ 0).hom (Work.Thom.Mn 0 B)
      = Work.Thom.Mn 0 B' := by
  apply (bijective_relToAbs_sphZero B').1
  rw [relCohMap_relToAbs_apply (prodMapA g (EuclideanSpace ℝ (Fin 0))) (Sph B' 0) (Sph B 0)
        (fun _ h => h) ℤ 0 (Mn 0 B)]
  rw [Mn_zero_spec B, Mn_zero_spec B']
  exact CohMap_oneH (prodMapA g (EuclideanSpace ℝ (Fin 0)))

end Work.Thom
