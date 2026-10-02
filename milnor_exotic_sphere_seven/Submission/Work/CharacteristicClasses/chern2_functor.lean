import Mathlib
import Submission.Work.CharacteristicClasses.Degree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.CharacteristicClasses

open CategoryTheory

noncomputable section

/-- **Functoriality of the degree.**  `chern2 = s3SelfDegree` is the degree of a self-map of the
quaternionic `S³ = Sp(1)`, defined by evaluating the induced map on `H₃(S³;ℤ)` against the chosen
generator `s3HomologyGen`.  It is `1` on the identity, multiplicative on composition, and a
homotopy invariant.  (Proof: copy `Work.Cohomology.sphereSelfDegree_functor`, with `s3HomologyIso`
in place of `sphereHomologyTop`; the multiplicative step is `Work.Cohomology.moduleIso_deg_apply`;
use `TopCat.ofHom_comp`, `TopCat.ofHom_id`, and for homotopy invariance
`TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor`.) -/
theorem chern2_functor :
    Work.CharacteristicClasses.chern2 (ContinuousMap.id Work.CharacteristicClasses.S3) = 1 ∧
      (∀ f g : ContinuousMap Work.CharacteristicClasses.S3 Work.CharacteristicClasses.S3,
        Work.CharacteristicClasses.chern2 (g.comp f) =
          Work.CharacteristicClasses.chern2 g * Work.CharacteristicClasses.chern2 f) ∧
      (∀ f g : ContinuousMap Work.CharacteristicClasses.S3 Work.CharacteristicClasses.S3,
        ContinuousMap.Homotopic f g →
          Work.CharacteristicClasses.chern2 f = Work.CharacteristicClasses.chern2 g) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [chern2, s3SelfDegree, s3HomologyGen]
    have hcm : Work.Cohomology.chainMap ℤ (TopCat.of S3) (TopCat.of S3)
        (TopCat.ofHom (ContinuousMap.id S3)) = 𝟙 _ := by
      rw [TopCat.ofHom_id, Work.Cohomology.chainMap, CategoryTheory.Functor.map_id]
    rw [hcm, HomologicalComplex.homologyMap_id]
    have h2 : s3HomologyIso.hom (s3HomologyIso.inv.hom (1 : ℤ)) = 1 := by
      have h := congrArg ModuleCat.Hom.hom s3HomologyIso.inv_hom_id
      rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h
      exact LinearMap.congr_fun h (1 : ℤ)
    exact h2
  · intro f g
    rw [chern2, chern2, chern2, s3SelfDegree, s3SelfDegree, s3SelfDegree, s3HomologyGen]
    have hcm : Work.Cohomology.chainMap ℤ (TopCat.of S3) (TopCat.of S3)
        (TopCat.ofHom (g.comp f)) =
        Work.Cohomology.chainMap ℤ (TopCat.of S3) (TopCat.of S3) (TopCat.ofHom f) ≫
        Work.Cohomology.chainMap ℤ (TopCat.of S3) (TopCat.of S3) (TopCat.ofHom g) := by
      rw [TopCat.ofHom_comp, Work.Cohomology.chainMap, CategoryTheory.Functor.map_comp]
    rw [hcm, HomologicalComplex.homologyMap_comp]
    rw [Work.Cohomology.moduleCat_hom_comp_apply]
    exact Work.Cohomology.moduleIso_deg_apply _ _ _ _
  · intro f g hfg
    obtain ⟨H⟩ := hfg
    rw [chern2, chern2, s3SelfDegree, s3SelfDegree, s3HomologyGen]
    rw [show HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (TopCat.of S3) (TopCat.of S3) (TopCat.ofHom f)) 3 =
        HomologicalComplex.homologyMap
          (Work.Cohomology.chainMap ℤ (TopCat.of S3) (TopCat.of S3) (TopCat.ofHom g)) 3 from
      TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H (ModuleCat.of ℤ ℤ) 3]

end

end Work.CharacteristicClasses
