import Mathlib
import Submission.Work.Whitney.RankTwo.RepDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Whitney.RankTwo

open Work.Thom Work.Cohomology Work.Thom.Orientation
open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

noncomputable section

variable (Y : Type) [TopologicalSpace Y]

/-- The class of the pullback of a cochain along a continuous map. -/
theorem CohMap_classOf_pullCM {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (f : C(X, Z)) {n : ℕ} (α : Cochain ℤ (TopCat.toSSet.obj (TopCat.of Z)) n)
    (hα : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of Z)) α = 0) :
    (ModuleCat.Hom.hom (CohMap f ℤ n))
        (cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of Z)) α hα)
      = cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of X)) (pullCM f α)
          (by rw [cochainDiff_pullCM f, hα]; exact map_zero _) := by
  change (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (dualChainMap ℤ (TopCat.of X) (TopCat.of Z) (TopCat.ofHom f)) n))
      (cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of Z)) α hα) = _
  rw [singularCohomologyMap_classOf ℤ (X := TopCat.of X) (Y := TopCat.of Z)
    (TopCat.ofHom f) α hα]
  refine cohomologyClassOf_congr ℤ (TopCat.toSSet.obj (TopCat.of X)) ?_ _ _
  rfl

/-- The class of the pullback of a *relative* class: the representative-level statement. -/
theorem relToAbs_classOf_relKern {Z : Type} [TopologicalSpace Z] (A : Set Z) {n : ℕ}
    (a : ↥(relKern ℤ (TopCat.of Z) A n))
    (ha : relDiffLM ℤ (TopCat.of Z) A n a = 0) :
    (relToAbs ℤ A n).hom (relClassOf ℤ (TopCat.of Z) A a ha)
      = cohomologyClassOf ℤ (TopCat.toSSet.obj (TopCat.of Z)) a.1
          (relClassOf_cochainDiff ℤ (TopCat.of Z) A a ha) :=
  relIncl_homologyMap_relClassOf ℤ (TopCat.of Z) A a ha

/-- The homeomorphism `Y × S¹ ≅ Sph Y 2`, in the direction `Sph Y 2 → Y × S¹`. -/
abbrev homeoSymm : C(↥(Sph Y 2), Y × MSph 2) :=
  ((prodSubsetHomeoA Y (EuclideanSpace ℝ (Fin 2)) (mSph 2)).symm : C(↥(Sph Y 2), Y × MSph 2))

/-- **The representative of the transferred rank-one model class on the rank-two sphere bundle.** -/
theorem sph2_rep_exists :
    ∃ (b : Cochain ℤ (ssSph2 Y) 1) (hb : cochainDiff ℤ (ssSph2 Y) b = 0),
      (cohomologyClassOf ℤ (ssSph2 Y) b hb
        = (ModuleCat.Hom.hom (CohMap ((prodSubsetHomeoA Y (EuclideanSpace ℝ (Fin 2))
            (mSph 2)).symm) ℤ 1))
            ((relToAbs ℤ (SphB Y 1) 1).hom (stepSph Y 1 (Mn 1 Y))))
      ∧ (∀ (σ : (ssSph2 Y) _⦋1⦌),
          (∀ q : stdSimplex ℝ (Fin 2), (((eSph2 Y 1) σ q : ↥(Sph Y 2)) : R2 Y).2 ∈ mLower 1)
            → genEval ℤ (ssSph2 Y) b σ = 0) := by
  set τ : RelCoh ℤ 1 (Y × MSph 2) (SphB Y 1) := stepSph Y 1 (Mn 1 Y) with hτ
  obtain ⟨ψ, hψcoc, hψclass⟩ :=
    exists_relClassOf ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) 1 τ
  let ψc : Cochain ℤ (TopCat.toSSet.obj (TopCat.of (Y × MSph 2))) 1 := ψ.1
  have hψcoc' : cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (Y × MSph 2))) ψc = 0 :=
    relClassOf_cochainDiff ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) ψ hψcoc
  have hψmem' : ψc ∈ relKern ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) 1 := ψ.2
  refine ⟨pullCM (homeoSymm Y) ψc, ?_, ?_, ?_⟩
  · rw [cochainDiff_pullCM (homeoSymm Y), hψcoc']
    exact map_zero _
  · rw [← hψclass, relToAbs_classOf_relKern (SphB Y 1) ψ hψcoc]
    exact (CohMap_classOf_pullCM (homeoSymm Y) ψc hψcoc').symm
  · intro σ hσ
    rw [genEval_pullCM]
    have hrange : Set.range (fun q : stdSimplex ℝ (Fin 2) =>
        (TopCat.toSSetObjEquivOld (TopCat.of (Y × MSph 2))
          (Opposite.op (SimplexCategory.mk 1)))
          ((TopCat.toSSet.map (TopCat.ofHom (homeoSymm Y))).app
            (Opposite.op (SimplexCategory.mk 1)) σ) q) ⊆ SphB Y 1 := by
      rintro p ⟨q, rfl⟩
      show ((TopCat.toSSetObjEquivOld (TopCat.of (Y × MSph 2))
          (Opposite.op (SimplexCategory.mk 1)))
          ((TopCat.toSSet.map (TopCat.ofHom (homeoSymm Y))).app
            (Opposite.op (SimplexCategory.mk 1)) σ)) q ∈ SphB Y 1
      rw [toSSetObjEquiv_app_eq]
      change ((homeoSymm Y) ((eSph2 Y 1) σ q)).2.1 ∈ mLower 1
      exact hσ q
    obtain ⟨τ', hτ'⟩ := exists_lift_of_range_subset (X := TopCat.of (Y × MSph 2)) (SphB Y 1)
      ((TopCat.toSSet.map (TopCat.ofHom (homeoSymm Y))).app
        (Opposite.op (SimplexCategory.mk 1)) σ)
        (by rw [← TopCat.range_toSSetObjEquivOld]; exact hrange)
    rw [← hτ']
    exact genEval_eq_zero_of_mem_relKern ℤ (TopCat.of (Y × MSph 2)) (SphB Y 1) ψc hψmem' τ'

end

end Work.Whitney.RankTwo
