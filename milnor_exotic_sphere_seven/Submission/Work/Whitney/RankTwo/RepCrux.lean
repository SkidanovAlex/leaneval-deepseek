import Mathlib
import Submission.Work.Whitney.RankTwo.RepDefs
import Submission.Work.Thom.Orientation.pairDelta_flip_one

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

/-- The pullback of the sign cochain along the positive section is the unit cochain. -/
theorem sg0Sph_pullback_sigPos :
    ((dualChainMap ℤ (TopCat.of Y) (TopCat.of ↥(Sph Y 1))
        (TopCat.ofHom (sigPos (Y := Y)))).f 0) (sg0Sph Y) = unitCochain ℤ (ssY Y) := by
  apply genEval_ext
  intro σ
  rw [genEval_pullback, genEval_sg0Sph, genEval_unitCochain]
  have hpt : (eSph1 Y 0) ((TopCat.toSSet.map (TopCat.ofHom (sigPos (Y := Y)))).app
      (Opposite.op (SimplexCategory.mk 0)) σ) default
      = sigPos (Y := Y) ((eY Y 0) σ default) :=
    toSSetObjEquiv_app_eq (TopCat.of Y) (TopCat.of ↥(Sph Y 1))
      (TopCat.ofHom (sigPos (Y := Y))) 0 σ default
  rw [hpt]
  rw [show (((sigPos (Y := Y) ((eY Y 0) σ default) : ↥(Sph Y 1)) : R1 Y))
      = (((eY Y 0) σ default, (sphPlus : EuclideanSpace ℝ (Fin 1))) : R1 Y) from rfl]
  rw [signFibR2_sphPlus]

/-- The pullback of the sign cochain along the negative section vanishes. -/
theorem sg0Sph_pullback_sigNeg :
    ((dualChainMap ℤ (TopCat.of Y) (TopCat.of ↥(Sph Y 1))
        (TopCat.ofHom (sigNeg (Y := Y)))).f 0) (sg0Sph Y) = 0 := by
  apply genEval_ext
  intro σ
  rw [genEval_pullback, genEval_sg0Sph]
  have hpt : (eSph1 Y 0) ((TopCat.toSSet.map (TopCat.ofHom (sigNeg (Y := Y)))).app
      (Opposite.op (SimplexCategory.mk 0)) σ) default
      = sigNeg (Y := Y) ((eY Y 0) σ default) :=
    toSSetObjEquiv_app_eq (TopCat.of Y) (TopCat.of ↥(Sph Y 1))
      (TopCat.ofHom (sigNeg (Y := Y))) 0 σ default
  rw [hpt]
  rw [show (((sigNeg (Y := Y) ((eY Y 0) σ default) : ↥(Sph Y 1)) : R1 Y))
      = (((eY Y 0) σ default, (sphMinus : EuclideanSpace ℝ (Fin 1))) : R1 Y) from rfl]
  rw [signFibR2_sphMinus]
  rfl

/-- The differential of the zero cochain vanishes. -/
theorem cochainDiff_zero (X : SSet) (n : ℕ) :
    cochainDiff ℤ X (0 : Cochain ℤ X n) = 0 := by
  rw [cochainDiff]
  exact LinearMap.zero_comp _

/-- The class of the zero cochain is zero. -/
theorem cohomologyClassOf_zero (X : SSet) {n : ℕ}
    (h : cochainDiff ℤ X (0 : Cochain ℤ X n) = 0) :
    cohomologyClassOf ℤ X (0 : Cochain ℤ X n) h = 0 := by
  rw [cohomologyClassOf]
  have hz : cocycleOf ℤ X (0 : Cochain ℤ X n) h = 0 := by
    apply iCycles_injective ℤ X n
    rw [iCycles_cocycleOf, map_zero]
    try rfl
  rw [hz, map_zero]

/-- **The sign cochain on the rank-one sphere bundle is the witness `w`.** -/
theorem sg0Sph_class (w : Coh ℤ 0 ↥(Sph Y 1))
    (hP : (CohMap (sigPos (Y := Y)) ℤ 0).hom w = oneH ℤ (ssY Y))
    (hN : (CohMap (sigNeg (Y := Y)) ℤ 0).hom w = 0) :
    cohomologyClassOf ℤ (ssSph1 Y) (sg0Sph Y) (sg0Sph_coc Y) = w := by
  set x : Coh ℤ 0 ↥(Sph Y 1) := cohomologyClassOf ℤ (ssSph1 Y) (sg0Sph Y) (sg0Sph_coc Y)
    with hx
  have hxP : (CohMap (sigPos (Y := Y)) ℤ 0).hom x = oneH ℤ (ssY Y) := by
    rw [hx]
    change (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (dualChainMap ℤ (TopCat.of Y) (TopCat.of ↥(Sph Y 1))
          (TopCat.ofHom (sigPos (Y := Y)))) 0))
        (cohomologyClassOf ℤ (ssSph1 Y) (sg0Sph Y) (sg0Sph_coc Y))
      = cohomologyClassOf ℤ (ssY Y) (unitCochain ℤ (ssY Y))
          (cochainDiff_unitCochain ℤ (ssY Y))
    rw [singularCohomologyMap_classOf ℤ (X := TopCat.of Y) (Y := TopCat.of ↥(Sph Y 1))
      (TopCat.ofHom (sigPos (Y := Y))) (sg0Sph Y) (sg0Sph_coc Y)]
    exact cohomologyClassOf_congr ℤ (ssY Y) (sg0Sph_pullback_sigPos Y) _ _
  have hxN : (CohMap (sigNeg (Y := Y)) ℤ 0).hom x = 0 := by
    rw [hx]
    change (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (dualChainMap ℤ (TopCat.of Y) (TopCat.of ↥(Sph Y 1))
          (TopCat.ofHom (sigNeg (Y := Y)))) 0))
        (cohomologyClassOf ℤ (ssSph1 Y) (sg0Sph Y) (sg0Sph_coc Y)) = 0
    rw [singularCohomologyMap_classOf ℤ (X := TopCat.of Y) (Y := TopCat.of ↥(Sph Y 1))
      (TopCat.ofHom (sigNeg (Y := Y))) (sg0Sph Y) (sg0Sph_coc Y)]
    exact (cohomologyClassOf_congr ℤ (ssY Y) (sg0Sph_pullback_sigNeg Y) _ _).trans
      (cohomologyClassOf_zero (ssY Y) (cochainDiff_zero (ssY Y) 0))
  have hzeroP : (CohMap (sigPos (Y := Y)) ℤ 0).hom (x - w) = 0 := by
    rw [map_sub, hxP, hP]
    exact sub_self _
  have hzeroN : (CohMap (sigNeg (Y := Y)) ℤ 0).hom (x - w) = 0 := by
    rw [map_sub, hxN, hN]
    exact sub_self _
  exact sub_eq_zero.mp (eq_zero_of_sigPos_sigNeg_eq_zero (Y := Y) (x - w) hzeroP hzeroN)

end

end Work.Whitney.RankTwo
