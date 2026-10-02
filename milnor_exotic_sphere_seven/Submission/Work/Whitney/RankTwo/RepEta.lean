import Mathlib
import Submission.Work.Whitney.RankTwo.RepDefs
import Submission.Work.Whitney.RankTwo.RepCrux
import Submission.Work.Whitney.RankTwo.RepSph2Rep
import Submission.Work.Thom.pairDeltaNatural
import Submission.Work.Sph3Disc.pairDelta_mixedCup_general

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

/-- The restriction of the sign cochain of the ball to its boundary is the boundary cochain. -/
theorem restr_sgBall_eq_gamma :
    ((dualChainMap ℤ (TopCat.of ↥(DiscB Y 1)) (TopCat.of (BBall Y))
      (subtypeIncl (TopCat.of (BBall Y)) (DiscB Y 1))).f 0) (sgBall Y)
      = ((dualChainMap ℤ (TopCat.of ↥(DiscB Y 1)) (TopCat.of ↥(Sph Y 1))
          (TopCat.ofHom (resDisc Y))).f 0) (sg0Sph Y) := by
  apply genEval_ext
  intro τ
  rw [genEval_pullback, genEval_pullback, genEval_sgBall, genEval_sg0Sph]
  rw [toSSetObjEquiv_app_eq, toSSetObjEquiv_app_eq]
  rfl

/-- The boundary cochain of the disc bundle is a cocycle. -/
theorem gamma_coc : cochainDiff ℤ (ssDiscB Y) (gamma Y) = 0 := by
  have h : cochainDiff ℤ (ssDiscB Y) (pullCM (resDisc Y) (sg0Sph Y)) = 0 := by
    rw [cochainDiff_pullCM (resDisc Y) (n := 0) (sg0Sph Y), sg0Sph_coc]
    exact map_zero _
  exact h

/-- The class of the boundary cochain is the pullback of the class of the sign cochain. -/
theorem gamma_class_eq (w : Coh ℤ 0 ↥(Sph Y 1))
    (hP : (CohMap (sigPos (Y := Y)) ℤ 0).hom w = oneH ℤ (ssY Y))
    (hN : (CohMap (sigNeg (Y := Y)) ℤ 0).hom w = 0) :
    cohomologyClassOf ℤ (ssDiscB Y) (gamma Y) (gamma_coc Y)
      = (CohMap (resDisc Y) ℤ 0).hom w := by
  have h1 : cohomologyClassOf ℤ (ssDiscB Y) (pullCM (resDisc Y) (sg0Sph Y))
      (by rw [cochainDiff_pullCM (resDisc Y) (n := 0) (sg0Sph Y), sg0Sph_coc]
          exact map_zero _)
      = (CohMap (resDisc Y) ℤ 0).hom w := by
    rw [← CohMap_classOf_pullCM (resDisc Y) (sg0Sph Y) (sg0Sph_coc Y)]
    rw [sg0Sph_class Y w hP hN]
  exact h1

/-- **The explicit `1`-cocycle of the disc bundle represents the transfer of the rank-one model
class.** -/
theorem eta_class :
    ∃ (hmem : eta Y ∈ relKern ℤ (TopCat.of (BBall Y)) (DiscB Y 1) 1)
      (hcoc : relDiffLM ℤ (TopCat.of (BBall Y)) (DiscB Y 1) 1 ⟨eta Y, hmem⟩ = 0),
      relClassOf ℤ (TopCat.of (BBall Y)) (DiscB Y 1) ⟨eta Y, hmem⟩ hcoc
        = stepDisc Y 1 (Mn 1 Y) := by
  obtain ⟨w, hwP, hwN, hwδ⟩ := Mn_one_eq_pairDelta Y
  obtain ⟨hmem0, hcoc0, hclass⟩ := Work.Sph3Disc.pdmc_pairδ_lift (X := TopCat.of (BBall Y))
    (DiscB Y 1) 0 (gamma Y) (gamma_coc Y) (sgBall Y) (restr_sgBall_eq_gamma Y)
  have hmem : eta Y ∈ relKern ℤ (TopCat.of (BBall Y)) (DiscB Y 1) 1 := by
    have h := hmem0
    rw [singularCochain_d_apply ℤ (TopCat.of (BBall Y)) (sgBall Y)] at h
    exact h
  have hsub : (⟨eta Y, hmem⟩ : relKern ℤ (TopCat.of (BBall Y)) (DiscB Y 1) 1)
      = ⟨((singularCochainComplex ℤ (TopCat.of (BBall Y))).d 0 (0 + 1)).hom (sgBall Y),
          hmem0⟩ := by
    apply Subtype.ext
    exact (singularCochain_d_apply ℤ (TopCat.of (BBall Y)) (sgBall Y)).symm
  have hcoc : relDiffLM ℤ (TopCat.of (BBall Y)) (DiscB Y 1) 1 ⟨eta Y, hmem⟩ = 0 := by
    rw [hsub]
    exact hcoc0
  have hclass' : (pairδ ℤ (TopCat.of (BBall Y)) (DiscB Y 1) 0)
      (cohomologyClassOf ℤ (ssDiscB Y) (gamma Y) (gamma_coc Y))
      = relClassOf ℤ (TopCat.of (BBall Y)) (DiscB Y 1) ⟨eta Y, hmem⟩ hcoc := by
    rw [hclass]
    exact (relClassOf_congr ℤ (TopCat.of (BBall Y)) (DiscB Y 1)
      (a := ⟨eta Y, hmem⟩)
      (a' := ⟨((singularCochainComplex ℤ (TopCat.of (BBall Y))).d 0 (0 + 1)).hom (sgBall Y),
        hmem0⟩) hcoc hcoc0 hsub).symm
  refine ⟨hmem, hcoc, ?_⟩
  rw [← hclass']
  rw [show (cohomologyClassOf ℤ (ssDiscB Y) (gamma Y) (gamma_coc Y))
      = (CohMap (resDisc Y) ℤ 0).hom w from gamma_class_eq Y w hwP hwN]
  rw [show stepDisc Y 1 (Mn 1 Y) = (relCohMap (CleanA.discFullMap Y 1) (DiscB Y 1) (Sph Y 1)
      (CleanA.discFullMap_mem Y 1) ℤ 1).hom (Mn 1 Y) from rfl]
  rw [← hwδ]
  exact (pairDeltaNatural (CleanA.discFullMap Y 1) (DiscB Y 1) (Sph Y 1)
    (CleanA.discFullMap_mem Y 1) 0 w).symm

end

end Work.Whitney.RankTwo
