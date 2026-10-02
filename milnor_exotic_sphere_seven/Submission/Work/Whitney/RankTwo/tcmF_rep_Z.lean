import Mathlib
import Submission.Work.Whitney.RankTwo.Basic
import Submission.Work.Whitney.RankTwo.Eval
import Submission.Work.Whitney.RankTwo.Chain
import Submission.Work.Whitney.RankTwo.Cochains
import Submission.Work.Thom.naturalModelClass_punct
import Submission.Work.Sph3Disc.pairDelta_mixedCup_general
import Submission.Work.Whitney.Mn_one_eq_pairDelta
import Submission.Work.Thom.pairDeltaNatural
import Submission.Work.Whitney.RankTwo.RepEval
import Submission.Work.Whitney.RankTwo.RepCapMain

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.Whitney.RankTwo

open Work.Thom Work.Cohomology Work.Thom.Orientation
open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

theorem tcmF_rep_Z (Y : Type) [TopologicalSpace Y] [Subsingleton Y] [Nonempty Y] (y : Y)
    (s : ↥(Work.Cohomology.relKern ℤ
        (TopCat.of (Y × EuclideanSpace ℝ (Fin 2))) (Work.Thom.Punct Y 2) 2))
    (hs : (Work.Cohomology.relDiffLM ℤ
        (TopCat.of (Y × EuclideanSpace ℝ (Fin 2))) (Work.Thom.Punct Y 2) 2) s = 0)
    (hclass : Work.Cohomology.relClassOf ℤ
        (TopCat.of (Y × EuclideanSpace ℝ (Fin 2))) (Work.Thom.Punct Y 2) s hs
      = Work.Thom.Mpun 2 Y) :
    Work.Cohomology.kronecker ℤ (Work.Whitney.RankTwo.ssX Y)
      (((Work.Cohomology.dualChainMap ℤ (TopCat.of (Work.Whitney.RankTwo.X Y))
          (TopCat.of (Y × EuclideanSpace ℝ (Fin 2)))
          (TopCat.ofHom (Work.Whitney.tcmF Y 1 1))).f 2).hom s.1)
      (Work.Whitney.RankTwo.Z Y y) = -1 := by
  change Work.Cohomology.kronecker ℤ (ssX Y)
    (pullCM (tcmF Y 1 1) s.1) (Z Y y) = -1
  -- the representative of the transfer `stepSph Y 1 (Mn 1 Y)`
  obtain ⟨ψ, hψrel, hψclass, hψcoc⟩ := sph2_rep_data Y
  -- a lift of its pullback to the rank-two total space
  obtain ⟨bt, hbt⟩ := surjective_restr ℤ (TopCat.of (R2 Y)) (Sph Y 2) 1
    (pullCM (homeoSymm Y) ψ.1)
  have hb : cochainDiff ℤ (ssSph2 Y) (pullCM (homeoSymm Y) ψ.1) = 0 :=
    pullCM_homeoSymm_coc Y ψ hψcoc
  have hbclass := pullCM_homeoSymm_class Y ψ hψrel hψclass
  -- the connecting homomorphism realises `Mn 2 Y`
  obtain ⟨hu_mem, hu_coc, hu_class0⟩ := Work.Sph3Disc.pdmc_pairδ_lift
    (X := TopCat.of (R2 Y)) (Sph Y 2) 1 (pullCM (homeoSymm Y) ψ.1) hb bt hbt
  have hMn2 : Mn 2 Y = pairδ ℤ (TopCat.of (R2 Y)) (Sph Y 2) 1
      (cohomologyClassOf ℤ (ssSph2 Y) (pullCM (homeoSymm Y) ψ.1) hb) := by
    rw [show Mn 2 Y = step Y 1 (Mn 1 Y) from rfl, step, ← hbclass]
    rfl
  have hu_class : relClassOf ℤ (TopCat.of (R2 Y)) (Sph Y 2)
      ⟨((singularCochainComplex ℤ (TopCat.of (R2 Y))).d 1 2).hom bt, hu_mem⟩ hu_coc = Mn 2 Y := by
    rw [← hu_class0, hMn2]
  -- the representative `s` viewed in the sphere-relative complex
  have hSphPunct : (Sph Y 2 : Set (R2 Y)) ⊆ (Punct Y 2 : Set (R2 Y)) :=
    fun x hx => mem_Sph_punct Y 2 x hx
  let sSph : ↥(relKern ℤ (TopCat.of (R2 Y)) (Sph Y 2) 2) :=
    ⟨s.1, relKern_mono hSphPunct s.2⟩
  have hsSph : relDiffLM ℤ (TopCat.of (R2 Y)) (Sph Y 2) 2 sSph = 0 := by
    apply Subtype.ext
    rw [relDiffLM_coe, Submodule.coe_zero]
    have h := congrArg Subtype.val hs
    simp only [relDiffLM_coe, Submodule.coe_zero] at h
    exact h
  have hsSph_class : relClassOf ℤ (TopCat.of (R2 Y)) (Sph Y 2) sSph hsSph = Mn 2 Y := by
    have hcl : (HomologicalComplex.homologyMap (relComplexMap ℤ (Sph Y 2) (Punct Y 2)
        (TopCat.ofHom (ContinuousMap.id (R2 Y))) (fun x hx => mem_Sph_punct Y 2 x hx)) 2).hom
          (relClassOf ℤ (TopCat.of (R2 Y)) (Punct Y 2) s hs)
        = relClassOf ℤ (TopCat.of (R2 Y)) (Sph Y 2) sSph hsSph := by
      rw [homologyMap_relComplexMap_relClassOf (R := ℤ) (X₁ := TopCat.of (R2 Y))
        (X₂ := TopCat.of (R2 Y)) (A₁ := Sph Y 2) (A₂ := Punct Y 2)
        (f := TopCat.ofHom (ContinuousMap.id (R2 Y)))
        (h := fun x hx => mem_Sph_punct Y 2 x hx) (n := 2) s hs]
      exact relClassOf_congr ℤ (TopCat.of (R2 Y)) (Sph Y 2) _ hsSph (by
        apply Subtype.ext
        rw [relMapLM_coe, TopCat.ofHom_id, dualChainMap_id, HomologicalComplex.id_f,
          ModuleCat.hom_id, LinearMap.id_apply])
    rw [← hcl, hclass]
    exact Mpun_spec 2 Y
  -- the two cocycles differ by a coboundary
  obtain ⟨v, hv⟩ := relClassOf_coboundary (X := TopCat.of (R2 Y)) (Sph Y 2) (n := 1)
    sSph ⟨((singularCochainComplex ℤ (TopCat.of (R2 Y))).d 1 2).hom bt, hu_mem⟩
    hsSph hu_coc (by rw [hsSph_class, hu_class])
  have hs1 : s.1 = cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (R2 Y))) bt
      + cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (R2 Y))) v.1 := by
    have h := congrArg Subtype.val hv
    simp only [relDiffLM_coe, Submodule.coe_sub] at h
    rw [show (sSph.1 : (singularCochainComplex ℤ (TopCat.of (R2 Y))).X 2) = s.1 from rfl] at h
    rw [show ((singularCochainComplex ℤ (TopCat.of (R2 Y))).d 1 2).hom v.1
        = cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (R2 Y))) v.1 from
      singularCochain_d_apply ℤ (TopCat.of (R2 Y)) v.1] at h
    rw [show ((singularCochainComplex ℤ (TopCat.of (R2 Y))).d 1 2).hom bt
        = cochainDiff ℤ (TopCat.toSSet.obj (TopCat.of (R2 Y))) bt from
      singularCochain_d_apply ℤ (TopCat.of (R2 Y)) bt] at h
    rw [h]
    rw [← add_sub_assoc, add_sub_cancel_left]
  -- the evaluation
  have hpull : pullCM (tcmF Y 1 1) s.1
      = cochainDiff ℤ (ssX Y) (pullCM (tcmF Y 1 1) bt)
        + cochainDiff ℤ (ssX Y) (pullCM (tcmF Y 1 1) v.1) := by
    rw [hs1]
    rw [show pullCM (tcmF Y 1 1)
          (cochainDiff ℤ (ssR2 Y) bt + cochainDiff ℤ (ssR2 Y) v.1)
        = pullCM (tcmF Y 1 1) (cochainDiff ℤ (ssR2 Y) bt)
          + pullCM (tcmF Y 1 1) (cochainDiff ℤ (ssR2 Y) v.1) from
      map_add (((dualChainMap ℤ (TopCat.of (X Y)) (TopCat.of (R2 Y))
        (TopCat.ofHom (tcmF Y 1 1))).f 2).hom) _ _]
    rw [cochainDiff_pullCM (tcmF Y 1 1), cochainDiff_pullCM (tcmF Y 1 1)]
  have hv0 : (pullCM (tcmF Y 1 1) v.1) (c Y y) = 0 := by
    rw [show (pullCM (tcmF Y 1 1) v.1) (c Y y)
        = kronecker ℤ (ssX Y) (pullCM (tcmF Y 1 1) v.1) (c Y y) from rfl,
      kronecker_c_apply]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [genEval_pullCM, tcmF_arcSimp Y y k]
    exact genEval_relKern_incl Y y v.1 v.2 k
  rw [hpull,
    show kronecker ℤ (ssX Y) (cochainDiff ℤ (ssX Y) (pullCM (tcmF Y 1 1) bt)
          + cochainDiff ℤ (ssX Y) (pullCM (tcmF Y 1 1) v.1)) (Z Y y)
        = kronecker ℤ (ssX Y) (cochainDiff ℤ (ssX Y) (pullCM (tcmF Y 1 1) bt)) (Z Y y)
          + kronecker ℤ (ssX Y) (cochainDiff ℤ (ssX Y) (pullCM (tcmF Y 1 1) v.1)) (Z Y y) from
      kronecker_add ℤ (ssX Y) _ _ (Z Y y),
    show kronecker ℤ (ssX Y) (cochainDiff ℤ (ssX Y) (pullCM (tcmF Y 1 1) bt)) (Z Y y)
        = kronecker ℤ (ssX Y) (pullCM (tcmF Y 1 1) bt)
            (((ssX Y).chainComplex zR).d 2 1 (Z Y y)) from rfl,
    show kronecker ℤ (ssX Y) (cochainDiff ℤ (ssX Y) (pullCM (tcmF Y 1 1) v.1)) (Z Y y)
        = kronecker ℤ (ssX Y) (pullCM (tcmF Y 1 1) v.1)
            (((ssX Y).chainComplex zR).d 2 1 (Z Y y)) from rfl,
    d_Z Y y,
    show kronecker ℤ (ssX Y) (pullCM (tcmF Y 1 1) bt) (c Y y)
        = (pullCM (tcmF Y 1 1) bt) (c Y y) from rfl,
    show kronecker ℤ (ssX Y) (pullCM (tcmF Y 1 1) v.1) (c Y y)
        = (pullCM (tcmF Y 1 1) v.1) (c Y y) from rfl,
    pullCM_tcmF_bt_c Y y bt ψ hψrel hψclass hbt, hv0]
  norm_num

end Work.Whitney.RankTwo
