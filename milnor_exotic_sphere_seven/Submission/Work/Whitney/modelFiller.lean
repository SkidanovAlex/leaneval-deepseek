import Mathlib
import Submission.Work.Whitney.CupDefs
import Submission.Work.Whitney.capTransferPrep
import Submission.Work.Whitney.Signed.CapFull
import Submission.Work.Whitney.Signed.KronAdj
import Submission.Work.Whitney.Signed.ModelSide
import Submission.Work.Whitney.Signed.ModelAux
import Submission.Work.Whitney.relCycleKron
import Submission.Work.Whitney.RankTwo.RepDefs
import Submission.Work.Whitney.RankTwo.RepRelCoh
import Submission.Work.Whitney.RankTwo.RepEval
import Submission.Work.Whitney.RankTwo.RepCapMain
import Submission.Work.Whitney.pairDeltaC_restr_gammaSharp_eq
import Submission.Work.Whitney.tcmSuspAux.pushChain_isSmallChain_of_subset
import Submission.Work.Whitney.tcmSuspAux.kronecker_eq_zero_of_isSmallChain_of_restr_sphPush
import Submission.Work.Whitney.tcmSuspAux.kronecker_capMapPairSph_eq
import Submission.Work.Thom.stepDefs
import Submission.Work.Thom.ModelGeometry
import Submission.Work.Thom.naturalModelClass_punct
import Submission.Work.Thom.MixedCup
import Submission.Work.Thom.Indicator
import Submission.Work.Cohomology.relCupHNatural
import Submission.Work.Sph3Disc.pairDelta_mixedCup_general
import Submission.Work.Whitney.RankTwo.tcmF_rep_Z

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option quotPrecheck false

namespace Work.Whitney

open Work.Thom Work.Cohomology
open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

noncomputable section

/-- The push-forward of singular chains commutes with the differential. -/
theorem mf_pushChain_d_succ (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (c : (singularChains ℤ X).X (n + 1)) :
    ((singularChains ℤ Y).d (n + 1) n) (pushChain X Y f (n + 1) c)
      = pushChain X Y f n (((singularChains ℤ X).d (n + 1) n) c) := by
  have hc := congrArg ModuleCat.Hom.hom ((chainMap ℤ X Y f).comm (n + 1) n)
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hc
  have hcx := LinearMap.congr_fun hc c
  simpa only [LinearMap.comp_apply, pushChain, pushChainHom, chainMap_f_eq] using hcx

/-- A representative of the class `stepSph Y n (Mn n Y)`, together with the cochain form of its
cocycle condition. -/
theorem mf_exists_rep_stepSph (Y : Type) [TopologicalSpace Y] (n : ℕ) :
    ∃ (ψ : ↥(relKern ℤ (TopCat.of (Y × MSph (n + 1))) (SphB Y n) n))
      (hψrel : relDiffLM ℤ (TopCat.of (Y × MSph (n + 1))) (SphB Y n) n ψ = 0),
      relClassOf ℤ (TopCat.of (Y × MSph (n + 1))) (SphB Y n) ψ hψrel
          = stepSph Y n (Mn n Y)
        ∧ cochainDiff ℤ (ssB (Y × MSph (n + 1))) ψ.1 = 0 := by
  obtain ⟨ψ, hψrel, hψclass⟩ :=
    exists_relClassOf ℤ (TopCat.of (Y × MSph (n + 1))) (SphB Y n) n (stepSph Y n (Mn n Y))
  exact ⟨ψ, hψrel, hψclass,
    RankTwo.cochainDiff_of_relDiffLM (X := TopCat.of (Y × MSph (n + 1))) (SphB Y n) ψ hψrel⟩

section General

variable (Y : Type) [TopologicalSpace Y] (n : ℕ)

local notation "Yb" => (Y × EuclideanSpace ℝ (Fin (n + 1)))
local notation "Tb" => TopCat.of (Y × EuclideanSpace ℝ (Fin (n + 1)))
local notation "Xw" => TopCat.of (tcmX Y n 1)
local notation "Xd" => TopCat.of (Y × MBall n)
local notation "Sphb" => TopCat.of ↥(Sph Y (n + 1))
local notation "MSphb" => TopCat.of (Y × MSph (n + 1))
local notation "tcmFH" => TopCat.ofHom (tcmF Y n 1)
local notation "capXH" => TopCat.ofHom (capX Y n)
local notation "capFullH" => TopCat.ofHom (capFull Y n)
local notation "capMapH" => TopCat.ofHom (capMapPairSph Y n)
local notation "sphUnflatH" => TopCat.ofHom (sphUnflat Y n)
local notation "sphFlatH" => TopCat.ofHom (sphFlat Y n)
local notation "dC" => (ModuleCat.Hom.hom ((singularCochainComplex ℤ Tb).d n (n + 1)))
local notation "dCh" => ((singularChains ℤ Tb).d (n + 1) n)
local notation "ssBw" => ssB (tcmX Y n 1)
local notation "ssBd" => ssB (Y × MBall n)
local notation "ssBb" => ssB (Y × EuclideanSpace ℝ (Fin (n + 1)))
local notation "ssBm" => ssB (Y × MSph (n + 1))
local notation "ssBs" => ssB ↥(Sph Y (n + 1))
local notation "Kb" "(" α "," c ")" => kronecker ℤ ssBb α c
local notation "Kd" "(" α "," c ")" => kronecker ℤ ssBd α c
local notation "Kw" "(" α "," c ")" => kronecker ℤ ssBw α c
local notation "Km" "(" α "," c ")" => kronecker ℤ ssBm α c
local notation "Ks" "(" α "," c ")" => kronecker ℤ ssBs α c
local notation "FZ" "(" Z ")" => pushChain Xw Tb tcmFH (n + 1) Z
local notation "FL" "(" L ")" => pushChain Xw Tb tcmFH n L
local notation "FCB" "(" B ")" => pushChain Xd Tb capFullH n B

theorem mf_modelSideCap
    (B : (singularChains ℤ Xd).X n)
    (hB : IsSmallChain (DiscB Y n) (∅ : Set (Y × MBall n)) ((singularChains ℤ Xd).d n (n - 1) B))
    (L : (singularChains ℤ Xw).X n)
    (hL : IsSmallChain (fun x : tcmX Y n 1 => (tcmF Y n 1 x).2 ∈ mLower n)
      (∅ : Set (tcmX Y n 1)) L)
    (Z : (singularChains ℤ Xw).X (n + 1))
    (hZ : (singularChains ℤ Xw).d (n + 1) n Z = pushChain Xd Xw capXH n B + L)
    (s : ↥(relKern ℤ Tb (Punct Y (n + 1)) (n + 1)))
    (hs : relDiffLM ℤ Tb (Punct Y (n + 1)) (n + 1) s = 0)
    (hsr : relClassOf ℤ Tb (Punct Y (n + 1)) s hs = Mpun (n + 1) Y)
    (b : ↥(relKern ℤ Xd (DiscB Y n) n))
    (hb : relDiffLM ℤ Xd (DiscB Y n) n b = 0)
    (hbc : relClassOf ℤ Xd (DiscB Y n) b hb = stepDisc Y n (Mn n Y)) :
    kronecker ℤ ssBw
      (show Cochain ℤ ssBw (n + 1) from
        (ModuleCat.Hom.hom ((dualChainMap ℤ Xw Tb tcmFH).f (n + 1))) s.1) Z
    = kronecker ℤ ssBd (show Cochain ℤ ssBd n from b.1) B := by
  classical
  change (show Cochain ℤ ssBw (n + 1) from
        (ModuleCat.Hom.hom ((dualChainMap ℤ Xw Tb tcmFH).f (n + 1))) s.1) Z
    = (show Cochain ℤ ssBd n from b.1) B
  -- 1. a representative of `stepSph`
  obtain ⟨ψ, hψrel, hψclass, hψcoc⟩ := mf_exists_rep_stepSph Y n
  -- 2. the pushed cochain on the sphere bundle, and its class
  have hb0coc : cochainDiff ℤ (ssB ↥(Sph Y (n + 1))) (sphPushCochain Y n ψ.1) = 0 :=
    sphPushCochain_cocycle Y n ψ.1 hψcoc
  have hb0class : cohomologyClassOf ℤ (ssB ↥(Sph Y (n + 1))) (sphPushCochain Y n ψ.1) hb0coc
      = (CohMap (sphUnflat Y n) ℤ n).hom
          ((relToAbs ℤ (SphB Y n) n).hom (stepSph Y n (Mn n Y))) := by
    rw [← hψclass, RankTwo.relToAbs_classOf_relKern (SphB Y n) ψ hψrel]
    exact (RankTwo.CohMap_classOf_pullCM (sphUnflat Y n) ψ.1 hψcoc).symm
  -- 3. lift to the total space
  obtain ⟨bt, hbt⟩ := surjective_restr ℤ Tb (Sph Y (n + 1)) n (sphPushCochain Y n ψ.1)
  -- 4. the pair-delta representative of `Mn (n+1)`
  obtain ⟨hmem, hcoc, hpair⟩ := Sph3Disc.pdmc_pairδ_lift Tb (Sph Y (n + 1)) n
    (sphPushCochain Y n ψ.1) hb0coc bt hbt
  have hwclass : relClassOf ℤ Tb (Sph Y (n + 1)) ⟨dC bt, hmem⟩ hcoc = Mn (n + 1) Y := by
    rw [← hpair, hb0class]
    rfl
  -- 5. `s` viewed in the `Sph`-relative complex
  have hSphPunct : Sph Y (n + 1) ⊆ Punct Y (n + 1) :=
    fun x hx => mem_Sph_punct Y (n + 1) x hx
  let sSph : ↥(relKern ℤ Tb (Sph Y (n + 1)) (n + 1)) := ⟨s.1, relKern_mono hSphPunct s.2⟩
  have hsSph : relDiffLM ℤ Tb (Sph Y (n + 1)) (n + 1) sSph = 0 := by
    apply Subtype.ext
    rw [relDiffLM_coe, Submodule.coe_zero]
    have h := congrArg Subtype.val hs
    simp only [relDiffLM_coe, Submodule.coe_zero] at h
    exact h
  have hsSph_class : relClassOf ℤ Tb (Sph Y (n + 1)) sSph hsSph = Mn (n + 1) Y := by
    have hcl : (HomologicalComplex.homologyMap
        (relComplexMap ℤ (X₁ := Tb) (X₂ := Tb) (Sph Y (n + 1)) (Punct Y (n + 1))
          (TopCat.ofHom (ContinuousMap.id Yb)) (fun x hx => mem_Sph_punct Y (n + 1) x hx))
        (n + 1)).hom (relClassOf ℤ Tb (Punct Y (n + 1)) s hs)
        = relClassOf ℤ Tb (Sph Y (n + 1)) sSph hsSph := by
      rw [homologyMap_relComplexMap_relClassOf ℤ (Sph Y (n + 1)) (Punct Y (n + 1))
        (TopCat.ofHom (ContinuousMap.id Yb)) (fun x hx => mem_Sph_punct Y (n + 1) x hx) s hs]
      exact relClassOf_congr ℤ Tb (Sph Y (n + 1)) _ hsSph (by
        apply Subtype.ext
        rw [relMapLM_coe, TopCat.ofHom_id, dualChainMap_id, HomologicalComplex.id_f,
          ModuleCat.hom_id, LinearMap.id_apply])
    rw [← hcl, hsr]
    exact Mpun_spec (n + 1) Y
  -- 6. the coboundary
  obtain ⟨v, hv⟩ := RankTwo.relClassOf_coboundary (X := Tb) (Sph Y (n + 1))
    sSph ⟨dC bt, hmem⟩ hsSph hcoc (by rw [hsSph_class, hwclass])
  have hs1 : s.1 = dC bt + dC v.1 := by
    have h := congrArg Subtype.val hv
    simp only [relDiffLM_coe, Submodule.coe_sub] at h
    rw [show sSph.1 = s.1 from rfl] at h
    rw [h]
    abel
  -- 7. the boundary of the push-forward
  have hdFZ : dCh (pushChain Xw Tb tcmFH (n + 1) Z)
      = pushChain Xd Tb capFullH n B + pushChain Xw Tb tcmFH n L := by
    rw [mf_pushChain_d_succ Xw Tb tcmFH n Z, hZ, map_add,
      pushChain_comp Xd Xw Tb capXH tcmFH n B]
    rw [← TopCat.ofHom_comp, tcmF_comp_capX_eq_capFull]
  -- 8. smallness
  have hsmall_cap : IsSmallChain (Sph Y (n + 1)) (∅ : Set Yb) (pushChain Xd Tb capFullH n B) :=
    pushChain_isSmallChain (X := Tb) (A := Xd) (U := Sph Y (n + 1)) (V := ∅)
      capFullH (n := n)
      (Or.inl (by rintro x ⟨q, rfl⟩; exact capFull_image_subset_Sph Y n q)) B
  have hsmall_FL_band : IsSmallChain (BandFull Y n) (∅ : Set Yb) (pushChain Xw Tb tcmFH n L) :=
    tcmSuspAux.pushChain_isSmallChain_of_subset (f := tcmFH)
      (U := fun x : tcmX Y n 1 => (tcmF Y n 1 x).2 ∈ mLower n)
      (U' := BandFull Y n) (h := fun a ha => ha) (n := n) L hL
  have hsmall_FL : IsSmallChain (Sph Y (n + 1)) (∅ : Set Yb) (pushChain Xw Tb tcmFH n L) :=
    tcmSuspAux.pushChain_isSmallChain_of_subset (f := tcmFH)
      (U := fun x : tcmX Y n 1 => (tcmF Y n 1 x).2 ∈ mLower n)
      (U' := Sph Y (n + 1)) (h := fun a ha => ha.1) (n := n) L hL
  -- 9. the four evaluations
  have hv_cap : Kb(v.1, FCB(B)) = 0 :=
    kronecker_eq_zero_of_isSmallChain_of_mem_relKern Tb (A := Sph Y (n + 1)) (n := n)
      v FCB(B) hsmall_cap
  have hv_L : Kb(v.1, FL(L)) = 0 :=
    kronecker_eq_zero_of_isSmallChain_of_mem_relKern Tb (A := Sph Y (n + 1)) (n := n)
      v FL(L) hsmall_FL
  have hbt_L : Kb(bt, FL(L)) = 0 :=
    tcmSuspAux.kronecker_eq_zero_of_isSmallChain_of_restr_sphPush Y n ψ bt hbt FL(L) hsmall_FL_band
  have hbt_cap : Kb(bt, FCB(B)) = Kd(b.1, B) := by
    rw [show Kb(bt, FCB(B))
        = Kb(bt, pushChain Sphb Tb (subtypeIncl Tb (Sph Y (n + 1))) n
            (pushChain Xd Sphb
              (TopCat.ofHom ((sphFlat Y n).comp (capMapPairSph Y n))) n B))
        from congrArg (fun c => kronecker ℤ ssBb bt c) (capFull_pushChain_eq Y n B)]
    rw [show Kb(bt, pushChain Sphb Tb (subtypeIncl Tb (Sph Y (n + 1))) n
            (pushChain Xd Sphb
              (TopCat.ofHom ((sphFlat Y n).comp (capMapPairSph Y n))) n B))
        = Ks((sphPushCochain Y n ψ.1),
            pushChain Xd Sphb
              (TopCat.ofHom ((sphFlat Y n).comp (capMapPairSph Y n))) n B)
        from subtypeIncl_push_apply (X := Tb) (Sph Y (n + 1)) n bt
          (sphPushCochain Y n ψ.1) hbt _]
    rw [show Ks((sphPushCochain Y n ψ.1),
            pushChain Xd Sphb
              (TopCat.ofHom ((sphFlat Y n).comp (capMapPairSph Y n))) n B)
        = Km(ψ.1, pushChain Sphb MSphb sphUnflatH n
            (pushChain Xd Sphb
              (TopCat.ofHom ((sphFlat Y n).comp (capMapPairSph Y n))) n B))
        from sphPushCochain_pushChain Y n ψ.1
          (pushChain Xd Sphb
            (TopCat.ofHom ((sphFlat Y n).comp (capMapPairSph Y n))) n B)]
    rw [show pushChain Xd Sphb
            (TopCat.ofHom ((sphFlat Y n).comp (capMapPairSph Y n))) n B
        = pushChain MSphb Sphb sphFlatH n (pushChain Xd MSphb capMapH n B)
        from (pushChain_comp Xd MSphb Sphb capMapH sphFlatH n B).symm]
    rw [show Km(ψ.1, pushChain Sphb MSphb sphUnflatH n
            (pushChain MSphb Sphb sphFlatH n (pushChain Xd MSphb capMapH n B)))
        = Km(ψ.1, pushChain Xd MSphb capMapH n B)
        from congrArg (fun c => kronecker ℤ ssBm ψ.1 c)
          (sphUnflat_pushChain_sphFlat Y n (pushChain Xd MSphb capMapH n B))]
    rw [show Km(ψ.1, pushChain Xd MSphb capMapH n B)
        = Kd((RankTwo.pullCM (capMapPairSph Y n) ψ.1), B)
        from cochain_push_apply capMapH n ψ.1 B]
    exact tcmSuspAux.kronecker_capMapPairSph_eq Y n ψ hψrel hψclass B hB b hb hbc
  -- 10. assembly
  have hs1b : Kb(s.1, FZ(Z)) = Kb(dC bt, FZ(Z)) + Kb(dC v.1, FZ(Z)) := by
    rw [hs1]
    exact kronecker_add ℤ ssBb _ _ FZ(Z)
  have hbt_eval : Kb(dC bt, FZ(Z)) = Kb(bt, dCh FZ(Z)) :=
    singularCochain_d_apply_value (X := Tb) n bt FZ(Z)
  have hv_eval : Kb(dC v.1, FZ(Z)) = Kb(v.1, dCh FZ(Z)) :=
    singularCochain_d_apply_value (X := Tb) n v.1 FZ(Z)
  have hbt_split : Kb(bt, FCB(B) + FL(L)) = Kb(bt, FCB(B)) + Kb(bt, FL(L)) :=
    map_add (show Cochain ℤ ssBb n from bt) FCB(B) FL(L)
  have hv_split : Kb(v.1, FCB(B) + FL(L)) = Kb(v.1, FCB(B)) + Kb(v.1, FL(L)) :=
    map_add (show Cochain ℤ ssBb n from v.1) FCB(B) FL(L)
  calc Kw((show Cochain ℤ ssBw (n + 1) from
        (ModuleCat.Hom.hom ((dualChainMap ℤ Xw Tb tcmFH).f (n + 1))) s.1), Z)
      = Kb(s.1, FZ(Z)) := (cochain_push_apply tcmFH (n + 1) s.1 Z).symm
    _ = Kb(dC bt, FZ(Z)) + Kb(dC v.1, FZ(Z)) := hs1b
    _ = Kb(bt, dCh FZ(Z)) + Kb(v.1, dCh FZ(Z)) := by rw [hbt_eval, hv_eval]
    _ = Kb(bt, FCB(B) + FL(L)) + Kb(v.1, FCB(B) + FL(L)) := by rw [hdFZ]
    _ = (Kb(bt, FCB(B)) + Kb(bt, FL(L))) + (Kb(v.1, FCB(B)) + Kb(v.1, FL(L))) := by
          rw [hbt_split, hv_split]
    _ = Kd((show Cochain ℤ ssBd n from b.1), B) := by
          rw [hbt_cap, hbt_L, hv_cap, hv_L]; ring

end General

theorem modelFiller (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (B : (Work.Cohomology.singularChains ℤ (TopCat.of (Y × Work.Thom.MBall n))).X n)
    (hB : Work.Cohomology.IsSmallChain (Work.Thom.DiscB Y n) (∅ : Set (Y × Work.Thom.MBall n))
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Y × Work.Thom.MBall n))).d n (n - 1) B))
    (L : (Work.Cohomology.singularChains ℤ (TopCat.of (Work.Whitney.tcmX Y n 1))).X n)
    (hL : Work.Cohomology.IsSmallChain
        (fun x : Work.Whitney.tcmX Y n 1 => (Work.Whitney.tcmF Y n 1 x).2 ∈ Work.Thom.mLower n)
        (∅ : Set (Work.Whitney.tcmX Y n 1)) L)
    (Z : (Work.Cohomology.singularChains ℤ (TopCat.of (Work.Whitney.tcmX Y n 1))).X (n + 1))
    (hZ : (Work.Cohomology.singularChains ℤ (TopCat.of (Work.Whitney.tcmX Y n 1))).d (n + 1) n Z
      = Work.Cohomology.pushChain (TopCat.of (Y × Work.Thom.MBall n))
          (TopCat.of (Work.Whitney.tcmX Y n 1)) (TopCat.ofHom (Work.Whitney.capX Y n)) n B + L)
    (s : ↥(Work.Cohomology.relKern ℤ (TopCat.of (Y × EuclideanSpace ℝ (Fin (n + 1))))
      (Work.Thom.Punct Y (n + 1)) (n + 1)))
    (hs : Work.Cohomology.relDiffLM ℤ (TopCat.of (Y × EuclideanSpace ℝ (Fin (n + 1))))
      (Work.Thom.Punct Y (n + 1)) (n + 1) s = 0)
    (hsr : Work.Cohomology.relClassOf ℤ (TopCat.of (Y × EuclideanSpace ℝ (Fin (n + 1))))
      (Work.Thom.Punct Y (n + 1)) s hs = Work.Thom.Mpun (n + 1) Y)
    (b : ↥(Work.Cohomology.relKern ℤ (TopCat.of (Y × Work.Thom.MBall n)) (Work.Thom.DiscB Y n) n))
    (hb : Work.Cohomology.relDiffLM ℤ (TopCat.of (Y × Work.Thom.MBall n))
      (Work.Thom.DiscB Y n) n b = 0)
    (hbc : Work.Cohomology.relClassOf ℤ (TopCat.of (Y × Work.Thom.MBall n))
      (Work.Thom.DiscB Y n) b hb = Work.Thom.stepDisc Y n (Work.Thom.Mn n Y)) :
    Work.Cohomology.kronecker ℤ (Work.Whitney.ssB (Work.Whitney.tcmX Y n 1))
      (show Work.Cohomology.Cochain ℤ (Work.Whitney.ssB (Work.Whitney.tcmX Y n 1)) (n + 1) from
        (ModuleCat.Hom.hom ((Work.Cohomology.dualChainMap ℤ (TopCat.of (Work.Whitney.tcmX Y n 1))
          (TopCat.of (Y × EuclideanSpace ℝ (Fin (n + 1))))
          (TopCat.ofHom (Work.Whitney.tcmF Y n 1))).f (n + 1))) s.1) Z
      = Work.Cohomology.kronecker ℤ (Work.Whitney.ssB (Y × Work.Thom.MBall n)) b.1 B :=
  mf_modelSideCap Y n B hB L hL Z hZ s hs hsr b hb hbc

end

end Work.Whitney
