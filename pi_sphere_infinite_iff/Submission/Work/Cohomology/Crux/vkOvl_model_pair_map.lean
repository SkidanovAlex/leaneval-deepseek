import Mathlib
import Submission.Work.Cohomology.Crux.vkOvlDefs
import Submission.Work.Cohomology.RelCapHTransfer
import Submission.Work.Cohomology.exists_relComplexMap
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.cohomologyPairVk
import Submission.Work.Cohomology.sphere3DiscPairDefs
import Submission.Work.Cohomology.homotopyEquiv
import Submission.Work.Milnor.VBundleDefs
import Submission.Work.Glue.Basic
import Submission.Work.Cohomology.Crux.vkOvlModelDefs
import Submission.Work.Cohomology.Crux.vkOvlModelHomotopies

set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

namespace Work.Cohomology.Crux

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology unitInterval

noncomputable section

def eA : ↥vkOvlA ≃ₜ ↥ovlVA where
  toFun a := ⟨ovlHomeo (a : ↥(vkU ∩ vkV)), (mem_vkOvlA_iff _).mp a.2⟩
  invFun q := ⟨ovlHomeo.symm (q : ovlV), by
    refine (mem_vkOvlA_iff _).mpr ?_
    show (ovlHomeo (ovlHomeo.symm (q : ovlV)) : ovlV) ∈ ovlVA
    rw [Homeomorph.apply_symm_apply]
    exact q.2⟩
  left_inv a := by
    apply Subtype.ext
    exact Homeomorph.symm_apply_apply ovlHomeo _
  right_inv q := by
    apply Subtype.ext
    exact Homeomorph.apply_symm_apply ovlHomeo _
  continuous_toFun := Continuous.subtype_mk
    (ovlHomeo.continuous_toFun.comp continuous_subtype_val)
    (fun a => (mem_vkOvlA_iff (a : ↥(vkU ∩ vkV))).mp a.2)
  continuous_invFun := Continuous.subtype_mk
    (ovlHomeo.symm.continuous_toFun.comp continuous_subtype_val)
    (fun q => (mem_vkOvlA_iff _).mpr (by
      show (ovlHomeo (ovlHomeo.symm (q : ovlV)) : ovlV) ∈ ovlVA
      rw [Homeomorph.apply_symm_apply]
      exact q.2))

def PhiA : C(↥S3HA, ↥PairAT) where
  toFun p := ⟨PhiM (p : S3H), PhiM_mem_PairAT p.2⟩
  continuous_toFun := (PhiM.continuous.comp continuous_subtype_val).subtype_mk
    (fun p => PhiM_mem_PairAT p.2)

def PsiA : C(↥PairAT, ↥S3HA) where
  toFun p := ⟨PsiM (p : ↥PairXT), PsiM_mem_S3HA p.2⟩
  continuous_toFun := (PsiM.continuous.comp continuous_subtype_val).subtype_mk
    (fun p => PsiM_mem_S3HA p.2)

def pSA : C(↥ovlVA, ↥S3HA) where
  toFun q := ⟨pS (q : ovlV), pS_mem_S3HA q.2⟩
  continuous_toFun := (pS.continuous.comp continuous_subtype_val).subtype_mk
    (fun q => pS_mem_S3HA q.2)

def pSiA : C(↥S3HA, ↥ovlVA) where
  toFun p := ⟨pSi (p : S3H), pSi_mem_ovlVA p.2⟩
  continuous_toFun := (pSi.continuous.comp continuous_subtype_val).subtype_mk
    (fun p => pSi_mem_ovlVA p.2)

theorem PsiA_comp_PhiA : PsiA.comp PhiA = ContinuousMap.id ↥S3HA := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  show PsiM (PhiM (p : S3H)) = (p : S3H)
  rw [PhiM_apply, PsiM_apply]
  apply Prod.ext
  · rfl
  · show linIsom.symm (fibRetract (p : S3H).2) = (p : S3H).2
    rw [fibRetract_of_norm_eq_one p.2, linIsom.symm_apply_apply]

theorem PhiA_comp_PsiA : PhiA.comp PsiA = ContinuousMap.id ↥PairAT := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  exact DFunLike.congr_fun PhiM_comp_PsiM (p : ↥PairXT)

theorem pSA_comp_pSiA : pSA.comp pSiA = ContinuousMap.id ↥S3HA := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  exact DFunLike.congr_fun pS_comp_pSi (p : S3H)

theorem pSiA_comp_pSA_homotopic :
    (pSiA.comp pSA).Homotopic (ContinuousMap.id ↥ovlVA) := by
  obtain ⟨H, hH⟩ := vkOvlBaseHomotopy
  refine ⟨ContinuousMap.Homotopy.mk
    ⟨fun z => ⟨H.toFun (z.1, (z.2 : ovlV)), hH z.1 (z.2 : ovlV) z.2.2⟩, ?_⟩ ?_ ?_⟩
  · exact (H.continuous.comp (Continuous.prodMk continuous_fst
      (continuous_subtype_val.comp continuous_snd))).subtype_mk
      (fun z => hH z.1 (z.2 : ovlV) z.2.2)
  · intro q
    apply Subtype.ext
    show H.toFun (0, (q : ovlV)) = ((pSiA.comp pSA) q : ovlV)
    exact H.map_zero_left (q : ovlV)
  · intro q
    apply Subtype.ext
    show H.toFun (1, (q : ovlV)) = (q : ovlV)
    exact H.map_one_left (q : ovlV)

def pSeA : ContinuousMap.HomotopyEquiv ↥ovlVA ↥S3HA where
  toFun := pSA
  invFun := pSiA
  left_inv := pSiA_comp_pSA_homotopic
  right_inv := ⟨by rw [pSA_comp_pSiA]; exact ContinuousMap.Homotopy.refl _⟩

def PhieA : ContinuousMap.HomotopyEquiv ↥S3HA ↥PairAT where
  toFun := PhiA
  invFun := PsiA
  left_inv := ⟨by rw [PsiA_comp_PhiA]; exact ContinuousMap.Homotopy.refl _⟩
  right_inv := ⟨by rw [PhiA_comp_PsiA]; exact ContinuousMap.Homotopy.refl _⟩

def feA : ContinuousMap.HomotopyEquiv ↥vkOvlA ↥PairAT :=
  (eA.toHomotopyEquiv).trans (pSeA.trans PhieA)

def pSe : ContinuousMap.HomotopyEquiv ovlV S3H where
  toFun := pS
  invFun := pSi
  left_inv := by
    obtain ⟨H, -⟩ := vkOvlBaseHomotopy
    exact ⟨H⟩
  right_inv := ⟨by rw [pS_comp_pSi]; exact ContinuousMap.Homotopy.refl _⟩

def Phie : ContinuousMap.HomotopyEquiv S3H ↥PairXT where
  toFun := PhiM
  invFun := PsiM
  left_inv := vkOvlFibreHomotopy
  right_inv := ⟨by rw [PhiM_comp_PsiM]; exact ContinuousMap.Homotopy.refl _⟩

def fe : ContinuousMap.HomotopyEquiv ↥(vkU ∩ vkV) ↥PairXT :=
  (ovlHomeo.toHomotopyEquiv).trans (pSe.trans Phie)

/-- The restriction of `fe` to the sphere-bundle parts is `feA`, so that `(fe, feA)` is a map of
pairs. -/
theorem fe_restrict_feA (a : ↥vkOvlA) :
    fe.toFun (a : ↥(vkU ∩ vkV)) = (feA.toFun a : ↥PairXT) := by
  show PhiM (pS (ovlHomeo (a : ↥(vkU ∩ vkV)))) = PhiM (pS (ovlHomeo (a : ↥(vkU ∩ vkV))))
  rfl

/-- **The overlap of the two charts of `Vk (-2)` is modelled by `(PairXT, PairAT) = (S³×D⁴, S³×S³)`.**

There is a map of pairs `f : (U ∩ V, (U ∩ V) ∩ Mk(-2)) ⟶ (S³ × D⁴, S³ × S³)` (with its restriction
`g` to the sphere-bundle parts, and the compatibility `w` saying that it is a map of pairs) which is a
homotopy equivalence of pairs: it is an isomorphism on the absolute homology in degree `3` and on the
*relative* homology of the pairs in degree `7`.

The intended construction: in the first chart `ιX` the overlap `U ∩ V` is `{(x,y) : x ≠ 0}` inside
`ℝ⁴ × ℍ` (see `Work.Glue.Data.preimage_image_U`, `Work.Glue.Data.homX_symm_apply` and
`Submission.Milnor.mem_vOpens`), the sphere bundle part is `‖y‖ = 1`, and the map is
`(x,y) ↦ (x/‖x‖, y/max 1 ‖y‖)`: the radial retraction on the base combined with the radial
retraction of `ℍ` onto the closed unit ball.  Its homotopy inverse is the obvious inclusion
`(s,z) ↦ (s,z)`, and the two homotopies are the radial homotopies (which preserve the sphere bundle
part setwise, so they are homotopies of pairs).  The three isomorphism statements then follow from
`Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv` (with the `ContinuousMap.HomotopyEquiv`
built from the explicit homotopies) and `Work.Cohomology.relChainsMapOf_homologyMap_isIso`
(`Submission/Work/Cohomology/localHomology.lean`), which needs the component maps to be
quasi-isomorphisms in *every* degree — so it is worth proving the stronger all-degrees statement
`∀ n, IsIso (homologyMap (chainMap ℤ _ _ f) n)` and its analogue for `g`, rather than only the
degrees named below.  (`H₃` of the sphere-bundle parts is `ℤ²`, so that conjunct is an isomorphism of
`ℤ²`.)

The identification `ℍ ≅ EuclideanSpace ℝ (Fin 4)` is `Quaternion.linearIsometryEquivTuple`; the model
pair is `PairXT = Sph3T × Disc4T` and `PairAT = {p | p.2 ∈ sphereInUnit 4}`
(`Submission/Work/Cohomology/sphere3DiscPairDefs.lean`).  (The composite in the statement of `w` is
written `CategoryTheory.CategoryStruct.comp` because the statement is elaborated in a bare file; the
child should feel free to restate it with `≫` inside its own file as long as the statement is the
same.) -/
theorem vkOvl_model_pair_map :
    ∃ (f : TopCat.of ↥(Work.Cohomology.Crux.vkU ∩ Work.Cohomology.Crux.vkV) ⟶
        Work.Cohomology.PairXT)
      (g : TopCat.of ↥(Work.Cohomology.Crux.vkOvlA) ⟶
        TopCat.of Work.Cohomology.PairAT)
      (w : (CategoryTheory.CategoryStruct.comp
              (Work.Cohomology.subtypeIncl
                (TopCat.of ↥(Work.Cohomology.Crux.vkU ∩ Work.Cohomology.Crux.vkV))
                Work.Cohomology.Crux.vkOvlA) f
            = CategoryTheory.CategoryStruct.comp g
                (Work.Cohomology.subtypeIncl Work.Cohomology.PairXT Work.Cohomology.PairAT))),
      CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
        (TopCat.of ↥(Work.Cohomology.Crux.vkU ∩ Work.Cohomology.Crux.vkV))
        Work.Cohomology.PairXT f) 3) ∧
      CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
        (TopCat.of ↥(Work.Cohomology.Crux.vkOvlA))
        (TopCat.of Work.Cohomology.PairAT) g) 3) ∧
      CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf
          (TopCat.of ↥(Work.Cohomology.Crux.vkU ∩ Work.Cohomology.Crux.vkV))
          Work.Cohomology.PairXT Work.Cohomology.Crux.vkOvlA Work.Cohomology.PairAT f g w) 7) := by
  have hw : (Work.Cohomology.subtypeIncl (TopCat.of ↥(vkU ∩ vkV)) vkOvlA) ≫
      TopCat.ofHom fe.toFun
      = TopCat.ofHom feA.toFun ≫ Work.Cohomology.subtypeIncl PairXT PairAT := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    exact fe_restrict_feA a
  refine ⟨TopCat.ofHom fe.toFun, TopCat.ofHom feA.toFun, hw, ?_, ?_, ?_⟩
  · exact isIso_homologyMap_chainMap_of_homotopyEquiv (X := TopCat.of ↥(vkU ∩ vkV)) (Y := PairXT)
      fe 3
  · exact isIso_homologyMap_chainMap_of_homotopyEquiv (X := TopCat.of ↥vkOvlA)
      (Y := TopCat.of PairAT) feA 3
  · refine relChainsMapOf_homologyMap_isIso (X := TopCat.of ↥(vkU ∩ vkV)) (Y := PairXT)
      vkOvlA PairAT (TopCat.ofHom fe.toFun) (TopCat.ofHom feA.toFun) hw 7 ?_ ?_
    · intro k
      exact isIso_homologyMap_chainMap_of_homotopyEquiv (X := TopCat.of ↥(vkU ∩ vkV))
        (Y := PairXT) fe k
    · intro k
      exact isIso_homologyMap_chainMap_of_homotopyEquiv (X := TopCat.of ↥vkOvlA)
        (Y := TopCat.of PairAT) feA k

end

end Work.Cohomology.Crux
