import Mathlib
import Submission.Work.Cohomology.Crux.vkOvlDefs
import Submission.Work.Cohomology.Crux.vkOvlModelDefs
import Submission.Work.Cohomology.Crux.vkOvlModelHomotopies
import Submission.Work.Cohomology.localHomology

set_option synthInstance.maxHeartbeats 400000


/-!
# The comparison map of pairs `(U ∩ V, (U ∩ V) ∩ Mk) → (S³ × D⁴, S³ × S³)`

This file builds the explicit homotopy equivalence of pairs from the overlap of the two chart images
of `Vk (-2)` to the model pair `(S³ × D⁴, S³ × S³)`: the chart identification `ovlHomeo` of the
overlap with the gluing region `ovlV = {x ≠ 0} × ℍ`, the radial retraction of the base
(`pS`/`pSi`) and the fibrewise radial retraction `PhiM`/`PsiM`, together with an explicit radial
homotopy `Hval`.  It then records that the induced chain maps on the total space and on the
sphere-bundle parts are quasi-isomorphisms.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

namespace Work.Cohomology.Crux

open CategoryTheory AlgebraicTopology
open scoped Topology unitInterval

noncomputable section

/-- The model total-space map `ovlV → S³ × D⁴`. -/
def Fmap : C(ovlV, ↥PairXT) := PhiM.comp pS

/-- The inverse-up-to-homotopy `S³ × D⁴ → ovlV`. -/
def Gmap : C(↥PairXT, ovlV) := pSi.comp PsiM

/-- The explicit homotopy from the identity to `Gmap ∘ Fmap`. -/
def Hval (z : I × ovlV) : Submission.Milnor.MSpace8 :=
  (((1 - (z.1 : ℝ)) + (z.1 : ℝ) * (‖((z.2 : ovlV) : Submission.Milnor.MSpace8).1‖ : ℝ)⁻¹) •
      ((z.2 : ovlV) : Submission.Milnor.MSpace8).1,
   ((1 - (z.1 : ℝ)) + (z.1 : ℝ) * rho ((z.2 : ovlV) : Submission.Milnor.MSpace8).2) •
      ((z.2 : ovlV) : Submission.Milnor.MSpace8).2)

theorem Hval_mem (z : I × ovlV) : Hval z ∈ Submission.Milnor.vOpens := by
  rw [Submission.Milnor.mem_vOpens]
  have hx : ((z.2 : ovlV) : Submission.Milnor.MSpace8).1 ≠ 0 :=
    Submission.Milnor.mem_vOpens.mp z.2.2
  have hxpos : 0 < ‖((z.2 : ovlV) : Submission.Milnor.MSpace8).1‖ := norm_pos_iff.mpr hx
  have ht0 : 0 ≤ (z.1 : ℝ) := z.1.2.1
  have hpos : 0 < (1 - (z.1 : ℝ)) + (z.1 : ℝ) *
      (‖((z.2 : ovlV) : Submission.Milnor.MSpace8).1‖ : ℝ)⁻¹ := by
    rcases eq_or_lt_of_le (z.1.2.2 : (z.1 : ℝ) ≤ 1) with h | h
    · rw [h]; norm_num; exact hx
    · have h1 : 0 < 1 - (z.1 : ℝ) := by linarith
      have h2 : 0 ≤ (z.1 : ℝ) * (‖((z.2 : ovlV) : Submission.Milnor.MSpace8).1‖ : ℝ)⁻¹ :=
        mul_nonneg ht0 (le_of_lt (inv_pos.mpr hxpos))
      linarith
  exact smul_ne_zero (ne_of_gt hpos) hx

theorem continuous_Hval : Continuous Hval := by
  have hq : Continuous fun z : I × ovlV => ((z.2 : ovlV) : Submission.Milnor.MSpace8) :=
    continuous_subtype_val.comp continuous_snd
  have ht : Continuous fun z : I × ovlV => (z.1 : ℝ) := continuous_subtype_val.comp continuous_fst
  have hxi : Continuous fun z : I × ovlV =>
      (‖((z.2 : ovlV) : Submission.Milnor.MSpace8).1‖ : ℝ)⁻¹ :=
    (hq.fst.norm).inv₀ (fun z => ne_of_gt (norm_pos_iff.mpr
      (Submission.Milnor.mem_vOpens.mp z.2.2)))
  have hρ : Continuous fun z : I × ovlV => rho ((z.2 : ovlV) : Submission.Milnor.MSpace8).2 :=
    continuous_rho.comp hq.snd
  have hc1 : Continuous fun z : I × ovlV =>
      (1 - (z.1 : ℝ)) + (z.1 : ℝ) *
        (‖((z.2 : ovlV) : Submission.Milnor.MSpace8).1‖ : ℝ)⁻¹ :=
    (continuous_const.sub ht).add (ht.mul hxi)
  have hc2 : Continuous fun z : I × ovlV =>
      (1 - (z.1 : ℝ)) + (z.1 : ℝ) * rho ((z.2 : ovlV) : Submission.Milnor.MSpace8).2 :=
    (continuous_const.sub ht).add (ht.mul hρ)
  exact Continuous.prodMk (hc1.smul hq.fst) (hc2.smul hq.snd)

theorem Hval_zero (q : ovlV) :
    (⟨Hval (0, q), Hval_mem (0, q)⟩ : ovlV) = q := by
  apply Subtype.ext
  simp [Hval]

theorem Hval_one (q : ovlV) :
    (⟨Hval (1, q), Hval_mem (1, q)⟩ : ovlV) = Gmap (Fmap q) := by
  apply Subtype.ext
  show Hval (1, q) = ((Gmap (Fmap q) : ovlV) : Submission.Milnor.MSpace8)
  have hG : ((Gmap (Fmap q) : ovlV) : Submission.Milnor.MSpace8)
      = ((((‖((q : ovlV) : Submission.Milnor.MSpace8).1‖ : ℝ)⁻¹) •
            ((q : ovlV) : Submission.Milnor.MSpace8).1),
         rho ((q : ovlV) : Submission.Milnor.MSpace8).2 •
            ((q : ovlV) : Submission.Milnor.MSpace8).2) := by
    rw [show (Gmap (Fmap q) : ovlV) = pSi (PsiM (PhiM (pS q))) from rfl]
    rw [pSi_apply, pS_apply, PhiM_apply, PsiM_apply, vSphProj_apply]
    apply Prod.ext
    · rfl
    · show linIsom.symm (fibRetract ((q : ovlV) : Submission.Milnor.MSpace8).2)
        = rho ((q : ovlV) : Submission.Milnor.MSpace8).2 •
            ((q : ovlV) : Submission.Milnor.MSpace8).2
      rw [fibRetract, map_smul, LinearIsometryEquiv.symm_apply_apply]
  rw [hG]
  apply Prod.ext
  · show ((1 - 1 + 1 * (‖((q : ovlV) : Submission.Milnor.MSpace8).1‖ : ℝ)⁻¹) •
        ((q : ovlV) : Submission.Milnor.MSpace8).1) = _
    norm_num
  · show ((1 - 1 + 1 * rho ((q : ovlV) : Submission.Milnor.MSpace8).2) •
        ((q : ovlV) : Submission.Milnor.MSpace8).2) = _
    norm_num

theorem Hval_mem_A (z : I × ovlV) (hz : (z.2 : ovlV) ∈ ovlVA) :
    (⟨Hval z, Hval_mem z⟩ : ovlV) ∈ ovlVA := by
  show ‖(Hval z).2‖ = 1
  have hρ : rho ((z.2 : ovlV) : Submission.Milnor.MSpace8).2 = 1 :=
    rho_of_norm_le_one (le_of_eq hz)
  rw [show (Hval z).2 = ((1 - (z.1 : ℝ)) + (z.1 : ℝ) *
        rho ((z.2 : ovlV) : Submission.Milnor.MSpace8).2) •
        ((z.2 : ovlV) : Submission.Milnor.MSpace8).2 from rfl]
  rw [norm_smul, hz, mul_one, hρ, mul_one]
  rw [show (1 - (z.1 : ℝ)) + (z.1 : ℝ) = 1 by ring, norm_one]

/-- The homotopy `id ~ Gmap ∘ Fmap`, as a continuous map `I × ovlV → ovlV`. -/
def Hcont : C(I × ovlV, ovlV) where
  toFun z := ⟨Hval z, Hval_mem z⟩
  continuous_toFun := continuous_Hval.subtype_mk Hval_mem

/-- The homotopy from the identity to `Gmap ∘ Fmap`. -/
def HhomV : ContinuousMap.Homotopy (ContinuousMap.id ovlV) (Gmap.comp Fmap) :=
  ContinuousMap.Homotopy.mk Hcont Hval_zero Hval_one

theorem Fmap_comp_Gmap : Fmap.comp Gmap = ContinuousMap.id ↥PairXT := by
  apply ContinuousMap.ext
  intro p
  have h1 : pS (pSi (PsiM p)) = PsiM p :=
    congrArg (fun (f : C(S3H, S3H)) => f (PsiM p)) pS_comp_pSi
  have h2 : PhiM (PsiM p) = p :=
    congrArg (fun (f : C(↥PairXT, ↥PairXT)) => f p) PhiM_comp_PsiM
  show PhiM (pS (pSi (PsiM p))) = p
  rw [h1, h2]






/-- The homotopy equivalence `ovlV ≃ PairXT` of total spaces. -/
def e₂ : ContinuousMap.HomotopyEquiv ovlV ↥PairXT where
  toFun := Fmap
  invFun := Gmap
  left_inv := ⟨HhomV.symm⟩
  right_inv := by rw [Fmap_comp_Gmap]

/-! ## The A-part -/

theorem ftotA_mem (x : ↥vkOvlA) : Fmap (ovlHomeo x.1) ∈ PairAT :=
  PhiM_mem_PairAT (pS_mem_S3HA ((ovlHomeo_mem_ovlVA_iff x.1).mpr x.2))

theorem continuous_ftotA : Continuous fun x : ↥vkOvlA => Fmap (ovlHomeo x.1) :=
  Fmap.continuous.comp (ovlHomeo.continuous.comp continuous_subtype_val)

/-- The A-part of `Fmap ∘ ovlHomeo`. -/
def ftotA : C(↥vkOvlA, ↥PairAT) where
  toFun x := ⟨Fmap (ovlHomeo x.1), ftotA_mem x⟩
  continuous_toFun := continuous_ftotA.subtype_mk ftotA_mem

theorem gtotA_mem (p : ↥PairAT) : ovlHomeo.symm (Gmap p) ∈ vkOvlA :=
  (ovlHomeo_mem_ovlVA_iff _).mp (by
    rw [Homeomorph.apply_symm_apply]
    exact pSi_mem_ovlVA (PsiM_mem_S3HA p.2))

theorem continuous_gtotA : Continuous fun p : ↥PairAT => ovlHomeo.symm (Gmap p) :=
  ovlHomeo.symm.continuous.comp (Gmap.continuous.comp continuous_subtype_val)

/-- The A-part of `Gmap ∘ ovlHomeo.symm`. -/
def gtotA : C(↥PairAT, ↥vkOvlA) where
  toFun p := ⟨ovlHomeo.symm (Gmap p), gtotA_mem p⟩
  continuous_toFun := continuous_gtotA.subtype_mk gtotA_mem

theorem HvalA_mem (z : I × ↥vkOvlA) :
    ovlHomeo.symm (⟨Hval (z.1, ovlHomeo z.2.1), Hval_mem _⟩ : ovlV) ∈ vkOvlA :=
  (ovlHomeo_mem_ovlVA_iff _).mp (by
    rw [Homeomorph.apply_symm_apply]
    exact Hval_mem_A (z.1, ovlHomeo z.2.1) ((ovlHomeo_mem_ovlVA_iff z.2.1).mpr z.2.2))

/-- The A-part radial homotopy. -/
def HtotAval (z : I × ↥vkOvlA) : ↥vkOvlA :=
  ⟨ovlHomeo.symm (⟨Hval (z.1, ovlHomeo z.2.1), Hval_mem _⟩ : ovlV), HvalA_mem z⟩

theorem continuous_HtotAval : Continuous fun z : I × ↥vkOvlA =>
    ovlHomeo.symm (⟨Hval (z.1, ovlHomeo z.2.1), Hval_mem _⟩ : ovlV) := by
  refine (ovlHomeo.symm.continuous).comp ?_
  refine (continuous_Hval.comp ?_).subtype_mk _
  have hv : Continuous fun z : I × ↥vkOvlA => ((z.2 : ↥vkOvlA) : ↥(vkU ∩ vkV)) :=
    (continuous_subtype_val : Continuous (Subtype.val : ↥vkOvlA → ↥(vkU ∩ vkV))).comp
      continuous_snd
  exact continuous_fst.prodMk (ovlHomeo.continuous.comp hv)

theorem HtotAval_zero (z : ↥vkOvlA) : HtotAval (0, z) = z := by
  apply Subtype.ext
  show ovlHomeo.symm (⟨Hval (0, ovlHomeo z), Hval_mem _⟩ : ovlV) = z
  rw [show (⟨Hval (0, ovlHomeo z), Hval_mem _⟩ : ovlV) = ovlHomeo z from
    Hval_zero (ovlHomeo z)]
  exact Homeomorph.symm_apply_apply ovlHomeo z

theorem HtotAval_one (z : ↥vkOvlA) : HtotAval (1, z) = gtotA (ftotA z) := by
  apply Subtype.ext
  show ovlHomeo.symm (⟨Hval (1, ovlHomeo z), Hval_mem _⟩ : ovlV) = ovlHomeo.symm (Gmap (ftotA z))
  rw [show (⟨Hval (1, ovlHomeo z), Hval_mem _⟩ : ovlV) = Gmap (Fmap (ovlHomeo z)) from
    Hval_one (ovlHomeo z)]
  rfl

def HtotA : C(I × ↥vkOvlA, ↥vkOvlA) := ⟨HtotAval, continuous_HtotAval.subtype_mk HvalA_mem⟩

/-- The homotopy `id ~ gtotA ∘ ftotA` on the A-part. -/
def HhomA :
    ContinuousMap.Homotopy (ContinuousMap.id ↥vkOvlA) (gtotA.comp ftotA) :=
  ContinuousMap.Homotopy.mk HtotA HtotAval_zero HtotAval_one

theorem ftotA_comp_gtotA : ftotA.comp gtotA = ContinuousMap.id ↥PairAT := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  show Fmap (ovlHomeo (ovlHomeo.symm (Gmap p))) = (p : ↥PairXT)
  rw [Homeomorph.apply_symm_apply]
  have h1 : pS (pSi (PsiM p)) = PsiM p :=
    congrArg (fun (f : C(S3H, S3H)) => f (PsiM p)) pS_comp_pSi
  have h2 : PhiM (PsiM p) = p :=
    congrArg (fun (f : C(↥PairXT, ↥PairXT)) => f p) PhiM_comp_PsiM
  show PhiM (pS (pSi (PsiM p))) = (p : ↥PairXT)
  rw [h1, h2]

/-- The homotopy equivalence of pairs on the A-parts. -/
def eTotA : ContinuousMap.HomotopyEquiv ↥vkOvlA ↥PairAT where
  toFun := ftotA
  invFun := gtotA
  left_inv := ⟨HhomA.symm⟩
  right_inv := by rw [ftotA_comp_gtotA]

/-! ## The composite on the overlap -/

def ftot : C(↥(vkU ∩ vkV), ↥PairXT) := Fmap.comp ovlHomeo.toHomotopyEquiv.toFun

def gtot : C(↥PairXT, ↥(vkU ∩ vkV)) := ovlHomeo.symm.toHomotopyEquiv.toFun.comp Gmap

def HtotVal (z : I × ↥(vkU ∩ vkV)) : ↥(vkU ∩ vkV) :=
  ovlHomeo.symm (⟨Hval (z.1, ovlHomeo z.2), Hval_mem _⟩ : ovlV)

theorem continuous_HtotVal : Continuous HtotVal := by
  refine (ovlHomeo.symm.continuous).comp ?_
  refine (continuous_Hval.comp ?_).subtype_mk _
  exact continuous_fst.prodMk (ovlHomeo.continuous.comp continuous_snd)

theorem HtotVal_zero (z : ↥(vkU ∩ vkV)) : HtotVal (0, z) = z := by
  show ovlHomeo.symm (⟨Hval (0, ovlHomeo z), Hval_mem _⟩ : ovlV) = z
  rw [show (⟨Hval (0, ovlHomeo z), Hval_mem _⟩ : ovlV) = ovlHomeo z from Hval_zero (ovlHomeo z)]
  exact Homeomorph.symm_apply_apply ovlHomeo z

theorem HtotVal_one (z : ↥(vkU ∩ vkV)) : HtotVal (1, z) = gtot (ftot z) := by
  show ovlHomeo.symm (⟨Hval (1, ovlHomeo z), Hval_mem _⟩ : ovlV)
    = ovlHomeo.symm (Gmap (Fmap (ovlHomeo z)))
  rw [show (⟨Hval (1, ovlHomeo z), Hval_mem _⟩ : ovlV) = Gmap (Fmap (ovlHomeo z)) from
    Hval_one (ovlHomeo z)]

def Htot : C(I × ↥(vkU ∩ vkV), ↥(vkU ∩ vkV)) := ⟨HtotVal, continuous_HtotVal⟩

/-- The homotopy `id ~ gtot ∘ ftot` on the overlap. -/
def HhomTot :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(vkU ∩ vkV)) (gtot.comp ftot) :=
  ContinuousMap.Homotopy.mk Htot HtotVal_zero HtotVal_one

theorem ftot_comp_gtot : ftot.comp gtot = ContinuousMap.id ↥PairXT := by
  apply ContinuousMap.ext
  intro z
  show Fmap (ovlHomeo (ovlHomeo.symm (Gmap z))) = z
  rw [Homeomorph.apply_symm_apply]
  have h : Fmap (Gmap z) = z := by
    simpa using congrArg (fun (f : C(↥PairXT, ↥PairXT)) => f z) Fmap_comp_Gmap
  exact h

/-- The homotopy equivalence `(U ∩ V) ≃ PairXT` of total spaces. -/
def eTot : ContinuousMap.HomotopyEquiv ↥(vkU ∩ vkV) ↥PairXT where
  toFun := ftot
  invFun := gtot
  left_inv := ⟨HhomTot.symm⟩
  right_inv := by rw [ftot_comp_gtot]

/-! ## The comparison map of pairs and the three isomorphisms -/

/-- The map of pairs `(U ∩ V, (U ∩ V) ∩ Mk) → (S³ × D⁴, S³ × S³)` on the total spaces. -/
abbrev ovlPairMap : vkOvl ⟶ PairXT := TopCat.ofHom eTot.toFun

theorem ovlPairMap_mem (x : ↥vkOvl) (hx : x ∈ vkOvlA) : ovlPairMap x ∈ PairAT := by
  show Fmap (ovlHomeo x) ∈ PairAT
  exact ftotA_mem ⟨x, hx⟩

/-- The comparison map is a quasi-isomorphism on the total spaces. -/
theorem ovlPairMap_chainMap_isIso (k : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (chainMap ℤ vkOvl PairXT ovlPairMap) k) :=
  Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv (X := vkOvl) (Y := PairXT) eTot k

/-- The restriction of the comparison map to the sphere-bundle parts is the A-part comparison. -/
theorem relMapSub_ovlPairMap_eq :
    relMapSub vkOvlA PairAT ovlPairMap ovlPairMap_mem = TopCat.ofHom eTotA.toFun := by
  apply TopCat.ext
  intro x
  apply Subtype.ext
  rfl

/-- The comparison map is a quasi-isomorphism on the sphere-bundle parts. -/
theorem ovlPairMapA_chainMap_isIso (k : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of vkOvlA)
      (TopCat.of PairAT) (relMapSub vkOvlA PairAT ovlPairMap ovlPairMap_mem)) k) := by
  rw [relMapSub_ovlPairMap_eq]
  exact Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv
    (X := TopCat.of vkOvlA) (Y := TopCat.of PairAT) eTotA k

end

end Work.Cohomology.Crux
