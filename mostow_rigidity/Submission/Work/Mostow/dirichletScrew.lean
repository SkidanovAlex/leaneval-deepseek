import Mathlib
import Submission.Work.Mostow.geodSetup
import Submission.Work.Mostow.torusData
import Submission.Work.Mostow.rescaledPoint
import Submission.Work.Mostow.screwExists
import Submission.Work.Mostow.countingCondition
import Submission.Work.Mostow.nearIdWeights
import Submission.Work.Mostow.axisDichotomy
import Submission.Work.Mostow.axisDatum
import Submission.Work.Mostow.ellipsoidVol
import Submission.Work.Mostow.ellipsoidMargRegion
import Submission.Work.Mostow.nearId_blk
import Submission.Work.Mostow.blk_smul_fermi
import Submission.Work.Mostow.resStd_hom_discrete
import Submission.Work.Mostow.nrmStdMulAndRotNConj
import Submission.Work.Mostow.normalPartsIndex
import Submission.Work.Mostow.cardTransversal
import Submission.Work.Mostow.axisTranslationCentralises
import Submission.Work.Mostow.hdistZpowFixedfree
import Submission.Work.Mostow.geeDisplacement
import Submission.Work.Mostow.geeStripMeasure
import Submission.Work.Mostow.geeFdTop
import Submission.Work.Mostow.geeAxisCovol
import Submission.Work.Mostow.existsFDone
import Submission.Work.Mostow.finite_fixes_of_sq_eq_one
import Submission.Work.Mostow.finiteFDmeasureTop
import Submission.Work.Mostow.detBoundBlockE
import Submission.Work.Mostow.rotN_le_of_blockWeights
import Submission.Work.Mostow.exists_eta0_screw
import Submission.Work.Mostow.exists_mem_of_mem_closure_resStd
import Submission.Work.Mostow.eqOneOfPhiEqZero
import Submission.Work.Mostow.rotDispOfBlock
import Submission.Work.Mostow.detBoundBlockM
import Submission.Work.Mostow.chordLeRotN
import Submission.Work.Mostow.blockNormSqSum
import Submission.Work.Mostow.blk_hom
import Submission.Work.Mostow.axisGenFiniteAbelian
import Submission.Work.Mostow.normalPartsCommute
import Submission.Work.Mostow.geeVolStripTop
set_option maxHeartbeats 8000000

namespace Work.Mostow.DirichletScrew

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

lemma fermi_mem_stdTG (k m : ℕ) (v : Submission.Mostow.E k) (w : Submission.Mostow.E m) :
    Submission.Mostow.fermi k m v w ∈ Submission.Mostow.stdTG k m ↔ w = 0 := by
  constructor
  · intro h
    rw [Submission.Mostow.stdTG, Set.mem_range] at h
    obtain ⟨v', hv'⟩ := h
    have h1 : Submission.Mostow.nrmC k m (Submission.Mostow.fermi k m v w)
        = Submission.Mostow.nrmC k m (Submission.Mostow.coordEmb k m v') := by rw [hv']
    have h2 : Submission.Mostow.nrmC k m (Submission.Mostow.coordEmb k m v') = 0 := by
      rw [← Work.Mostow.rhd_fermi_zero_right k m v', Work.Mostow.nib_nrmC_fermi]
      simp
    rw [Work.Mostow.nib_nrmC_fermi, h2] at h1
    exact (smul_eq_zero.mp h1).resolve_left (ne_of_gt (Work.Mostow.rhd_sinhc_pos ‖w‖))
  · intro hw
    rw [Submission.Mostow.stdTG, Set.mem_range]
    exact ⟨v, by rw [← Work.Mostow.rhd_fermi_zero_right k m v, hw]⟩

/-- The block isometry preserves the standard stratum setwise. -/
lemma gsv2_mem_stab (k m : ℕ) (hAk : Submission.Mostow.POActionProp k)
    (hIk : Submission.Mostow.HypIsometryProp k)
    (hA : Submission.Mostow.POActionProp (k + m)) (hI : Submission.Mostow.HypIsometryProp (k + m))
    (h : LeanEval.Geometry.MostowRigidity.PO k 1)
    (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) :
    Submission.Mostow.blk k m h R ∈ Submission.Mostow.SetStabStd k m := by
  rw [Work.Mostow.rhd_mem_stab_iff]
  intro u
  obtain ⟨v, w, rfl⟩ : ∃ v w, u = Submission.Mostow.fermi k m v w :=
    ⟨(Submission.Mostow.fermiInv k m u).1, (Submission.Mostow.fermiInv k m u).2,
      ((Work.Mostow.fermi_inv k m).2.1 u).symm⟩
  rw [Work.Mostow.blk_smul_fermi k m hAk hIk hA hI h R v w, fermi_mem_stdTG, fermi_mem_stdTG]
  constructor
  · intro hw
    rw [hw, map_zero]
  · intro hw
    have h2 : R w = R 0 := by rw [hw, map_zero]
    exact R.injective h2

/-- The pointwise stabiliser of `stdTG 1 m` inside `Λ`: elements of `Λ` that preserve the geodesic
setwise and act trivially on it. -/
noncomputable def gsvPtSub (m : ℕ) (hA1 : Submission.Mostow.POActionProp 1)
    (hI1 : Submission.Mostow.HypIsometryProp 1)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)) :
    Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1) where
  carrier := {c | c ∈ geodStab m hA Λ ∧ Submission.Mostow.resStd 1 m c = 1}
  one_mem' := ⟨(geodStab m hA Λ).one_mem, Work.Mostow.rhd_resStd_one 1 m hA1 hI1 hA hI⟩
  mul_mem' := by
    intro a b ha hb
    refine ⟨(geodStab m hA Λ).mul_mem ha.1 hb.1, ?_⟩
    have haS : a ∈ Submission.Mostow.SetStabStd 1 m := (Subgroup.mem_inf.mp ha.1).2
    have hbS : b ∈ Submission.Mostow.SetStabStd 1 m := (Subgroup.mem_inf.mp hb.1).2
    rw [Work.Mostow.rhd_resStd_mul 1 m hA1 hI1 hA hI haS hbS, ha.2, hb.2, mul_one]
  inv_mem' := by
    intro a ha
    refine ⟨(geodStab m hA Λ).inv_mem ha.1, ?_⟩
    have haS : a ∈ Submission.Mostow.SetStabStd 1 m := (Subgroup.mem_inf.mp ha.1).2
    rw [Work.Mostow.rhd_resStd_inv 1 m hA1 hI1 hA hI haS, ha.2, inv_one]

lemma gsvPtSub_le_geodStab (m : ℕ) (hA1 : Submission.Mostow.POActionProp 1)
    (hI1 : Submission.Mostow.HypIsometryProp 1)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)) :
    gsvPtSub m hA1 hI1 hA hI Λ ≤ geodStab m hA Λ :=
  fun _ hc => hc.1

lemma gsvPtSub_mem_stab (m : ℕ) (hA1 : Submission.Mostow.POActionProp 1)
    (hI1 : Submission.Mostow.HypIsometryProp 1)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1))
    {c : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1} (hc : c ∈ gsvPtSub m hA1 hI1 hA hI Λ) :
    c ∈ Submission.Mostow.SetStabStd 1 m :=
  (Subgroup.mem_inf.mp hc.1).2

lemma gsvPtSub_resStd (m : ℕ) (hA1 : Submission.Mostow.POActionProp 1)
    (hI1 : Submission.Mostow.HypIsometryProp 1)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1))
    {c : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1} (hc : c ∈ gsvPtSub m hA1 hI1 hA hI Λ) :
    Submission.Mostow.resStd 1 m c = 1 := hc.2

/-- The finite subgroup of `O(m)` generated by the *small* normal parts of the pointwise stabiliser
of the standard geodesic. -/
noncomputable def gsvSmallNrm (m : ℕ) (hA1 : Submission.Mostow.POActionProp 1)
    (hI1 : Submission.Mostow.HypIsometryProp 1)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)) :
    Subgroup (Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) :=
  Subgroup.closure (Submission.Mostow.nrmStd 1 m ''
    {p : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1 |
      p ∈ gsvPtSub m hA1 hI1 hA hI Λ ∧ Submission.Mostow.rotN (Submission.Mostow.nrmStd 1 m p) ≤ 1 / 4})

lemma gsvSmallNrm_def (m : ℕ) (hA1 : Submission.Mostow.POActionProp 1)
    (hI1 : Submission.Mostow.HypIsometryProp 1)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)) :
    ∀ x : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m, x ∈ gsvSmallNrm m hA1 hI1 hA hI Λ ↔
      x ∈ Subgroup.closure (Submission.Mostow.nrmStd 1 m ''
        {p : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1 |
          p ∈ gsvPtSub m hA1 hI1 hA hI Λ ∧
            Submission.Mostow.rotN (Submission.Mostow.nrmStd 1 m p) ≤ 1 / 4}) :=
  fun _ => Iff.rfl

lemma gsvSmallNrm_gen (m : ℕ) (hA1 : Submission.Mostow.POActionProp 1)
    (hI1 : Submission.Mostow.HypIsometryProp 1)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)) :
    gsvSmallNrm m hA1 hI1 hA hI Λ
      = Subgroup.closure {a | a ∈ gsvSmallNrm m hA1 hI1 hA hI Λ ∧ Submission.Mostow.rotN a ≤ 1 / 4} := by
  refine le_antisymm ?_ ?_
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨p, hp, rfl⟩
    exact Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨p, hp, rfl⟩, hp.2⟩
  · exact (Subgroup.closure_le _).mpr fun x hx => hx.1

lemma gsvSmallNrm_comm (m : ℕ) (hm : 0 < m) (hA1 : Submission.Mostow.POActionProp 1)
    (hI1 : Submission.Mostow.HypIsometryProp 1)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1))
    (hdisc : IsDiscrete (SetLike.coe Λ)) :
    ∀ a ∈ gsvSmallNrm m hA1 hI1 hA hI Λ, ∀ b ∈ gsvSmallNrm m hA1 hI1 hA hI Λ, a * b = b * a :=
  normalPartsCommute m hm hA1 hI1 hA hI (gsvPtSub m hA1 hI1 hA hI Λ)
    (hdisc.mono fun c hc => (Subgroup.mem_inf.mp (gsvPtSub_le_geodStab m hA1 hI1 hA hI Λ hc)).1)
    (fun c hc => gsvPtSub_resStd m hA1 hI1 hA hI Λ hc)
    (gsvSmallNrm m hA1 hI1 hA hI Λ) rfl

lemma gsvSmallNrm_finite (m : ℕ) (hm : 0 < m) (hA1 : Submission.Mostow.POActionProp 1)
    (hI1 : Submission.Mostow.HypIsometryProp 1)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1))
    (hdisc : IsDiscrete (SetLike.coe Λ))
    (g : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)
    (hg : g ∈ geodStab m hA Λ) :
    Finite (gsvSmallNrm m hA1 hI1 hA hI Λ) :=
  (axisGenFiniteAbelian m hm hA1 hI1 hA hI (geodStab m hA Λ)
    (hdisc.mono fun c hc => (Subgroup.mem_inf.mp hc).1)
    (fun n hn => (Subgroup.mem_inf.mp hn).2) g hg (gsvPtSub m hA1 hI1 hA hI Λ)
    (fun p hp => ⟨gsvPtSub_le_geodStab m hA1 hI1 hA hI Λ hp, gsvPtSub_resStd m hA1 hI1 hA hI Λ hp⟩)
    (by
      intro n hn p hp
      refine ⟨(geodStab m hA Λ).mul_mem ((geodStab m hA Λ).mul_mem hn hp.1) ?_, ?_⟩
      · exact (geodStab m hA Λ).inv_mem hn
      · have hnS : n ∈ Submission.Mostow.SetStabStd 1 m := (Subgroup.mem_inf.mp hn).2
        have hpS : p ∈ Submission.Mostow.SetStabStd 1 m := gsvPtSub_mem_stab m hA1 hI1 hA hI Λ hp
        have hnS' : n⁻¹ ∈ Submission.Mostow.SetStabStd 1 m :=
          Work.Mostow.rhd_inv_mem_stab 1 m hA hnS
        rw [Work.Mostow.rhd_resStd_mul 1 m hA1 hI1 hA hI (Work.Mostow.rhd_mul_mem_stab 1 m hA hnS hpS) hnS',
          Work.Mostow.rhd_resStd_mul 1 m hA1 hI1 hA hI hnS hpS,
          Work.Mostow.rhd_resStd_inv 1 m hA1 hI1 hA hI hnS,
          gsvPtSub_resStd m hA1 hI1 hA hI Λ hp, mul_one, mul_inv_cancel])
    (gsvSmallNrm m hA1 hI1 hA hI Λ) (gsvSmallNrm_def m hA1 hI1 hA hI Λ)).1

lemma gsvSmallNrm_noFix (m : ℕ) (hA1 : Submission.Mostow.POActionProp 1)
    (hI1 : Submission.Mostow.HypIsometryProp 1)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1))
    {R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m}
    (hRmem : R ∈ gsvSmallNrm m hA1 hI1 hA hI Λ) (hR : ∀ w : Submission.Mostow.E m, R w = w → w = 0) :
    ∀ w : Submission.Mostow.E m, (∀ a ∈ gsvSmallNrm m hA1 hI1 hA hI Λ, a w = w) → w = 0 :=
  fun w hw => hR w (hw R hRmem)

/-- The subgroup of `E m ≃ₗᵢ[ℝ] E m` consisting of the normal parts of the elements of the
pointwise stabiliser `gsvPtSub`. -/

theorem gsvIndex (m : ℕ) (hm : 0 < m)
    (hA1 : Submission.Mostow.POActionProp 1) (hI1 : Submission.Mostow.HypIsometryProp 1)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m)) :
    ∃ J : ℕ, 0 < J ∧ ∀ (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)),
      _root_.IsDiscrete (SetLike.coe Λ) →
      Nat.card (Work.Mostow.DirichletScrew.gsvPtSub m hA1 hI1 hA hI Λ) ≤
        J * Nat.card (Work.Mostow.DirichletScrew.gsvSmallNrm m hA1 hI1 hA hI Λ) := by
  classical
  obtain ⟨J, hJpos, hJ⟩ := normalPartsIndex m hm hA1 hI1 hA hI
  refine ⟨J, hJpos, ?_⟩
  intro Λ hdisc
  let C : Subgroup (PO (1 + m) 1) := gsvPtSub m hA1 hI1 hA hI Λ
  have hCmem : ∀ c : PO (1 + m) 1, c ∈ C ↔ c ∈ geodStab m hA Λ ∧ resStd 1 m c = 1 :=
    fun c => Iff.rfl
  have hCdisc : IsDiscrete (SetLike.coe C) :=
    hdisc.mono (fun c hc => (Subgroup.mem_inf.mp ((hCmem c).mp hc).1).1)
  have hCtriv : ∀ c ∈ C, resStd 1 m c = 1 := fun c hc => ((hCmem c).mp hc).2
  -- the block parametrisation is multiplicative on the stratum and detects the parts
  have hpair : ∀ R R' : E m ≃ₗᵢ[ℝ] E m,
      blk 1 m (1 : PO 1 1) (R * R') = blk 1 m (1 : PO 1 1) R * blk 1 m (1 : PO 1 1) R' := by
    intro R R'
    have h := (blk_hom 1 m hA1 hI1 hA hI).1 (1 : PO 1 1) (1 : PO 1 1) R R'
    simpa using h
  have hone : blk 1 m (1 : PO 1 1) (1 : E m ≃ₗᵢ[ℝ] E m) = 1 :=
    (blk_hom 1 m hA1 hI1 hA hI).2.1
  have hparts : ∀ R : E m ≃ₗᵢ[ℝ] E m,
      resStd 1 m (blk 1 m (1 : PO 1 1) R) = 1 ∧ nrmStd 1 m (blk 1 m (1 : PO 1 1) R) = R :=
    fun R => (blk_hom 1 m hA1 hI1 hA hI).2.2 _ _ _ _
      (rhd_stab_form 1 m hA1 hI1 hA hI (gsv2_mem_stab 1 m hA1 hI1 hA hI (1 : PO 1 1) R)).symm
  -- the group `B` of normal parts occurring in `P`
  let B : Subgroup (E m ≃ₗᵢ[ℝ] E m) :=
    { carrier := {R | blk 1 m (1 : PO 1 1) R ∈ C}
      mul_mem' := by
        intro R R' hR hR'
        show blk 1 m (1 : PO 1 1) (R * R') ∈ C
        rw [hpair R R']
        exact C.mul_mem hR hR'
      one_mem' := by
        show blk 1 m (1 : PO 1 1) (1 : E m ≃ₗᵢ[ℝ] E m) ∈ C
        rw [hone]
        exact C.one_mem
      inv_mem' := by
        intro R hR
        show blk 1 m (1 : PO 1 1) R⁻¹ ∈ C
        have h1 : blk 1 m (1 : PO 1 1) R * blk 1 m (1 : PO 1 1) R⁻¹ = 1 := by
          rw [← hpair R R⁻¹, mul_inv_cancel, hone]
        have h2 : blk 1 m (1 : PO 1 1) R⁻¹ = (blk 1 m (1 : PO 1 1) R)⁻¹ := by
          calc blk 1 m (1 : PO 1 1) R⁻¹
              = (blk 1 m (1 : PO 1 1) R)⁻¹ *
                  (blk 1 m (1 : PO 1 1) R * blk 1 m (1 : PO 1 1) R⁻¹) := by group
            _ = (blk 1 m (1 : PO 1 1) R)⁻¹ := by rw [h1, mul_one]
        rw [h2]
        exact C.inv_mem hR }
  -- `B` is exactly the image of `C` under `nrmStd 1 m`
  have hBiff : ∀ x : E m ≃ₗᵢ[ℝ] E m, x ∈ B ↔ ∃ c ∈ C, nrmStd 1 m c = x := by
    intro x
    constructor
    · intro hx
      exact ⟨blk 1 m (1 : PO 1 1) x, hx, (hparts x).2⟩
    · rintro ⟨c, hc, rfl⟩
      show blk 1 m (1 : PO 1 1) (nrmStd 1 m c) ∈ C
      have hcP : c ∈ gsvPtSub m hA1 hI1 hA hI Λ := hc
      have hform : c = blk 1 m (1 : PO 1 1) (nrmStd 1 m c) := by
        have h := rhd_stab_form 1 m hA1 hI1 hA hI
          (gsvPtSub_mem_stab m hA1 hI1 hA hI Λ hcP)
        rw [gsvPtSub_resStd m hA1 hI1 hA hI Λ hcP] at h
        exact h
      exact hform ▸ hc
  -- the covering statement from `normalPartsIndex`
  obtain ⟨s, hscard, htrans⟩ := hJ C hCdisc hCtriv B hBiff
    (gsvSmallNrm m hA1 hI1 hA hI Λ) (gsvSmallNrm_def m hA1 hI1 hA hI Λ)
  haveI hfin : Finite (gsvSmallNrm m hA1 hI1 hA hI Λ) :=
    gsvSmallNrm_finite m hm hA1 hI1 hA hI Λ hdisc 1 (geodStab m hA Λ).one_mem
  have hcardB : Nat.card B ≤ s.card * Nat.card (gsvSmallNrm m hA1 hI1 hA hI Λ) :=
    cardTransversal B (gsvSmallNrm m hA1 hI1 hA hI Λ) s htrans
  -- `C ≃ B` via the normal part
  have hcardC : Nat.card C = Nat.card B := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun c : C => (⟨nrmStd 1 m (c : PO (1 + m) 1), (hBiff _).mpr ⟨c, c.2, rfl⟩⟩ : B)) ⟨?_, ?_⟩)
    · intro c c' hcc
      apply Subtype.ext
      have h1 : nrmStd 1 m (c : PO (1 + m) 1) = nrmStd 1 m (c' : PO (1 + m) 1) := by
        simpa using congrArg (fun y : B => (y : E m ≃ₗᵢ[ℝ] E m)) hcc
      have hc1 : (c : PO (1 + m) 1) =
          blk 1 m (1 : PO 1 1) (nrmStd 1 m (c : PO (1 + m) 1)) := by
        have h := rhd_stab_form 1 m hA1 hI1 hA hI
          (gsvPtSub_mem_stab m hA1 hI1 hA hI Λ c.2)
        rw [gsvPtSub_resStd m hA1 hI1 hA hI Λ c.2] at h
        exact h
      have hc2 : (c' : PO (1 + m) 1) =
          blk 1 m (1 : PO 1 1) (nrmStd 1 m (c' : PO (1 + m) 1)) := by
        have h := rhd_stab_form 1 m hA1 hI1 hA hI
          (gsvPtSub_mem_stab m hA1 hI1 hA hI Λ c'.2)
        rw [gsvPtSub_resStd m hA1 hI1 hA hI Λ c'.2] at h
        exact h
      rw [hc1, hc2, h1]
    · intro x
      obtain ⟨c, hc, hcx⟩ := (hBiff (x : E m ≃ₗᵢ[ℝ] E m)).mp x.2
      exact ⟨⟨c, hc⟩, Subtype.ext (by simpa using hcx)⟩
  change Nat.card C ≤ J * Nat.card (gsvSmallNrm m hA1 hI1 hA hI Λ)
  calc Nat.card C = Nat.card B := hcardC
    _ ≤ s.card * Nat.card (gsvSmallNrm m hA1 hI1 hA hI Λ) := hcardB
    _ ≤ J * Nat.card (gsvSmallNrm m hA1 hI1 hA hI Λ) := Nat.mul_le_mul_right _ hscard




/-- The strip of a non-identity isometry has positive measure. -/
lemma gsv2_strip_pos {m : ℕ} (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
    (hR : R ≠ 1) (c : ℝ) (hc : 0 < c) :
    0 < (MeasureTheory.volume : MeasureTheory.Measure (Submission.Mostow.E m))
      {W : Submission.Mostow.E m | ‖R W - W‖ ≤ c} := by
  by_cases hfpf : ∀ w : Submission.Mostow.E m, R w = w → w = 0
  · rw [ellipsoidVol m R hfpf c hc.le]
    have hdet : 0 < |LinearMap.det ((R.toLinearEquiv : Submission.Mostow.E m →ₗ[ℝ] Submission.Mostow.E m)
        - LinearMap.id)| := by
      refine abs_pos.mpr ?_
      intro h0
      have hker : ((R.toLinearEquiv : Submission.Mostow.E m →ₗ[ℝ] Submission.Mostow.E m)
          - LinearMap.id).ker = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro w hw
        simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply] at hw
        exact hfpf w (sub_eq_zero.mp hw)
      exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h0) hker
    exact ENNReal.mul_pos (ne_of_gt (ENNReal.ofReal_pos.mpr (div_pos (pow_pos hc m) hdet)))
      (ne_of_gt (Metric.measure_closedBall_pos (volume : MeasureTheory.Measure (Submission.Mostow.E m)) 0 one_pos))
  · push_neg at hfpf
    obtain ⟨w, hw1, hw2⟩ := hfpf
    rw [geeVolStripTop m R c hc ⟨w, hw2, hw1⟩]
    exact ENNReal.zero_lt_top


/-- `geodPtCard` is the cardinality of the pointwise stabiliser. -/
lemma gsvPtCardDef (m : ℕ) (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)) :
    geodPtCard m Λ = Nat.card {c : LeanEval.Geometry.MostowRigidity.PO (1 + m) 1 //
      c ∈ Λ ∧ c ∈ Submission.Mostow.SetStabStd 1 m ∧ Submission.Mostow.resStd 1 m c = 1} := rfl

lemma gsvPtCardEq (m : ℕ) (hA1 : Submission.Mostow.POActionProp 1)
    (hI1 : Submission.Mostow.HypIsometryProp 1)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1)) :
    geodPtCard m Λ = Nat.card (gsvPtSub m hA1 hI1 hA hI Λ) := by
  rw [gsvPtCardDef]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
  exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

end Work.Mostow.DirichletScrew

namespace Work.Mostow.DirichletScrew

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal

/-- `resStd` of a power of an element of the stratum stabiliser. -/
private lemma gsv_resStd_pow {m : ℕ} (hA1 : POActionProp 1) (hI1 : HypIsometryProp 1)
    (hA : POActionProp (1 + m)) (hI : HypIsometryProp (1 + m))
    {g : PO (1 + m) 1} (hg : g ∈ SetStabStd 1 m) (n : ℕ) :
    resStd 1 m (g ^ n) = (resStd 1 m g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, rhd_resStd_one 1 m hA1 hI1 hA hI]
  | succ k ih =>
      have h1 : g ^ k ∈ SetStabStd 1 m := by
        clear ih
        induction k with
        | zero => simpa using rhd_one_mem_stab 1 m hA
        | succ j ihj => rw [pow_succ]; exact rhd_mul_mem_stab 1 m hA ihj hg
      rw [pow_succ, pow_succ, rhd_resStd_mul 1 m hA1 hI1 hA hI h1 hg, ih]

/-- `nrmStd` of a power of an element of the stratum stabiliser. -/
private lemma gsv_nrmStd_pow {m : ℕ} (hA1 : POActionProp 1) (hI1 : HypIsometryProp 1)
    (hA : POActionProp (1 + m)) (hI : HypIsometryProp (1 + m))
    {g : PO (1 + m) 1} (hg : g ∈ SetStabStd 1 m) (n : ℕ) :
    nrmStd 1 m (g ^ n) = (nrmStd 1 m g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, rhd_nrmStd_one 1 m hA1 hI1 hA hI]
  | succ k ih =>
      have h1 : g ^ k ∈ SetStabStd 1 m := by
        clear ih
        induction k with
        | zero => simpa using rhd_one_mem_stab 1 m hA
        | succ j ihj => rw [pow_succ]; exact rhd_mul_mem_stab 1 m hA ihj hg
      rw [pow_succ, pow_succ, rhd_nrmStd_mul 1 m hA1 hI1 hA hI h1 hg, ih]

/-- The angle image of a subgroup of the rotation torus. -/
private def gsvAngImg {m : ℕ} (A B : Subgroup (Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m))
    (φ : (Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) →
      Fin (m / 2) → AddCircle (2 * Real.pi))
    (hle : A ≤ B) (hadd : ∀ c ∈ B, ∀ c' ∈ B, φ (c * c') = φ c + φ c')
    (h1 : φ 1 = 0) : AddSubgroup (Fin (m / 2) → AddCircle (2 * Real.pi)) where
  carrier := {f | ∃ c ∈ A, φ c = f}
  zero_mem' := ⟨1, A.one_mem, h1⟩
  add_mem' := by
    rintro f g ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    exact ⟨c * d, A.mul_mem hc hd, by rw [hadd c (hle hc) d (hle hd)]⟩
  neg_mem' := by
    rintro f ⟨c, hc, rfl⟩
    refine ⟨c⁻¹, A.inv_mem hc, ?_⟩
    have h := hadd c (hle hc) c⁻¹ (hle (A.inv_mem hc))
    rw [mul_inv_cancel, h1] at h
    exact eq_neg_of_add_eq_zero_right h.symm

/-- The normal parts of the pointwise stabiliser form a subgroup of `O (m)`. -/
private def gsvNrmSub {m : ℕ} (hA1 : POActionProp 1) (hI1 : HypIsometryProp 1)
    (hA : POActionProp (1 + m)) (hI : HypIsometryProp (1 + m))
    (Λ : Subgroup (PO (1 + m) 1)) : Subgroup (Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) where
  carrier := nrmStd 1 m '' (gsvPtSub m hA1 hI1 hA hI Λ : Set (PO (1 + m) 1))
  one_mem' := ⟨1, (gsvPtSub m hA1 hI1 hA hI Λ).one_mem,
    by rw [rhd_nrmStd_one 1 m hA1 hI1 hA hI]⟩
  mul_mem' := by
    rintro a b ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, (gsvPtSub m hA1 hI1 hA hI Λ).mul_mem hx hy,
      by rw [rhd_nrmStd_mul 1 m hA1 hI1 hA hI (gsvPtSub_mem_stab m hA1 hI1 hA hI Λ hx)
        (gsvPtSub_mem_stab m hA1 hI1 hA hI Λ hy)]⟩
  inv_mem' := by
    rintro a ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, (gsvPtSub m hA1 hI1 hA hI Λ).inv_mem hx,
      by rw [rhd_nrmStd_inv 1 m hA1 hI1 hA hI (gsvPtSub_mem_stab m hA1 hI1 hA hI Λ hx)]⟩

end Work.Mostow.DirichletScrew

namespace Work.Mostow.DirichletScrew

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal


/-- The `resStd`/`nrmStd` parts of `blk 1 m 1 R`. -/
private lemma gsv2_blk_parts {m : ℕ} (hA1 : POActionProp 1) (hI1 : HypIsometryProp 1)
    (hA : POActionProp (1 + m)) (hI : HypIsometryProp (1 + m))
    (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) :
    resStd 1 m (blk 1 m (1 : PO 1 1) R) = 1 ∧ nrmStd 1 m (blk 1 m (1 : PO 1 1) R) = R :=
  (blk_hom 1 m hA1 hI1 hA hI).2.2 _ _ _ _
    (rhd_stab_form 1 m hA1 hI1 hA hI
      (gsv2_mem_stab 1 m hA1 hI1 hA hI (1 : PO 1 1) R)).symm

/-- A fixed-vector-free linear isometry is not the identity. -/
private lemma gsv2_R_ne_one {m : ℕ} (hm : 0 < m)
    (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
    (hR : ∀ w : Submission.Mostow.E m, R w = w → w = 0) : R ≠ 1 := by
  intro h
  have h1 : R (EuclideanSpace.single (⟨0, hm⟩ : Fin m) (1 : ℝ)) =
      EuclideanSpace.single (⟨0, hm⟩ : Fin m) (1 : ℝ) := by rw [h]; rfl
  have h2 := hR _ h1
  have h3 : (EuclideanSpace.single (⟨0, hm⟩ : Fin m) (1 : ℝ) : Submission.Mostow.E m) ≠ 0 := by
    intro hc
    have h4 := congrArg (fun v : Submission.Mostow.E m => v ⟨0, hm⟩) hc
    simp at h4
  exact h3 h2

/-- `blk 1 m 1 R` is nontrivial as soon as `R` is. -/
private lemma gsv2_blk_ne_one {m : ℕ} (hA1 : POActionProp 1) (hI1 : HypIsometryProp 1)
    (hA : POActionProp (1 + m)) (hI : HypIsometryProp (1 + m))
    (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) (hR : R ≠ 1) :
    blk 1 m (1 : PO 1 1) R ≠ 1 := by
  intro h
  have h1 : blk 1 m (1 : PO 1 1) R =
      blk 1 m (1 : PO 1 1) (1 : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) := by
    rw [h, (blk_hom 1 m hA1 hI1 hA hI).2.1]
  exact hR ((blk_hom 1 m hA1 hI1 hA hI).2.2 _ _ _ _ h1).2

/-- The chord length of a block rotation angle is at most the operator norm of `R - 1`. -/
private lemma gsv_arsinh_le_self {x : ℝ} (hx : 0 ≤ x) : Real.arsinh x ≤ x := by
  have h1 : x ≤ Real.sinh x := (Real.self_le_sinh_iff).mpr hx
  have h2 : Real.arsinh x ≤ Real.arsinh (Real.sinh x) := (Real.arsinh_le_arsinh).mpr h1
  rwa [Real.arsinh_sinh] at h2

/-- Division comparison in a linear ordered field. -/
private lemma gsv_div_le_div {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    a / b ≤ c / d ↔ a * d ≤ c * b := by
  rw [div_le_iff₀ hb, show (c / d) * b = c * b / d by ring, le_div_iff₀ hd]

theorem dirichletScrew (m : ℕ) (hm : 4 ≤ m) (hev : Even m)
    (hA : Submission.Mostow.POActionProp (1 + m)) (hI : Submission.Mostow.HypIsometryProp (1 + m))
    (hA1 : Submission.Mostow.POActionProp 1) (hI1 : Submission.Mostow.HypIsometryProp 1)
    (η₁ : ℝ → ℝ) (hη₁ : ∀ V : ℝ, 0 < V → 0 < η₁ V) (Cn : ℝ) (hCn : 0 < Cn) :
    ∃ C : ℝ, 0 < C ∧ ∀ V : ℝ, 0 < V → ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ η₁ V ∧
      ∀ (Λ : Subgroup (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1))
        (D : Set (Submission.Mostow.E (1 + m))) (R : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
        (z : Submission.Mostow.E (1 + m)) (η : ℝ),
        _root_.IsDiscrete (SetLike.coe Λ) →
        MeasureTheory.IsFundamentalDomain Λ D (Submission.Mostow.volH (1 + m)) →
        Submission.Mostow.volH (1 + m) D ≤ ENNReal.ofReal V →
        Submission.Mostow.blk 1 m 1 R ∈ Λ → (∀ w : Submission.Mostow.E m, R w = w → w = 0) →
        Submission.Mostow.NearIdAt (Submission.Mostow.blk 1 m 1 R) z η → 0 < η → η ≤ η₀ →
        (∀ DY : Set (Submission.Mostow.E 1),
          MeasureTheory.IsFundamentalDomain
            (Subgroup.closure (Submission.Mostow.resStd 1 m ''
              (Work.Mostow.geodStab m hA Λ : Set (LeanEval.Geometry.MostowRigidity.PO (1 + m) 1))))
            DY (Submission.Mostow.volH 1) →
          Submission.Mostow.volH 1 DY * (MeasureTheory.volume : MeasureTheory.Measure (Submission.Mostow.E m))
              (Submission.Mostow.nrmC 1 m '' Work.Mostow.margRegion m Λ (η₁ V)) ≤
            ENNReal.ofReal (Cn * V) * (Work.Mostow.geodPtCard m Λ : ENNReal)) →
        ∃ γ ∈ Λ, orderOf γ = 0 ∧ Submission.Mostow.hdist z (γ • z) ≤ C * η := by
  classical
  ------------------------------------------------------------------
  -- (0) elementary constants
  ------------------------------------------------------------------
  have hev2 : 2 ∣ m := even_iff_two_dvd.mp hev
  have hm2 : 2 * (m / 2) = m := Nat.mul_div_cancel' hev2
  have hm0 : 0 < m / 2 := by omega
  have hspos : 0 < Real.sqrt ((m : ℝ) / 2) := Real.sqrt_pos.mpr (by positivity)
  have hcast : (m : ℝ) / 2 = ((m / 2 : ℕ) : ℝ) := by
    rw [Nat.cast_div hev2 (by norm_num : (((2 : ℕ) : ℝ)) ≠ 0)]
    norm_num
  set cδ : ℝ := 8 + 16 * Real.sqrt ((m : ℝ) / 2) with hcδdef
  have hcδpos : 0 < cδ := by rw [hcδdef]; positivity
  refine ⟨(2 * Real.sqrt (1 + (m : ℝ) / 2) + 1) * cδ + 1, by positivity, ?_⟩
  intro V hV
  ------------------------------------------------------------------
  -- (1) constants depending on `V` (but not on `Λ`)
  ------------------------------------------------------------------
  obtain ⟨J₀, hJ₀pos, hJ₀spec⟩ := gsvIndex m (by omega) hA1 hI1 hA hI
  have hσpos : 0 < η₁ V := hη₁ V hV
  set vB : ℝ := (volume (Metric.closedBall (0 : Submission.Mostow.E m) 1)).toReal with hvBdef
  have hvBpos : 0 < vB := by
    rw [hvBdef]
    refine ENNReal.toReal_pos ?_ ?_
    · exact ne_of_gt (Metric.measure_closedBall_pos (volume : MeasureTheory.Measure (Submission.Mostow.E m)) 0 one_pos)
    · exact ne_of_lt (isCompact_closedBall 0 1).measure_lt_top
  set K₀ : ℝ := 2 * ((Nat.factorial m : ℝ)) ^ 2 * Cn / ((η₁ V / 40) ^ m * vB) with hK₀def
  have hK₀pos : 0 < K₀ := by rw [hK₀def]; positivity
  set C_r : ℝ := 2 ^ (m / 2) * (4 * Real.pi * Real.sqrt ((m : ℝ) / 2)) ^ (m / 2) with hC_rdef
  have hC_rpos : 0 < C_r := by rw [hC_rdef]; positivity
  set up : ℝ := max 1 (max (((20 : ℝ) / η₁ V) ^ (m / 2 - 1))
      (Real.sqrt ((m : ℝ) / 2) * (J₀ : ℝ) * K₀ * V * C_r)) with hupdef
  have hup1 : 1 ≤ up := le_max_left _ _
  set κ : ℝ := up ^ (m / 2 - 1) with hκdef
  have hκpos : 0 < κ := by rw [hκdef]; exact pow_pos (lt_of_lt_of_le one_pos hup1) _
  have hκ1 : 1 ≤ κ := by rw [hκdef]; exact one_le_pow₀ hup1
  refine ⟨min (min (η₁ V / 160) (1 / 16)) (1 / (16 * Real.sqrt ((m : ℝ) / 2) * κ)), ?_, ?_, ?_⟩
  · exact lt_min (lt_min (by positivity) (by norm_num))
      (div_pos one_pos (by positivity))
  · exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith [hσpos])
  intro Λ D R z η hdisc hD hvol hb hRfree hnear hη hηle hCH
  ------------------------------------------------------------------
  -- (2) consequences of `η ≤ η₀`
  ------------------------------------------------------------------
  have hησ : η ≤ η₁ V := le_trans hηle (le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith [hσpos]))
  have hη160 : η ≤ η₁ V / 160 := le_trans hηle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hη16 : η ≤ 1 / 16 := le_trans hηle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hη_κ : η * (16 * Real.sqrt ((m : ℝ) / 2) * κ) ≤ 1 := by
    have h1 : η ≤ 1 / (16 * Real.sqrt ((m : ℝ) / 2) * κ) := le_trans hηle (min_le_right _ _)
    have h2 : 0 < 16 * Real.sqrt ((m : ℝ) / 2) * κ := by positivity
    calc η * (16 * Real.sqrt ((m : ℝ) / 2) * κ)
        ≤ (1 / (16 * Real.sqrt ((m : ℝ) / 2) * κ)) * (16 * Real.sqrt ((m : ℝ) / 2) * κ) :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt h2)
      _ = 1 := by field_simp
  have hη1le : η ≤ 1 := by linarith
  -- the Fermi coordinates of `z`
  set W_z : Submission.Mostow.E m := nrmC 1 m z with hW_zdef
  set v_z : Submission.Mostow.E 1 := (Real.sqrt (1 + ‖nrmC 1 m z‖ ^ 2))⁻¹ • tanC 1 m z with hv_zdef
  have hz_eq : fermiW 1 m v_z W_z = z := by
    rw [hv_zdef, hW_zdef]; exact nib_fermiW_surj m z
  have hnearF : NearIdAt (blk 1 m 1 R) (fermiW 1 m v_z W_z) η := by rw [hz_eq]; exact hnear
  ------------------------------------------------------------------
  -- (3) the given block element
  ------------------------------------------------------------------
  have hbP : blk 1 m 1 R ∈ gsvPtSub m hA1 hI1 hA hI Λ :=
    ⟨⟨hb, gsv2_mem_stab 1 m hA1 hI1 hA hI (1 : PO 1 1) R⟩, (gsv2_blk_parts hA1 hI1 hA hI R).1⟩
  have hbStab : blk 1 m 1 R ∈ SetStabStd 1 m := gsv2_mem_stab 1 m hA1 hI1 hA hI (1 : PO 1 1) R
  have hRne : R ≠ 1 := gsv2_R_ne_one (by omega) R hRfree
  have hblkne : blk 1 m 1 R ≠ 1 := gsv2_blk_ne_one hA1 hI1 hA hI R hRne
  have hRrot : rotN R ≤ 4 * η := (((nearId_blk m hA1 hI1 hA hI R v_z W_z).2 η hnearF hη1le)).1
  have hRdisp : ‖R W_z - W_z‖ ≤ 2 * Real.sinh (η / 2) :=
    (((nearId_blk m hA1 hI1 hA hI R v_z W_z).2 η hnearF hη1le)).2
  have hRrotσ : rotN R ≤ η₁ V / 40 := by
    have : 4 * η ≤ η₁ V / 40 := by linarith [hη160]
    linarith
  ------------------------------------------------------------------
  -- (4) the stabiliser and the dichotomy
  ------------------------------------------------------------------
  set N : Subgroup (PO (1 + m) 1) := geodStab m hA Λ with hNdef
  set G : Subgroup (PO 1 1) := Subgroup.closure (resStd 1 m '' (N : Set (PO (1 + m) 1))) with hGdef
  have hStab : ∀ c ∈ N, c ∈ SetStabStd 1 m := fun c hc => (Subgroup.mem_inf.mp hc).2
  have hNdisc : IsDiscrete (SetLike.coe N) := hdisc.mono (fun c hc => (Subgroup.mem_inf.mp hc).1)
  have hGdisc : IsDiscrete (SetLike.coe G) := by
    rw [hGdef]
    exact ((resStd_hom_discrete 1 m hA1 hI1 hA hI).2 (geodStab m hA Λ) hNdisc hStab).1
  have hCHG : ∀ DY : Set (Submission.Mostow.E 1), IsFundamentalDomain G DY (volH 1) →
      volH 1 DY * volume (nrmC 1 m '' margRegion m Λ (η₁ V)) ≤
        ENNReal.ofReal (Cn * V) * (geodPtCard m Λ : ENNReal) := by
    intro DY hDY
    refine hCH DY ?_
    rw [hGdef] at hDY
    exact hDY
  -- the strip of `blk 1 m 1 R` sits in the Margulis region, so its image has positive volume
  have hvolImgpos : 0 < volume (nrmC 1 m '' margRegion m Λ (η₁ V)) := by
    have hsub := geeStripMeasure_subset m hA1 hI1 hA hI Λ (η₁ V) (η₁ V / 40)
      (by positivity) (by linarith) (blk 1 m 1 R) hb hbStab (gsv2_blk_parts hA1 hI1 hA hI R).1
      hblkne (by rw [(gsv2_blk_parts hA1 hI1 hA hI R).2]; exact hRrotσ)
    rw [(gsv2_blk_parts hA1 hI1 hA hI R).2] at hsub
    have hstrip : 0 < volume {W : Submission.Mostow.E m | ‖R W - W‖ ≤ η₁ V / 40} :=
      gsv2_strip_pos R hRne (η₁ V / 40) (by positivity)
    exact lt_of_lt_of_le hstrip (measure_mono hsub)
  rcases axisDatum hA1 hI1 G hGdisc with ⟨g₀, hg₀G, hg₀free, hg₀min, hg₀sq⟩ | hsquares
  · -- ============ Case B: there is a translation; the screw ============
    obtain ⟨DG, hDG, _⟩ := existsFDone hA1 hI1 G hGdisc
    -- (a) the lift of `g₀` and the translation element `h₂ = n₀ ^ (m!)²`
    have hg₀G' : g₀ ∈ Subgroup.closure (resStd 1 m '' (geodStab m hA Λ : Set (PO (1 + m) 1))) := by
      rw [← hGdef]; exact hg₀G
    obtain ⟨n₀, hn₀N, hn₀res⟩ := exists_mem_of_mem_closure_resStd 1 m hA1 hI1 hA hI
      (geodStab m hA Λ) hStab g₀ hg₀G'
    have hn₀stab : n₀ ∈ SetStabStd 1 m := hStab n₀ hn₀N
    set h₂ : PO (1 + m) 1 := n₀ ^ ((Nat.factorial m) ^ 2) with hh₂def
    have hh₂N : h₂ ∈ N := by rw [hh₂def]; exact Subgroup.pow_mem N hn₀N _
    have hh₂stab : h₂ ∈ SetStabStd 1 m := hStab h₂ hh₂N
    have hh₂res : resStd 1 m h₂ = g₀ ^ ((Nat.factorial m) ^ 2) := by
      rw [hh₂def, gsv_resStd_pow hA1 hI1 hA hI hn₀stab, hn₀res]
    have hh₂nrm : nrmStd 1 m h₂ = (nrmStd 1 m n₀) ^ ((Nat.factorial m) ^ 2) := by
      rw [hh₂def]; exact gsv_nrmStd_pow hA1 hI1 hA hI hn₀stab _
    have hℓ₀pos : 0 < hdist (0 : Submission.Mostow.E 1) (g₀ • (0 : Submission.Mostow.E 1)) := by
      rcases lt_or_eq_of_le (nib_hdist_nonneg (0 : Submission.Mostow.E 1) (g₀ • (0 : Submission.Mostow.E 1))) with h | h
      · exact h
      · exfalso
        have h1 : g₀ • (0 : Submission.Mostow.E 1) = 0 :=
          (((HypIsoData.ofProp hI1).eq_zero (0 : Submission.Mostow.E 1)
            (g₀ • (0 : Submission.Mostow.E 1))).mp h.symm).symm
        exact hg₀free 0 h1
    set T₀ : ℝ := ((Nat.factorial m : ℝ)) ^ 2 *
      hdist (0 : Submission.Mostow.E 1) (g₀ • (0 : Submission.Mostow.E 1)) with hT₀def
    have hT₀pos : 0 < T₀ := by rw [hT₀def]; positivity
    have hT₀disp : ∀ v : Submission.Mostow.E 1, hdist v (resStd 1 m h₂ • v) = T₀ := by
      intro v
      have h1 := hdistZpowFixedfree hA1 hI1 g₀ hg₀free v (((Nat.factorial m) ^ 2 : ℕ) : ℤ)
      rw [zpow_natCast] at h1
      have h2 : |((((Nat.factorial m) ^ 2 : ℕ) : ℤ) : ℝ)| = ((Nat.factorial m : ℝ)) ^ 2 := by
        rw [Int.cast_natCast, Nat.cast_pow, abs_of_nonneg (by positivity)]
      rw [hh₂res, h1, h2, hT₀def]
    -- (b) the tube bound: `T₀ · vol (Img) ≤ 2 (m!)² Cn V |P|`
    have hCHdg := hCHG DG hDG
    have hcov := geeAxisCovol hA1 hI1 G hGdisc g₀ hg₀G hg₀free hg₀min hg₀sq DG hDG
    have hT₀le : ENNReal.ofReal T₀
        ≤ ENNReal.ofReal ((Nat.factorial m : ℝ) ^ 2) * (2 * volH 1 DG) := by
      rw [hT₀def, ENNReal.ofReal_mul (by positivity)]
      exact mul_le_mul_of_nonneg_left hcov (by positivity)
    -- (c) the torus
    have hRmemA : R ∈ gsvSmallNrm m hA1 hI1 hA hI Λ := by
      rw [gsvSmallNrm_def]
      refine Subgroup.subset_closure ⟨blk 1 m 1 R, ⟨hbP, ?_⟩, ?_⟩
      · rw [(gsv2_blk_parts hA1 hI1 hA hI R).2]; linarith [hRrot, hη16]
      · exact (gsv2_blk_parts hA1 hI1 hA hI R).2
    haveI hfinA : Finite (gsvSmallNrm m hA1 hI1 hA hI Λ) :=
      gsvSmallNrm_finite m (by omega) hA1 hI1 hA hI Λ hdisc (blk 1 m 1 R)
        ⟨hb, gsv2_mem_stab 1 m hA1 hI1 hA hI (1 : PO 1 1) R⟩
    have hcommA : ∀ a ∈ gsvSmallNrm m hA1 hI1 hA hI Λ, ∀ b ∈ gsvSmallNrm m hA1 hI1 hA hI Λ,
        a * b = b * a :=
      gsvSmallNrm_comm m (by omega) hA1 hI1 hA hI Λ hdisc
    have hgenA : gsvSmallNrm m hA1 hI1 hA hI Λ =
        Subgroup.closure {a | a ∈ gsvSmallNrm m hA1 hI1 hA hI Λ ∧ rotN a ≤ 1 / 4} :=
      gsvSmallNrm_gen m hA1 hI1 hA hI Λ
    have hnofixA : ∀ w : Submission.Mostow.E m,
        (∀ a ∈ gsvSmallNrm m hA1 hI1 hA hI Λ, a w = w) → w = 0 :=
      gsvSmallNrm_noFix m hA1 hI1 hA hI Λ hRmemA hRfree
    have hPnorm : ∀ n ∈ N, ∀ p : PO (1 + m) 1,
        p ∈ gsvPtSub m hA1 hI1 hA hI Λ → n * p * n⁻¹ ∈ gsvPtSub m hA1 hI1 hA hI Λ := by
      intro n hn p hp
      obtain ⟨hpN, hpres⟩ := hp
      have hmem : n * p * n⁻¹ ∈ geodStab m hA Λ :=
        (geodStab m hA Λ).mul_mem ((geodStab m hA Λ).mul_mem hn hpN)
          ((geodStab m hA Λ).inv_mem hn)
      refine ⟨hmem, ?_⟩
      have hnS : n ∈ SetStabStd 1 m := (Subgroup.mem_inf.mp hn).2
      have hpS : p ∈ SetStabStd 1 m := (Subgroup.mem_inf.mp hpN).2
      have hnp : n * p ∈ SetStabStd 1 m := rhd_mul_mem_stab 1 m hA hnS hpS
      have hni : n⁻¹ ∈ SetStabStd 1 m := rhd_inv_mem_stab 1 m hA hnS
      rw [rhd_resStd_mul 1 m hA1 hI1 hA hI hnp hni,
          rhd_resStd_mul 1 m hA1 hI1 hA hI hnS hpS, hpres,
          rhd_resStd_inv 1 m hA1 hI1 hA hI hnS, mul_one, mul_inv_cancel]
    have hcomm₂ : ∀ a ∈ gsvSmallNrm m hA1 hI1 hA hI Λ, (nrmStd 1 m h₂) * a = a * (nrmStd 1 m h₂) := by
      intro a ha
      have hgl := axisTranslationCentralises m (by omega) hA1 hI1 hA hI N hNdisc hStab n₀ hn₀N
        (gsvPtSub m hA1 hI1 hA hI Λ)
        (fun p hp => ⟨hp.1, hp.2⟩) hPnorm (gsvSmallNrm m hA1 hI1 hA hI Λ)
        (gsvSmallNrm_def m hA1 hI1 hA hI Λ) a ha
      rw [hh₂nrm]
      have hc : Commute ((nrmStd 1 m n₀) ^ Nat.factorial m) a := hgl
      have hc2 := hc.pow_left (Nat.factorial m)
      simpa [pow_two, pow_mul] using hc2.eq
    obtain ⟨e, φ, Aang, hblk, hφadd, hAang⟩ :=
      torusData m hev (gsvSmallNrm m hA1 hI1 hA hI Λ) hgenA hcommA hnofixA (nrmStd 1 m h₂) hcomm₂
    have hφ1 : φ 1 = 0 := by
      have h := hφadd 1 (Subgroup.mem_sup_left (gsvSmallNrm m hA1 hI1 hA hI Λ).one_mem)
        1 (Subgroup.mem_sup_left (gsvSmallNrm m hA1 hI1 hA hI Λ).one_mem)
      rw [mul_one] at h
      exact (add_left_cancel (show φ 1 + 0 = φ 1 + φ 1 from by rw [add_zero]; exact h)).symm
    set AangR : AddSubgroup (Fin (m / 2) → AddCircle (2 * Real.pi)) :=
      gsvAngImg (gsvSmallNrm m hA1 hI1 hA hI Λ)
        (gsvSmallNrm m hA1 hI1 hA hI Λ ⊔ Subgroup.zpowers (nrmStd 1 m h₂)) φ le_sup_left hφadd hφ1
      with hAangRdef
    have hAangRmem : ∀ f, f ∈ AangR ↔ ∃ c ∈ gsvSmallNrm m hA1 hI1 hA hI Λ, φ c = f := fun f => Iff.rfl
    have hblkR : ∀ (i : Fin (m / 2)) (x y : ℝ), ∃ t : ℝ,
        (t : AddCircle (2 * Real.pi)) = φ R i ∧
        R (x • e (i, Fin.castSucc 0) + y • e (i, 1)) =
          (Real.cos t * x - Real.sin t * y) • e (i, Fin.castSucc 0) +
            (Real.sin t * x + Real.cos t * y) • e (i, 1) :=
      hblk R (Subgroup.mem_sup_left hRmemA)
    have hφRmem : φ R ∈ AangR := ⟨R, hRmemA, rfl⟩
    have hφRne : φ R ≠ 0 := by
      intro h0
      have h1 : R = 1 := eqOneOfPhiEqZero m e R (φ R) hblkR (fun i => by rw [h0]; rfl)
      exact hRne h1
    -- (d) the torus section: every element of `gsvSmallNrm` is a normal part over the stabiliser
    have hnrmSection : ∀ a ∈ gsvSmallNrm m hA1 hI1 hA hI Λ,
        ∃ p ∈ gsvPtSub m hA1 hI1 hA hI Λ, nrmStd 1 m p = a := by
      have hle : gsvSmallNrm m hA1 hI1 hA hI Λ ≤ gsvNrmSub hA1 hI1 hA hI Λ := by
        refine (Subgroup.closure_le _).mpr ?_
        rintro x ⟨p, hp, rfl⟩
        exact ⟨p, hp.1, rfl⟩
      intro a ha
      obtain ⟨p, hp, hp'⟩ := hle ha
      exact ⟨p, hp, hp'⟩
    -- (e) the weights and the two scale data
    set δ : ℝ := cδ * η with hδdef
    have hδpos : 0 < δ := by rw [hδdef]; positivity
    set ρ_ : ℝ := max 1 (2 * δ * κ) with hρ_def
    have hρ_pos : 0 < ρ_ := lt_of_lt_of_le one_pos (le_max_left _ _)
    set ρt : Fin (m / 2) → ℝ := fun i =>
      max ‖(inner ℝ (e (i, Fin.castSucc 0)) W_z) • e (i, Fin.castSucc 0) +
          (inner ℝ (e (i, 1)) W_z) • e (i, 1)‖ ρ_ with hρtdef
    have hρtpos : ∀ i, 0 < ρt i := fun i => lt_of_lt_of_le hρ_pos (le_max_right _ _)
    have hchordR : ∀ i : Fin (m / 2), chord (φ R i) ≤ 4 * η := by
      intro i
      have h1 := chordLeRotN m e R (φ R) hblkR i
      linarith [hRrot]
    have hnearW := nearIdWeights m hev (by omega) e R (φ R) hblkR W_z η ρ_ hη hρ_pos hRdisp hchordR
    have hδ₀le : 2 * Real.sinh (η / 2) + 2 * Real.sqrt ((m : ℝ) / 2) * 2 * η * ρ_ ≤ δ := by
      have hsin : 2 * Real.sinh (η / 2) ≤ 3 * η / 2 := by
        have h := nib_sinh_half_le (le_of_lt hη) hη1le
        linarith
      have hρle : ρ_ ≤ 1 + 2 * δ * κ := by
        rw [hρ_def]
        have h0 : (0 : ℝ) ≤ 2 * δ * κ := by positivity
        exact max_le (by linarith) (by linarith)
      have hκle : 8 * Real.sqrt ((m : ℝ) / 2) * η * κ ≤ 1 / 2 := by
        nlinarith [hη_κ, hspos, hκpos]
      have hδeq : δ = (8 + 16 * Real.sqrt ((m : ℝ) / 2)) * η := by rw [hδdef, hcδdef]
      have step1 : 2 * Real.sinh (η / 2) + 2 * Real.sqrt ((m : ℝ) / 2) * 2 * η * ρ_
          ≤ 3 * η / 2 + 2 * Real.sqrt ((m : ℝ) / 2) * 2 * η * (1 + 2 * δ * κ) := by
        have hnn : 0 ≤ 2 * Real.sqrt ((m : ℝ) / 2) * 2 * η := by positivity
        nlinarith [hρle, hnn]
      have step2 : 2 * Real.sqrt ((m : ℝ) / 2) * 2 * η * (1 + 2 * δ * κ)
          ≤ 4 * Real.sqrt ((m : ℝ) / 2) * η + δ / 2 := by
        nlinarith [hκle, hspos, hη, hκpos, hδpos]
      have step3 : 3 * η / 2 + 4 * Real.sqrt ((m : ℝ) / 2) * η ≤ δ / 2 := by
        rw [hδeq]; nlinarith [hspos, hη]
      linarith
    have hf_le : ∑ i : Fin (m / 2), (ρt i) ^ 2 * (chord (φ R i)) ^ 2 ≤ δ ^ 2 := by
      have hδ₀nn : 0 ≤ 2 * Real.sinh (η / 2) + 2 * Real.sqrt ((m : ℝ) / 2) * 2 * η * ρ_ := by
        have hsn : 0 ≤ Real.sinh (η / 2) := Real.sinh_nonneg_iff.mpr (by linarith)
        have hsp : 0 ≤ Real.sqrt ((m : ℝ) / 2) := Real.sqrt_nonneg _
        positivity
      exact le_trans hnearW (pow_le_pow_left₀ hδ₀nn hδ₀le 2)
    -- (f) rescaling
    haveI hfinAangR : Finite AangR := by
      have himg : (AangR : Set (Fin (m / 2) → AddCircle (2 * Real.pi))) =
          φ '' (gsvSmallNrm m hA1 hI1 hA hI Λ : Set (Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)) := by
        ext f; exact ⟨fun h => h, fun h => h⟩
      have hfin : (AangR : Set (Fin (m / 2) → AddCircle (2 * Real.pi))).Finite := by
        rw [himg]
        exact (Set.toFinite (gsvSmallNrm m hA1 hI1 hA hI Λ : Set _)).image φ
      exact hfin.to_subtype
    obtain ⟨s, hs1, b', hb'A, hb'ne, hb'eq, hb'min⟩ :=
      rescaledPoint (m / 2) AangR ρt hρtpos δ hδpos (φ R) hφRmem hφRne hf_le
    set ρ : Fin (m / 2) → ℝ := fun i => s * ρt i with hρdef
    have hρpos : ∀ i, 0 < ρ i := fun i => mul_pos (lt_of_lt_of_le one_pos hs1) (hρtpos i)
    have hρρ : ∀ i, ρ_ ≤ ρ i := by
      intro i
      have h1 : ρ_ ≤ ρt i := le_max_right _ _
      have h2 : ρt i ≤ s * ρt i := by nlinarith [h1, hs1, hρtpos i]
      show ρ_ ≤ s * ρt i
      linarith
    have hb'min' : ∀ a ∈ AangR, a ≠ 0 → δ ^ 2 ≤ ∑ i, (ρ i) ^ 2 * (chord (a i)) ^ 2 := hb'min
    have hb'eq' : ∑ i, (ρ i) ^ 2 * (chord (b' i)) ^ 2 = δ ^ 2 := hb'eq
    -- the geometric element realising `b'`
    obtain ⟨cp, hcpA, hcpeq⟩ : ∃ c ∈ gsvSmallNrm m hA1 hI1 hA hI Λ, φ c = b' := (hAangRmem b').mp hb'A
    obtain ⟨p₀, hp₀P, hp₀nrm⟩ := hnrmSection cp hcpA
    have hp₀stab : p₀ ∈ SetStabStd 1 m := gsvPtSub_mem_stab m hA1 hI1 hA hI Λ hp₀P
    have hp₀res : resStd 1 m p₀ = 1 := gsvPtSub_resStd m hA1 hI1 hA hI Λ hp₀P
    have hp₀memΛ : p₀ ∈ Λ := (Subgroup.mem_inf.mp hp₀P.1).1
    have hp₀ne : p₀ ≠ 1 := by
      intro h1
      have h2 : cp = 1 := by rw [← hp₀nrm, h1, rhd_nrmStd_one 1 m hA1 hI1 hA hI]
      have h3 : b' = 0 := by rw [← hcpeq, h2, hφ1]
      exact hb'ne h3
    have hblkb' : ∀ (i : Fin (m / 2)) (x y : ℝ), ∃ t : ℝ,
        (t : AddCircle (2 * Real.pi)) = b' i ∧
        cp (x • e (i, Fin.castSucc 0) + y • e (i, 1)) =
          (Real.cos t * x - Real.sin t * y) • e (i, Fin.castSucc 0) +
            (Real.sin t * x + Real.cos t * y) • e (i, 1) := by
      intro i x y
      have h := hblk cp (Subgroup.mem_sup_left hcpA) i x y
      simpa [hcpeq] using h
    -- the rotation of the minimiser is small, hence its strip lies in the Margulis region
    have hrot_p₀ : rotN cp ≤ η₁ V / 40 := by
      have h := rotN_le_of_blockWeights m e cp b' hblkb' ρ ρ_ δ hρ_pos hρρ hδpos
        (le_of_eq hb'eq')
      have h2 : δ / ρ_ ≤ 1 / (2 * κ) := by
        have h3 : 2 * δ * κ ≤ ρ_ := by rw [hρ_def]; exact le_max_right _ _
        rw [div_le_iff₀ hρ_pos, show (1 / (2 * κ)) * ρ_ = ρ_ / (2 * κ) by ring,
          le_div_iff₀ (by positivity : (0 : ℝ) < 2 * κ)]
        nlinarith [h3]
      have h5 : 1 / (2 * κ) ≤ η₁ V / 40 := by
        have h6 : 20 ≤ η₁ V * κ := by
          rcases le_or_gt 1 (20 / η₁ V) with hh | hh
          · have h1 : (20 / η₁ V) ^ (m / 2 - 1) ≤ up :=
              le_trans (le_max_left _ _) (le_max_right _ _)
            have h2 : 20 / η₁ V ≤ (20 / η₁ V) ^ (m / 2 - 1) := by
              simpa using pow_le_pow_right₀ hh (by omega : 1 ≤ m / 2 - 1)
            have h3 : up ≤ κ := by
              rw [hκdef]
              simpa using pow_le_pow_right₀ hup1 (by omega : 1 ≤ m / 2 - 1)
            have h4 : 20 ≤ κ * η₁ V := (div_le_iff₀ hσpos).mp (le_trans h2 (le_trans h1 h3))
            linarith [h4]
          · have h2 : 20 < η₁ V := by
              have h3 : 20 / η₁ V * η₁ V < 1 * η₁ V := mul_lt_mul_of_pos_right hh hσpos
              rwa [div_mul_cancel₀ 20 (ne_of_gt hσpos), one_mul] at h3
            nlinarith [h2, hκ1]
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * κ),
          show (η₁ V / 40) * (2 * κ) = η₁ V * κ / 20 by ring]
        exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 20)).mpr (by linarith [h6])
      linarith
    have hsub_m : {W : Submission.Mostow.E m | ‖cp W - W‖ ≤ η₁ V / 40} ⊆
        nrmC 1 m '' margRegion m Λ (η₁ V) := by
      have h1 := geeStripMeasure_subset m hA1 hI1 hA hI Λ (η₁ V) (η₁ V / 40)
        (by positivity) (by linarith) p₀ hp₀memΛ hp₀stab hp₀res hp₀ne
        (by rw [hp₀nrm]; exact hrot_p₀)
      rw [hp₀nrm] at h1
      exact h1
    -- the volume lower bound given by the ellipsoid of the minimiser
    have hvB_eq : volume (Metric.closedBall (0 : Submission.Mostow.E m) 1) = ENNReal.ofReal vB := by
      rw [hvBdef, ENNReal.ofReal_toReal]
      exact ne_of_lt (isCompact_closedBall (0 : Submission.Mostow.E m) 1).measure_lt_top
    have hdetM : |LinearMap.det ((cp.toLinearEquiv : Submission.Mostow.E m →ₗ[ℝ] Submission.Mostow.E m)
        - LinearMap.id)| ≤ δ ^ m / ∏ i, (ρ i) ^ 2 :=
      detBoundBlockM m hm0 e b' ρ hρpos δ hδpos cp hblkb' hm2 (le_of_eq hb'eq')
    have hvolE : ENNReal.ofReal ((η₁ V / 40) ^ m * (∏ i, (ρ i) ^ 2) / δ ^ m * vB)
        ≤ volume (nrmC 1 m '' margRegion m Λ (η₁ V)) := by
      by_cases hfpf : ∀ w : Submission.Mostow.E m, cp w = w → w = 0
      · have hmono : volume {W : Submission.Mostow.E m | ‖cp W - W‖ ≤ η₁ V / 40}
            ≤ volume (nrmC 1 m '' margRegion m Λ (η₁ V)) := measure_mono hsub_m
        have hdetpos : 0 < |LinearMap.det ((cp.toLinearEquiv : Submission.Mostow.E m →ₗ[ℝ] Submission.Mostow.E m)
            - LinearMap.id)| := by
          refine abs_pos.mpr ?_
          intro h0
          have hker : ((cp.toLinearEquiv : Submission.Mostow.E m →ₗ[ℝ] Submission.Mostow.E m)
              - LinearMap.id).ker = ⊥ := by
            rw [Submodule.eq_bot_iff]
            intro w hw
            simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply] at hw
            exact hfpf w (sub_eq_zero.mp hw)
          exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h0) hker
        have hle1 : (η₁ V / 40) ^ m * (∏ i, (ρ i) ^ 2) / δ ^ m
            ≤ (η₁ V / 40) ^ m / |LinearMap.det ((cp.toLinearEquiv : Submission.Mostow.E m →ₗ[ℝ] Submission.Mostow.E m)
                - LinearMap.id)| := by
          have h1 : |LinearMap.det ((cp.toLinearEquiv : Submission.Mostow.E m →ₗ[ℝ] Submission.Mostow.E m)
              - LinearMap.id)| * (∏ i, (ρ i) ^ 2) ≤ δ ^ m := by
            have h2 := hdetM
            rw [le_div_iff₀ (Finset.prod_pos (fun i _ => pow_pos (hρpos i) 2))] at h2
            linarith [h2]
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < δ ^ m),
            show ((η₁ V / 40) ^ m / |LinearMap.det ((cp.toLinearEquiv : Submission.Mostow.E m →ₗ[ℝ] Submission.Mostow.E m)
                - LinearMap.id)|) * δ ^ m =
              (η₁ V / 40) ^ m * δ ^ m / |LinearMap.det ((cp.toLinearEquiv : Submission.Mostow.E m →ₗ[ℝ] Submission.Mostow.E m)
                - LinearMap.id)| by ring,
            le_div_iff₀ hdetpos]
          nlinarith [h1, show 0 < (η₁ V / 40) ^ m by positivity]
        calc ENNReal.ofReal ((η₁ V / 40) ^ m * (∏ i, (ρ i) ^ 2) / δ ^ m * vB)
            ≤ ENNReal.ofReal ((η₁ V / 40) ^ m / |LinearMap.det ((cp.toLinearEquiv : Submission.Mostow.E m →ₗ[ℝ] Submission.Mostow.E m)
                - LinearMap.id)| * vB) := ENNReal.ofReal_le_ofReal (by nlinarith [hle1, hvBpos])
          _ = ENNReal.ofReal ((η₁ V / 40) ^ m / |LinearMap.det ((cp.toLinearEquiv : Submission.Mostow.E m →ₗ[ℝ] Submission.Mostow.E m)
                - LinearMap.id)|) * ENNReal.ofReal vB := by
                rw [ENNReal.ofReal_mul (by positivity)]
          _ = ENNReal.ofReal ((η₁ V / 40) ^ m / |LinearMap.det ((cp.toLinearEquiv : Submission.Mostow.E m →ₗ[ℝ] Submission.Mostow.E m)
                - LinearMap.id)|) * volume (Metric.closedBall (0 : Submission.Mostow.E m) 1) := by
                rw [hvB_eq]
          _ = volume {W : Submission.Mostow.E m | ‖cp W - W‖ ≤ η₁ V / 40} :=
                (ellipsoidVol m cp hfpf (η₁ V / 40) (by positivity)).symm
          _ ≤ _ := hmono
      · push_neg at hfpf
        obtain ⟨w, hw1, hw2⟩ := hfpf
        have hmono : volume {W : Submission.Mostow.E m | ‖cp W - W‖ ≤ η₁ V / 40}
            ≤ volume (nrmC 1 m '' margRegion m Λ (η₁ V)) := measure_mono hsub_m
        rw [geeVolStripTop m cp (η₁ V / 40) (by positivity) ⟨w, hw2, hw1⟩] at hmono
        exact le_trans le_top hmono
    -- the tube bound
    have hTube : T₀ * (∏ i, (ρ i) ^ 2) ≤ K₀ * V * (geodPtCard m Λ : ℝ) * δ ^ m := by
      have hstep1 : ENNReal.ofReal T₀ * volume (nrmC 1 m '' margRegion m Λ (η₁ V))
          ≤ ENNReal.ofReal ((Nat.factorial m : ℝ) ^ 2) *
              (2 * (ENNReal.ofReal (Cn * V) * (geodPtCard m Λ : ENNReal))) := by
        calc ENNReal.ofReal T₀ * volume (nrmC 1 m '' margRegion m Λ (η₁ V))
            ≤ (ENNReal.ofReal ((Nat.factorial m : ℝ) ^ 2) * (2 * volH 1 DG)) *
                volume (nrmC 1 m '' margRegion m Λ (η₁ V)) := mul_le_mul_of_nonneg_right hT₀le (by positivity)
          _ = ENNReal.ofReal ((Nat.factorial m : ℝ) ^ 2) *
                (2 * (volH 1 DG * volume (nrmC 1 m '' margRegion m Λ (η₁ V)))) := by
              rw [mul_assoc, mul_assoc]
          _ ≤ ENNReal.ofReal ((Nat.factorial m : ℝ) ^ 2) *
                (2 * (ENNReal.ofReal (Cn * V) * (geodPtCard m Λ : ENNReal))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hCHdg (by positivity)) (by positivity)
      have hstep2 : ENNReal.ofReal ((Nat.factorial m : ℝ) ^ 2) *
            (2 * (ENNReal.ofReal (Cn * V) * (geodPtCard m Λ : ENNReal)))
          = ENNReal.ofReal (2 * ((Nat.factorial m : ℝ)) ^ 2 * Cn * V * (geodPtCard m Λ : ℝ)) := by
        rw [← ENNReal.ofReal_natCast (geodPtCard m Λ), ← ENNReal.ofReal_ofNat 2]
        rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ Cn * V by positivity)]
        rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ ((Nat.factorial m : ℝ)) ^ 2 by positivity)]
        congr 1
        ring
      have hcomb : ENNReal.ofReal (T₀ * ((η₁ V / 40) ^ m * (∏ i, (ρ i) ^ 2) / δ ^ m * vB))
          ≤ ENNReal.ofReal (2 * ((Nat.factorial m : ℝ)) ^ 2 * Cn * V * (geodPtCard m Λ : ℝ)) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        calc ENNReal.ofReal T₀ * ENNReal.ofReal ((η₁ V / 40) ^ m * (∏ i, (ρ i) ^ 2) / δ ^ m * vB)
            ≤ ENNReal.ofReal T₀ * volume (nrmC 1 m '' margRegion m Λ (η₁ V)) :=
              mul_le_mul_of_nonneg_left hvolE (by positivity)
          _ ≤ _ := hstep1
          _ = _ := hstep2
      have hcomb' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcomb
      have hδm : 0 < δ ^ m := by positivity
      have h1 : T₀ * (∏ i, (ρ i) ^ 2) * ((η₁ V / 40) ^ m * vB)
          ≤ 2 * ((Nat.factorial m : ℝ)) ^ 2 * Cn * V * (geodPtCard m Λ : ℝ) * δ ^ m := by
        rw [show T₀ * ((η₁ V / 40) ^ m * (∏ i, (ρ i) ^ 2) / δ ^ m * vB)
            = T₀ * (∏ i, (ρ i) ^ 2) * ((η₁ V / 40) ^ m * vB) / δ ^ m by ring,
          div_le_iff₀ hδm] at hcomb'
        linarith [hcomb']
      have hsp : 0 < (η₁ V / 40) ^ m * vB := by positivity
      rw [hK₀def]
      rw [show (2 * (Nat.factorial m : ℝ) ^ 2 * Cn) / ((η₁ V / 40) ^ m * vB) * V *
              (geodPtCard m Λ : ℝ) * δ ^ m
          = 2 * (Nat.factorial m : ℝ) ^ 2 * Cn * V * (geodPtCard m Λ : ℝ) * δ ^ m /
              ((η₁ V / 40) ^ m * vB) by ring]
      exact (le_div_iff₀ hsp).mpr h1
    -- the star inequality
    have hS : (J₀ : ℝ) * K₀ * V * Real.sqrt ((m : ℝ) / 2) * C_r * δ ^ (m / 2 - 1)
        ≤ ρ_ ^ (m / 2 - 1) := by
      have hr1 : 1 ≤ m / 2 - 1 := by omega
      have hκpow : Real.sqrt ((m : ℝ) / 2) * (J₀ : ℝ) * K₀ * V * C_r ≤ κ ^ (m / 2 - 1) := by
        have h1 : Real.sqrt ((m : ℝ) / 2) * (J₀ : ℝ) * K₀ * V * C_r ≤ up :=
          le_trans (le_max_right _ _) (le_max_right _ _)
        have h2 : up ≤ κ ^ (m / 2 - 1) := by
          rw [hκdef]
          calc up = up ^ 1 := (pow_one up).symm
            _ ≤ up ^ ((m / 2 - 1) * (m / 2 - 1)) :=
                pow_le_pow_right₀ hup1 (by nlinarith [hr1])
            _ = (up ^ (m / 2 - 1)) ^ (m / 2 - 1) := pow_mul _ _ _
        exact le_trans h1 h2
      have h3 : Real.sqrt ((m : ℝ) / 2) * (J₀ : ℝ) * K₀ * V * C_r * δ ^ (m / 2 - 1)
          ≤ (2 * δ * κ) ^ (m / 2 - 1) := by
        have h4 : (2 * δ * κ) ^ (m / 2 - 1) = 2 ^ (m / 2 - 1) * (δ ^ (m / 2 - 1) * κ ^ (m / 2 - 1)) := by
          rw [mul_pow, mul_pow]
          ring
        have h5 : (1 : ℝ) ≤ 2 ^ (m / 2 - 1) := one_le_pow₀ (by norm_num)
        have h6 : 0 ≤ δ ^ (m / 2 - 1) := by positivity
        have h7 : 0 ≤ κ ^ (m / 2 - 1) := by positivity
        have h8 : 0 ≤ Real.sqrt ((m : ℝ) / 2) * (J₀ : ℝ) * K₀ * V * C_r := by positivity
        rw [h4]
        calc Real.sqrt ((m : ℝ) / 2) * (J₀ : ℝ) * K₀ * V * C_r * δ ^ (m / 2 - 1)
            = (Real.sqrt ((m : ℝ) / 2) * (J₀ : ℝ) * K₀ * V * C_r) * δ ^ (m / 2 - 1) := by ring
          _ ≤ κ ^ (m / 2 - 1) * δ ^ (m / 2 - 1) := mul_le_mul_of_nonneg_right hκpow h6
          _ = δ ^ (m / 2 - 1) * κ ^ (m / 2 - 1) := by ring
          _ ≤ 2 ^ (m / 2 - 1) * (δ ^ (m / 2 - 1) * κ ^ (m / 2 - 1)) :=
              le_mul_of_one_le_left (by positivity) h5
      have h9 : (2 * δ * κ) ^ (m / 2 - 1) ≤ ρ_ ^ (m / 2 - 1) :=
        pow_le_pow_left₀ (by positivity) (by rw [hρ_def]; exact le_max_right _ _) _
      calc (J₀ : ℝ) * K₀ * V * Real.sqrt ((m : ℝ) / 2) * C_r * δ ^ (m / 2 - 1)
          = Real.sqrt ((m : ℝ) / 2) * (J₀ : ℝ) * K₀ * V * C_r * δ ^ (m / 2 - 1) := by ring
        _ ≤ _ := h3
        _ ≤ _ := h9
    -- the product lower bound
    have hle : (s * Real.sqrt (∑ i, (ρt i) ^ 2)) * ρ_ ^ (m / 2 - 1) / Real.sqrt ((m : ℝ) / 2)
        ≤ ∏ i, ρ i := by
      obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ ρt ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
      have hi₀' : ∀ j, ρt j ≤ ρt i₀ := fun j => hi₀ j (Finset.mem_univ j)
      have hprod1 : ρt i₀ * ρ_ ^ (m / 2 - 1) ≤ ∏ i, ρt i := by
        rw [← Finset.mul_prod_erase Finset.univ ρt (Finset.mem_univ i₀)]
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (hρtpos i₀))
        have h5 : ∏ i ∈ Finset.univ.erase i₀, (ρ_ : ℝ) ≤ ∏ i ∈ Finset.univ.erase i₀, ρt i :=
          Finset.prod_le_prod₀ (fun i _ => le_of_lt hρ_pos) (fun i _ => le_max_right _ _)
        rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ,
          Fintype.card_fin] at h5
        simpa using h5
      have hsum : Real.sqrt (∑ i, (ρt i) ^ 2) ≤ Real.sqrt ((m : ℝ) / 2) * ρt i₀ := by
        have h6 : ∑ i : Fin (m / 2), (ρt i) ^ 2 ≤ ((m : ℝ) / 2) * (ρt i₀) ^ 2 := by
          calc ∑ i : Fin (m / 2), (ρt i) ^ 2 ≤ ∑ _i : Fin (m / 2), (ρt i₀) ^ 2 :=
                Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (le_of_lt (hρtpos i)) (hi₀' i) 2)
            _ = ((m / 2 : ℕ) : ℝ) * (ρt i₀) ^ 2 := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            _ = ((m : ℝ) / 2) * (ρt i₀) ^ 2 := by rw [hcast]
        calc Real.sqrt (∑ i, (ρt i) ^ 2) ≤ Real.sqrt (((m : ℝ) / 2) * (ρt i₀) ^ 2) :=
              Real.sqrt_le_sqrt h6
          _ = Real.sqrt ((m : ℝ) / 2) * ρt i₀ := by
              rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (le_of_lt (hρtpos i₀))]
      have hprodr : ∏ i, ρ i = s ^ (m / 2) * ∏ i, ρt i := by
        rw [hρdef, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hs1' : s ≤ s ^ (m / 2) := by
        calc s = s ^ 1 := (pow_one s).symm
          _ ≤ s ^ (m / 2) := pow_le_pow_right₀ hs1 (by omega)
      have hkey : (s * Real.sqrt (∑ i, (ρt i) ^ 2)) * ρ_ ^ (m / 2 - 1)
          ≤ s ^ (m / 2) * (ρt i₀ * ρ_ ^ (m / 2 - 1)) * Real.sqrt ((m : ℝ) / 2) := by
        have h7 : s * Real.sqrt (∑ i, (ρt i) ^ 2) * ρ_ ^ (m / 2 - 1)
            ≤ s * (Real.sqrt ((m : ℝ) / 2) * ρt i₀) * ρ_ ^ (m / 2 - 1) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hsum (by linarith [hs1])
        have h8 : s * (Real.sqrt ((m : ℝ) / 2) * ρt i₀) * ρ_ ^ (m / 2 - 1)
            ≤ s ^ (m / 2) * (Real.sqrt ((m : ℝ) / 2) * ρt i₀) * ρ_ ^ (m / 2 - 1) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hs1' (by positivity)
        calc (s * Real.sqrt (∑ i, (ρt i) ^ 2)) * ρ_ ^ (m / 2 - 1)
            = s * Real.sqrt (∑ i, (ρt i) ^ 2) * ρ_ ^ (m / 2 - 1) := by ring
          _ ≤ s * (Real.sqrt ((m : ℝ) / 2) * ρt i₀) * ρ_ ^ (m / 2 - 1) := h7
          _ ≤ s ^ (m / 2) * (Real.sqrt ((m : ℝ) / 2) * ρt i₀) * ρ_ ^ (m / 2 - 1) := h8
          _ = s ^ (m / 2) * (ρt i₀ * ρ_ ^ (m / 2 - 1)) * Real.sqrt ((m : ℝ) / 2) := by ring
      rw [hprodr, div_le_iff₀ hspos]
      exact le_trans hkey (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod1 (by positivity)) (by positivity))
    -- (j) the Dirichlet step
    have hφinj : ∀ c ∈ gsvSmallNrm m hA1 hI1 hA hI Λ, ∀ d ∈ gsvSmallNrm m hA1 hI1 hA hI Λ,
        φ c = φ d → c = d := by
      intro c hc d hd hcd
      have hmem : c * d⁻¹ ∈ gsvSmallNrm m hA1 hI1 hA hI Λ :=
        (gsvSmallNrm m hA1 hI1 hA hI Λ).mul_mem hc ((gsvSmallNrm m hA1 hI1 hA hI Λ).inv_mem hd)
      have hdmem : d⁻¹ ∈ gsvSmallNrm m hA1 hI1 hA hI Λ :=
        (gsvSmallNrm m hA1 hI1 hA hI Λ).inv_mem hd
      have hφinv : φ d⁻¹ = - φ d := by
        have h := hφadd d (Subgroup.mem_sup_left hd) d⁻¹ (Subgroup.mem_sup_left hdmem)
        rw [mul_inv_cancel, hφ1] at h
        exact eq_neg_of_add_eq_zero_right h.symm
      have hz : φ (c * d⁻¹) = 0 := by
        rw [hφadd c (Subgroup.mem_sup_left hc) d⁻¹ (Subgroup.mem_sup_left hdmem), hφinv, hcd]
        abel
      have hblk0 : ∀ (i : Fin (m / 2)) (x y : ℝ), ∃ t : ℝ,
          (t : AddCircle (2 * Real.pi)) = (0 : Fin (m / 2) → AddCircle (2 * Real.pi)) i ∧
          (c * d⁻¹) (x • e (i, Fin.castSucc 0) + y • e (i, 1)) =
            (Real.cos t * x - Real.sin t * y) • e (i, Fin.castSucc 0) +
              (Real.sin t * x + Real.cos t * y) • e (i, 1) := by
        intro i x y
        obtain ⟨t, ht, hform⟩ := hblk (c * d⁻¹) (Subgroup.mem_sup_left hmem) i x y
        exact ⟨t, by rw [Pi.zero_apply, ht, hz, Pi.zero_apply], hform⟩
      have h1 : c * d⁻¹ = 1 := eqOneOfPhiEqZero m e (c * d⁻¹) 0 hblk0 (fun i => rfl)
      exact mul_inv_eq_one.mp h1
    have hcardA : Nat.card AangR = Nat.card (gsvSmallNrm m hA1 hI1 hA hI Λ) := by
      have hbij : Function.Bijective (fun c : gsvSmallNrm m hA1 hI1 hA hI Λ =>
          (⟨φ (c : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m), ⟨c, c.2, rfl⟩⟩ : AangR)) := by
        constructor
        · intro c d hcd
          exact Subtype.ext (hφinj c c.2 d d.2 (Subtype.ext_iff.mp hcd))
        · intro f
          obtain ⟨c, hc, hcf⟩ := (hAangRmem f).mp f.2
          exact ⟨⟨c, hc⟩, Subtype.ext hcf⟩
      exact Nat.card_congr (Equiv.ofBijective _ hbij).symm
    have hcardP : (geodPtCard m Λ : ℝ) ≤ (J₀ : ℝ) * (Nat.card AangR : ℝ) := by
      have h1 := hJ₀spec Λ hdisc
      rw [gsvPtCardEq m hA1 hI1 hA hI Λ, hcardA]
      exact_mod_cast h1
    -- the rescaled point norm
    set W : ℝ := s * Real.sqrt (∑ i, (ρt i) ^ 2) with hWdef
    have hWpos : 0 < W := by
      rw [hWdef]
      have h1 : 0 < ∑ i : Fin (m / 2), (ρt i) ^ 2 := by
        haveI : Nonempty (Fin (m / 2)) := ⟨⟨0, by omega⟩⟩
        exact Finset.sum_pos (fun i _ => pow_pos (hρtpos i) 2) Finset.univ_nonempty
      exact mul_pos (lt_of_lt_of_le zero_lt_one hs1) (Real.sqrt_pos.mpr h1)
    have hWmax : ∀ i, ρt i ≤ W := by
      intro i
      have h1 : ρt i ≤ Real.sqrt (∑ j, (ρt j) ^ 2) := by
        have h2 : (ρt i) ^ 2 ≤ ∑ j : Fin (m / 2), (ρt j) ^ 2 :=
          Finset.single_le_sum (fun j _ => pow_nonneg (le_of_lt (hρtpos j)) 2) (Finset.mem_univ i)
        calc ρt i = Real.sqrt ((ρt i) ^ 2) := (Real.sqrt_sq (le_of_lt (hρtpos i))).symm
          _ ≤ Real.sqrt (∑ j, (ρt j) ^ 2) := Real.sqrt_le_sqrt h2
      calc ρt i ≤ Real.sqrt (∑ j, (ρt j) ^ 2) := h1
        _ ≤ s * Real.sqrt (∑ j, (ρt j) ^ 2) := le_mul_of_one_le_left (Real.sqrt_nonneg _) hs1
        _ = W := hWdef.symm
    have hWρ : 2 * δ ≤ W := by
      have h1 : ρ_ ≤ ρt ⟨0, by omega⟩ := le_max_right _ _
      have h2 : 2 * δ * κ ≤ ρ_ := by rw [hρ_def]; exact le_max_right _ _
      have h3 : ρt ⟨0, by omega⟩ ≤ W := hWmax _
      nlinarith [h1, h2, h3, hδpos, hκ1]
    have hWnn : 0 ≤ W := le_of_lt hWpos
    have hWz_le : ‖W_z‖ ^ 2 ≤ ∑ i, (ρt i) ^ 2 := by
      rw [blockNormSqSum m e W_z]
      exact Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) 2)
    -- the Dirichlet scale
    set J : ℕ := ⌊δ / (W * T₀)⌋₊ with hJdef
    have hJT : (J : ℝ) * T₀ ≤ δ / W := by
      have hWT : 0 < W * T₀ := mul_pos hWpos hT₀pos
      have h1 : (J : ℝ) ≤ δ / (W * T₀) := Nat.floor_le (div_nonneg hδpos.le hWT.le)
      calc (J : ℝ) * T₀ ≤ (δ / (W * T₀)) * T₀ := mul_le_mul_of_nonneg_right h1 hT₀pos.le
        _ = δ / W := by field_simp
    -- the smallness of the scale
    have hsm : ∀ i : Fin (m / 2), δ ≤ 2 * Real.pi * (2 * Real.sqrt ((m : ℝ) / 2) * ρ i) := by
      intro i
      have h3 : δ ≤ ρ_ := by
        have h4 : 2 * δ * κ ≤ ρ_ := by rw [hρ_def]; exact le_max_right _ _
        have h5 : δ ≤ 2 * δ * κ := by nlinarith only [hδpos, hκ1]
        exact le_trans h5 h4
      have h1 := hρρ i
      have hρ1 : 1 ≤ ρ i := by
        have hρ_1 : 1 ≤ ρ_ := by rw [hρ_def]; exact le_max_left _ _
        have hρt_1 : 1 ≤ ρt i := by
          rw [hρtdef]
          exact le_trans hρ_1 (le_max_right _ _)
        rw [hρdef]
        calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
          _ ≤ s * ρt i := mul_le_mul hs1 hρt_1 zero_le_one (by linarith [hs1])
      have hδle : δ ≤ 1 / 2 + Real.sqrt ((m : ℝ) / 2) := by
        rw [hδdef, hcδdef]
        nlinarith only [hη16, hη, hspos]
      have h4 : 1 / 2 + Real.sqrt ((m : ℝ) / 2) ≤ 4 * Real.pi * Real.sqrt ((m : ℝ) / 2) := by
        have h2 : (1 : ℝ) ≤ Real.sqrt ((m : ℝ) / 2) := by
          have h3 : (1 : ℝ) ≤ (m : ℝ) / 2 := by
            have h4 : (2 : ℝ) ≤ (m : ℝ) / 2 := by
              have h5 : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
              linarith
            linarith
          calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
            _ ≤ Real.sqrt ((m : ℝ) / 2) := Real.sqrt_le_sqrt h3
        have h5 : 3 * Real.sqrt ((m : ℝ) / 2) ≤ Real.pi * Real.sqrt ((m : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right Real.pi_gt_three.le (Real.sqrt_nonneg _)
        have h6 : (1 : ℝ) / 2 ≤ 11 * Real.sqrt ((m : ℝ) / 2) := by
          have h7 : (11 : ℝ) * 1 ≤ 11 * Real.sqrt ((m : ℝ) / 2) :=
            mul_le_mul_of_nonneg_left h2 (by norm_num)
          linarith
        nlinarith only [h5, h6]
      calc δ ≤ 1 / 2 + Real.sqrt ((m : ℝ) / 2) := hδle
        _ ≤ 4 * Real.pi * Real.sqrt ((m : ℝ) / 2) := h4
        _ ≤ 4 * Real.pi * Real.sqrt ((m : ℝ) / 2) * ρ i :=
            le_mul_of_one_le_right (by positivity) hρ1
        _ = 2 * Real.pi * (2 * Real.sqrt ((m : ℝ) / 2) * ρ i) := by ring
    have hmin : ∀ a ∈ AangR, a ≠ 0 → δ ^ 2 ≤ ∑ i, (ρ i) ^ 2 * (chord (a i)) ^ 2 := hb'min'
    -- the cleared form of the counting estimate
    have hcleared : (∏ i, (ρ i)) * (J₀ : ℝ) * C_r * W * T₀
        ≤ (geodPtCard m Λ : ℝ) * δ ^ (m / 2 + 1) := by
      have hprodbound : W * ((J₀ : ℝ) * K₀ * V * C_r * δ ^ (m / 2 - 1)) ≤ ∏ i, (ρ i) := by
        have h7 := hS
        have h8 : W * ρ_ ^ (m / 2 - 1) ≤ (∏ i, (ρ i)) * Real.sqrt ((m : ℝ) / 2) := by
          have h9 := hle
          rw [div_le_iff₀ hspos] at h9
          linarith only [h9]
        have h10 : W * ((J₀ : ℝ) * K₀ * V * C_r * δ ^ (m / 2 - 1))
            ≤ W * ρ_ ^ (m / 2 - 1) / Real.sqrt ((m : ℝ) / 2) := by
          rw [le_div_iff₀ hspos]
          calc W * ((J₀ : ℝ) * K₀ * V * C_r * δ ^ (m / 2 - 1)) * Real.sqrt ((m : ℝ) / 2)
              = W * ((J₀ : ℝ) * K₀ * V * Real.sqrt ((m : ℝ) / 2) * C_r
                  * δ ^ (m / 2 - 1)) := by ring
            _ ≤ W * ρ_ ^ (m / 2 - 1) := mul_le_mul_of_nonneg_left h7 hWnn
        have h10' : W * ρ_ ^ (m / 2 - 1) / Real.sqrt ((m : ℝ) / 2) ≤ ∏ i, (ρ i) := by
          rw [div_le_iff₀ hspos]
          exact h8
        exact le_trans h10 h10'
      have hprodpos : 0 < ∏ i, (ρ i) := Finset.prod_pos (fun i _ => hρpos i)
      have hfac : (J₀ : ℝ) * C_r * W / (∏ i, (ρ i) ^ 2)
          ≤ 1 / (K₀ * V * δ ^ (m / 2 - 1) * (∏ i, (ρ i))) := by
        rw [gsv_div_le_div (Finset.prod_pos (fun i _ => pow_pos (hρpos i) 2))
          (mul_pos (mul_pos (mul_pos hK₀pos hV) (pow_pos hδpos _)) hprodpos), one_mul]
        rw [show (∏ i : Fin (m / 2), (ρ i) ^ 2) = (∏ i : Fin (m / 2), ρ i) ^ 2 from by
          rw [Finset.prod_pow]]
        rw [show (J₀ : ℝ) * C_r * W * (K₀ * V * δ ^ (m / 2 - 1) * (∏ i, (ρ i)))
              = (W * ((J₀ : ℝ) * K₀ * V * C_r * δ ^ (m / 2 - 1))) * (∏ i, (ρ i)) from by ring]
        calc (W * ((J₀ : ℝ) * K₀ * V * C_r * δ ^ (m / 2 - 1))) * (∏ i, (ρ i))
            ≤ (∏ i, (ρ i)) * (∏ i, (ρ i)) := mul_le_mul_of_nonneg_right hprodbound hprodpos.le
          _ = (∏ i, (ρ i)) ^ 2 := (pow_two _).symm
      have hstep : T₀ * (J₀ : ℝ) * C_r * W
          ≤ K₀ * V * (geodPtCard m Λ : ℝ) * δ ^ m * ((J₀ : ℝ) * C_r * W / (∏ i, (ρ i) ^ 2)) := by
        have hprod2pos : 0 < (∏ i, (ρ i) ^ 2) := Finset.prod_pos (fun i _ => pow_pos (hρpos i) 2)
        have h1 : T₀ * (∏ i, (ρ i) ^ 2) * ((J₀ : ℝ) * C_r * W / (∏ i, (ρ i) ^ 2))
            ≤ K₀ * V * (geodPtCard m Λ : ℝ) * δ ^ m * ((J₀ : ℝ) * C_r * W / (∏ i, (ρ i) ^ 2)) :=
          mul_le_mul_of_nonneg_right hTube
            (div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg J₀) (le_of_lt hC_rpos))
              (le_of_lt hWpos)) hprod2pos.le)
        have h2 : T₀ * (∏ i, (ρ i) ^ 2) * ((J₀ : ℝ) * C_r * W / (∏ i, (ρ i) ^ 2))
            = T₀ * (J₀ : ℝ) * C_r * W := by
          have hne : (∏ i, (ρ i) ^ 2) ≠ 0 := ne_of_gt hprod2pos
          field_simp
        rwa [h2] at h1
      calc (∏ i, (ρ i)) * (J₀ : ℝ) * C_r * W * T₀
          = (∏ i, (ρ i)) * (T₀ * (J₀ : ℝ) * C_r * W) := by ring
        _ ≤ (∏ i, (ρ i)) * (K₀ * V * (geodPtCard m Λ : ℝ) * δ ^ m *
              (1 / (K₀ * V * δ ^ (m / 2 - 1) * (∏ i, (ρ i))))) := by
            refine mul_le_mul_of_nonneg_left ?_ hprodpos.le
            exact le_trans hstep (mul_le_mul_of_nonneg_left hfac (by positivity))
        _ = (geodPtCard m Λ : ℝ) * δ ^ (m / 2 + 1) := by
            have h3 : (m / 2 - 1) + (m / 2 + 1) = m := by omega
            have hpow : δ ^ (m / 2 - 1) * δ ^ (m / 2 + 1) = δ ^ m := by
              rw [← pow_add, h3]
            rw [← hpow]
            field_simp
            try ring
    have hPpos : 0 < (geodPtCard m Λ : ℝ) := by
      have hpp : 0 < ∏ i, (ρ i) := Finset.prod_pos (fun i _ => hρpos i)
      have hL : 0 < (∏ i, (ρ i)) * (J₀ : ℝ) * C_r * W * T₀ :=
        mul_pos (mul_pos (mul_pos (mul_pos hpp (by exact_mod_cast hJ₀pos)) hC_rpos) hWpos) hT₀pos
      have hR : 0 < (geodPtCard m Λ : ℝ) * δ ^ (m / 2 + 1) := lt_of_lt_of_le hL hcleared
      exact pos_of_mul_pos_left hR (pow_nonneg hδpos.le _)
    have hsm' : ∀ i : Fin (m / 2),
        δ ≤ 2 * Real.pi * (2 * Real.sqrt (((m / 2 : ℕ) : ℝ)) * ρ i) :=
      fun i => by rw [← hcast]; exact hsm i
    have hcount : ∏ i, ⌈2 * Real.pi / (δ / (2 * Real.sqrt (((m / 2 : ℕ) : ℝ)) * ρ i))⌉₊ <
        (J + 1) * Nat.card AangR := by
      have hAcardpos : 0 < Nat.card AangR :=
        Nat.card_pos_iff.mpr ⟨⟨0, AangR.zero_mem⟩, hfinAangR⟩
      have hApos : 0 < (Nat.card AangR : ℝ) := by exact_mod_cast hAcardpos
      have hJ₀posR : (0 : ℝ) < (J₀ : ℝ) := by exact_mod_cast hJ₀pos
      have hδrpos : 0 < δ ^ (m / 2) := by positivity
      have h1le : 1 ≤ (J + 1) * Nat.card AangR :=
        Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos J) hAcardpos)
      have hNat : ((J + 1) * Nat.card AangR - 1) + 1 = (J + 1) * Nat.card AangR :=
        Nat.sub_add_cancel h1le
      -- the key estimate
      have hkey : C_r * (∏ i, (ρ i)) / δ ^ (m / 2) < ((J : ℝ) + 1) * (Nat.card AangR : ℝ) := by
        have hfloor : δ / (W * T₀) < (J : ℝ) + 1 := by
          rw [hJdef]; exact Nat.lt_floor_add_one _
        have hdiv : (∏ i, (ρ i)) * (J₀ : ℝ) * C_r / ((geodPtCard m Λ : ℝ) * δ ^ (m / 2))
            ≤ δ / (W * T₀) := by
          have h1 : δ * ((geodPtCard m Λ : ℝ) * δ ^ (m / 2))
              = (geodPtCard m Λ : ℝ) * δ ^ (m / 2 + 1) := by rw [pow_add]; ring
          rw [gsv_div_le_div (mul_pos hPpos hδrpos) (mul_pos hWpos hT₀pos), h1]
          linarith only [hcleared]
        have hlt : (∏ i, (ρ i)) * (J₀ : ℝ) * C_r / ((geodPtCard m Λ : ℝ) * δ ^ (m / 2))
            < ((J : ℝ) + 1) := lt_of_le_of_lt hdiv hfloor
        have h3 : (∏ i, (ρ i)) * (J₀ : ℝ) * C_r
            < ((J : ℝ) + 1) * ((geodPtCard m Λ : ℝ) * δ ^ (m / 2)) := by
          rw [div_lt_iff₀ (mul_pos hPpos hδrpos)] at hlt
          linarith only [hlt]
        have h4 : ((J : ℝ) + 1) * ((geodPtCard m Λ : ℝ) * δ ^ (m / 2))
            ≤ ((J : ℝ) + 1) * ((J₀ : ℝ) * (Nat.card AangR : ℝ) * δ ^ (m / 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc (geodPtCard m Λ : ℝ) * δ ^ (m / 2)
              ≤ ((J₀ : ℝ) * (Nat.card AangR : ℝ)) * δ ^ (m / 2) :=
                mul_le_mul_of_nonneg_right hcardP hδrpos.le
            _ = (J₀ : ℝ) * (Nat.card AangR : ℝ) * δ ^ (m / 2) := by ring
        have h5 : (∏ i, (ρ i)) * C_r < ((J : ℝ) + 1) * (Nat.card AangR : ℝ) * δ ^ (m / 2) := by
          have h6 : (∏ i, (ρ i)) * (J₀ : ℝ) * C_r
              < ((J : ℝ) + 1) * (J₀ : ℝ) * (Nat.card AangR : ℝ) * δ ^ (m / 2) :=
            lt_of_lt_of_le h3 (by linarith only [h4])
          have h7 : 0 < (J₀ : ℝ) := hJ₀posR
          nlinarith only [h6, h7, hApos, hδrpos]
        rw [div_lt_iff₀ hδrpos]
        linarith only [h5]
      have hbox : (2 : ℝ) ^ (m / 2) *
            ((4 * Real.pi * Real.sqrt ((m : ℝ) / 2)) ^ (m / 2) * (∏ i, (ρ i)) / δ ^ (m / 2))
          < (((J + 1) * Nat.card AangR - 1 : ℕ) : ℝ) + 1 := by
        have hc : ((((J + 1) * Nat.card AangR - 1 : ℕ)) : ℝ) + 1
            = ((J : ℝ) + 1) * (Nat.card AangR : ℝ) := by
          rw [Nat.cast_sub h1le]
          push_cast
          ring
        rw [hc]
        have h2 : (2 : ℝ) ^ (m / 2) *
              ((4 * Real.pi * Real.sqrt ((m : ℝ) / 2)) ^ (m / 2) * (∏ i, (ρ i)) / δ ^ (m / 2))
            = C_r * (∏ i, (ρ i)) / δ ^ (m / 2) := by rw [hC_rdef]; ring
        rw [h2]; exact hkey
      have hbig : ∀ i, 1 ≤ 2 * Real.pi / (δ / (2 * Real.sqrt ((m : ℝ) / 2) * ρ i)) := by
        intro i
        rw [le_div_iff₀ (by positivity), one_mul, div_le_iff₀ (by positivity)]
        exact hsm i
      have hbig' : ∀ i : Fin (m / 2),
          1 ≤ 2 * Real.pi / (δ / (2 * Real.sqrt (((m / 2 : ℕ) : ℝ)) * ρ i)) :=
        fun i => by rw [← hcast]; exact hbig i
      have hbox' : (2 : ℝ) ^ (m / 2) *
            ((4 * Real.pi * Real.sqrt (((m / 2 : ℕ) : ℝ))) ^ (m / 2) * (∏ i, (ρ i))
              / δ ^ (m / 2))
          < (((J + 1) * Nat.card AangR - 1 : ℕ) : ℝ) + 1 := by
        rw [← hcast]; exact hbox
      have hc := countingCondition (m / 2) (by omega) δ hδpos ρ hρpos hbig'
        ((J + 1) * Nat.card AangR - 1) hbox'
      rwa [hNat] at hc
    -- the screw
    obtain ⟨j, hj1, hjJ, a, haA, hjT, hdisp⟩ :=
      screwExists (m / 2) (by omega) T₀ δ W hT₀pos hδpos hWpos
        (φ (nrmStd 1 m h₂)) AangR ρ hρpos J hJT hsm' hmin hcount
    -- the element of `Λ` realising the found angles
    obtain ⟨ca, hcaA, hcaφ⟩ := (hAangRmem a).mp haA
    obtain ⟨pa, hpaP, hpanrm⟩ := hnrmSection ca hcaA
    have hpaStab : pa ∈ SetStabStd 1 m := gsvPtSub_mem_stab m hA1 hI1 hA hI Λ hpaP
    have hpaN : pa ∈ N := gsvPtSub_le_geodStab m hA1 hI1 hA hI Λ hpaP
    set γ : PO (1 + m) 1 := h₂ ^ j * pa with hγdef
    have hh₂jN : h₂ ^ j ∈ N := Subgroup.pow_mem N hh₂N j
    have hh₂jstab : h₂ ^ j ∈ SetStabStd 1 m := hStab _ hh₂jN
    have hγN : γ ∈ N := N.mul_mem hh₂jN hpaN
    have hγΛ : γ ∈ Λ := (Subgroup.mem_inf.mp hγN).1
    have hγstab : γ ∈ SetStabStd 1 m := hStab γ hγN
    have hγres : resStd 1 m γ = g₀ ^ (((Nat.factorial m) ^ 2) * j) := by
      rw [hγdef, rhd_resStd_mul 1 m hA1 hI1 hA hI hh₂jstab hpaStab,
        gsv_resStd_pow hA1 hI1 hA hI hh₂stab j, hh₂res,
        gsvPtSub_resStd m hA1 hI1 hA hI Λ hpaP, mul_one, pow_mul]
    have hγnrm : nrmStd 1 m γ = (nrmStd 1 m h₂) ^ j * ca := by
      rw [hγdef, rhd_nrmStd_mul 1 m hA1 hI1 hA hI hh₂jstab hpaStab,
        gsv_nrmStd_pow hA1 hI1 hA hI hh₂stab j, hpanrm]
    -- the translation part of `γ` at `v_z`
    have hγdisp : hdist v_z (resStd 1 m γ • v_z) = (j : ℝ) * T₀ := by
      have hk : hdist v_z (g₀ ^ (((Nat.factorial m) ^ 2) * j) • v_z)
          = ((((Nat.factorial m) ^ 2) * j : ℕ) : ℝ) * hdist (0 : Submission.Mostow.E 1) (g₀ • (0 : Submission.Mostow.E 1)) := by
        have h := hdistZpowFixedfree hA1 hI1 g₀ hg₀free v_z (((((Nat.factorial m) ^ 2) * j : ℕ)) : ℤ)
        rw [zpow_natCast] at h
        rw [h, abs_of_nonneg (by positivity)]
        simp only [Int.cast_natCast]
      rw [hγres, hk, hT₀def]
      push_cast
      ring
    -- the normal part of `γ` at `W_z`
    have hγnrmdisp : ‖nrmStd 1 m γ W_z - W_z‖ ≤ δ := by
      have hmem : (nrmStd 1 m h₂) ^ j * ca ∈
          gsvSmallNrm m hA1 hI1 hA hI Λ ⊔ Subgroup.zpowers (nrmStd 1 m h₂) :=
        Subgroup.mul_mem (gsvSmallNrm m hA1 hI1 hA hI Λ ⊔ Subgroup.zpowers (nrmStd 1 m h₂))
          (Subgroup.mem_sup_right (Subgroup.pow_mem (Subgroup.zpowers (nrmStd 1 m h₂))
            (Subgroup.mem_zpowers (nrmStd 1 m h₂)) j))
          (Subgroup.mem_sup_left hcaA)
      have hφpow : ∀ n : ℕ, φ ((nrmStd 1 m h₂) ^ n) = (n : ℕ) • φ (nrmStd 1 m h₂) := by
        intro n
        induction n with
        | zero => rw [pow_zero, zero_nsmul, hφ1]
        | succ k ih =>
            rw [pow_succ, hφadd ((nrmStd 1 m h₂) ^ k) _ (nrmStd 1 m h₂) _, ih, succ_nsmul]
            · exact Subgroup.pow_mem
                (gsvSmallNrm m hA1 hI1 hA hI Λ ⊔ Subgroup.zpowers (nrmStd 1 m h₂))
                (Subgroup.mem_sup_right (Subgroup.mem_zpowers (nrmStd 1 m h₂))) k
            · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (nrmStd 1 m h₂))
      have hφγ : φ ((nrmStd 1 m h₂) ^ j * ca) = (j : ℕ) • φ (nrmStd 1 m h₂) + a := by
        rw [hφadd ((nrmStd 1 m h₂) ^ j) _ ca (Subgroup.mem_sup_left hcaA), hφpow j, hcaφ]
        exact Subgroup.pow_mem (gsvSmallNrm m hA1 hI1 hA hI Λ ⊔ Subgroup.zpowers (nrmStd 1 m h₂))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers (nrmStd 1 m h₂))) j
      have hblkγ : ∀ (i : Fin (m / 2)) (x y : ℝ), ∃ t : ℝ,
          (t : AddCircle (2 * Real.pi)) = ((j : ℕ) • φ (nrmStd 1 m h₂) + a) i ∧
          (nrmStd 1 m γ) (x • e (i, Fin.castSucc 0) + y • e (i, 1)) =
            (Real.cos t * x - Real.sin t * y) • e (i, Fin.castSucc 0) +
              (Real.sin t * x + Real.cos t * y) • e (i, 1) := by
        intro i x y
        obtain ⟨t, ht, hform⟩ := hblk ((nrmStd 1 m h₂) ^ j * ca) hmem i x y
        refine ⟨t, ?_, ?_⟩
        · rw [ht, hφγ]
        · rw [hγnrm]; exact hform
      have hdom : ∀ i : Fin (m / 2),
          ‖(inner ℝ (e (i, Fin.castSucc 0)) W_z) • e (i, Fin.castSucc 0) +
              (inner ℝ (e (i, 1)) W_z) • e (i, 1)‖ ≤ ρ i := by
        intro i
        have h1 : ‖(inner ℝ (e (i, Fin.castSucc 0)) W_z) • e (i, Fin.castSucc 0) +
              (inner ℝ (e (i, 1)) W_z) • e (i, 1)‖ ≤ ρt i := le_max_left _ _
        have h2 : ρt i ≤ ρ i := by rw [hρdef]; nlinarith [hs1, hρtpos i]
        linarith
      exact rotDispOfBlock m e (nrmStd 1 m γ) ((j : ℕ) • φ (nrmStd 1 m h₂) + a) hblkγ
        W_z ρ hρpos δ hδpos hdom hdisp
    -- infinite order
    have hγord : orderOf γ = 0 := by
      rw [orderOf_eq_zero_iff]
      intro hfin
      obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
      have hres1 : resStd 1 m (γ ^ n) = 1 := by
        rw [hpow, rhd_resStd_one 1 m hA1 hI1 hA hI]
      have hres2 : resStd 1 m (γ ^ n) = g₀ ^ (((Nat.factorial m) ^ 2) * j * n) := by
        rw [gsv_resStd_pow hA1 hI1 hA hI hγstab n, hγres, ← pow_mul]
      have hg1 : g₀ ^ (((Nat.factorial m) ^ 2) * j * n) = 1 := by rw [← hres2, hres1]
      have hk : (((Nat.factorial m) ^ 2) * j * n) ≠ 0 := by
        have h3 : 0 < ((Nat.factorial m) ^ 2) * j * n := by positivity
        omega
      have hd1 : hdist v_z (g₀ ^ (((Nat.factorial m) ^ 2) * j * n) • v_z)
          = ((((Nat.factorial m) ^ 2) * j * n : ℕ) : ℝ) *
              hdist (0 : Submission.Mostow.E 1) (g₀ • (0 : Submission.Mostow.E 1)) := by
        have h := hdistZpowFixedfree hA1 hI1 g₀ hg₀free v_z (((((Nat.factorial m) ^ 2) * j * n : ℕ)) : ℤ)
        rw [zpow_natCast] at h
        rw [h, abs_of_nonneg (by positivity)]
        simp only [Int.cast_natCast]
      have h4 : hdist v_z v_z = ((((Nat.factorial m) ^ 2) * j * n : ℕ) : ℝ) *
          hdist (0 : Submission.Mostow.E 1) (g₀ • (0 : Submission.Mostow.E 1)) := by
        have hthis : hdist v_z (g₀ ^ (((Nat.factorial m) ^ 2) * j * n) • v_z)
            = ((((Nat.factorial m) ^ 2) * j * n : ℕ) : ℝ) *
              hdist (0 : Submission.Mostow.E 1) (g₀ • (0 : Submission.Mostow.E 1)) := hd1
        rw [hg1] at hthis
        rw [hA1.2.2.2.1 v_z] at hthis
        exact hthis
      have h5 : 0 < ((((Nat.factorial m) ^ 2) * j * n : ℕ) : ℝ) *
          hdist (0 : Submission.Mostow.E 1) (g₀ • (0 : Submission.Mostow.E 1)) :=
        mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hk) hℓ₀pos
      rw [nib_hdist_self] at h4
      linarith [h4, h5]
    -- the displacement bound
    have hY : 2 * Real.arsinh (δ / 2) ≤ δ := by
      have h1 : Real.arsinh (δ / 2) ≤ δ / 2 := gsv_arsinh_le_self (by positivity)
      linarith
    have hX : Real.sqrt (1 + ‖W_z‖ ^ 2) * Real.sinh ((j : ℝ) * T₀ / 2) ≤ 3 * Real.sqrt 2 / 4 * δ := by
      have h1 : Real.sqrt (1 + ‖W_z‖ ^ 2) ≤ Real.sqrt 2 * W := by
        have hx : (0 : ℝ) ≤ ∑ i : Fin (m / 2), (ρt i) ^ 2 :=
          Finset.sum_nonneg (fun i _ => sq_nonneg (ρt i))
        have hW1 : 1 ≤ W := by
          have hρ_1 : 1 ≤ ρ_ := by rw [hρ_def]; exact le_max_left _ _
          have hρt1 : 1 ≤ ρt ⟨0, by omega⟩ := by
            rw [hρtdef]
            exact le_trans hρ_1 (le_max_right _ _)
          exact le_trans hρt1 (hWmax _)
        have hsumW : ∑ i : Fin (m / 2), (ρt i) ^ 2 ≤ W ^ 2 := by
          rw [hWdef, mul_pow, Real.sq_sqrt hx]
          exact le_mul_of_one_le_left hx (one_le_pow₀ hs1)
        have h2 : 1 + ‖W_z‖ ^ 2 ≤ 2 * W ^ 2 := by
          have h3 : 1 ≤ W ^ 2 := by nlinarith only [hW1]
          linarith only [hWz_le, hsumW, h3]
        calc Real.sqrt (1 + ‖W_z‖ ^ 2) ≤ Real.sqrt (2 * W ^ 2) := Real.sqrt_le_sqrt h2
          _ = Real.sqrt 2 * W := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hWnn]
      have h2 : Real.sinh ((j : ℝ) * T₀ / 2) ≤ 3 / 2 * (δ / (2 * W)) := by
        have h3 : (j : ℝ) * T₀ ≤ δ / W := hjT
        have h4 : (j : ℝ) * T₀ / 2 ≤ δ / (2 * W) := by
          have h5 : (j : ℝ) * T₀ / 2 ≤ (δ / W) / 2 := div_le_div_of_nonneg_right h3 (by norm_num)
          have h6 : (δ / W) / 2 = δ / (2 * W) := by
            have hWne : W ≠ 0 := ne_of_gt hWpos
            field_simp
          rwa [h6] at h5
        have h5 : δ / (2 * W) ≤ 1 / 2 := by
          rw [div_le_iff₀ (by linarith [hWpos] : (0 : ℝ) < 2 * W)]
          linarith only [hWρ, hδpos]
        exact le_trans (nib_sinh_half_le (by positivity) (by linarith)) (by linarith)
      calc Real.sqrt (1 + ‖W_z‖ ^ 2) * Real.sinh ((j : ℝ) * T₀ / 2)
          ≤ (Real.sqrt 2 * W) * (3 / 2 * (δ / (2 * W))) := by
            exact mul_le_mul h1 h2 (Real.sinh_nonneg_iff.mpr (by positivity))
              (mul_nonneg (Real.sqrt_nonneg 2) hWnn)
        _ = 3 * Real.sqrt 2 / 4 * δ := by field_simp; ring
    have hmain := geeDisplacement m hA1 hI1 hA hI γ hγstab v_z W_z ((j : ℝ) * T₀) δ
      (by positivity) (le_of_lt hδpos) (le_of_eq hγdisp) hγnrmdisp
    have hz_eq' : z = fermiW 1 m v_z W_z := hz_eq.symm
    rw [hz_eq']
    refine ⟨γ, hγΛ, hγord, ?_⟩
    calc hdist (fermiW 1 m v_z W_z) (γ • fermiW 1 m v_z W_z)
        ≤ 2 * Real.arsinh (Real.sqrt (1 + ‖W_z‖ ^ 2) * Real.sinh ((j : ℝ) * T₀ / 2)) +
            2 * Real.arsinh (δ / 2) := hmain
      _ ≤ 2 * (3 * Real.sqrt 2 / 4 * δ) + δ := by
            have h1 : Real.arsinh (Real.sqrt (1 + ‖W_z‖ ^ 2) * Real.sinh ((j : ℝ) * T₀ / 2))
                ≤ Real.sqrt (1 + ‖W_z‖ ^ 2) * Real.sinh ((j : ℝ) * T₀ / 2) :=
              gsv_arsinh_le_self (by
                refine mul_nonneg (by positivity) ?_
                exact Real.sinh_nonneg_iff.mpr (by positivity))
            linarith [h1, hX, hY]
      _ ≤ ((2 * Real.sqrt (1 + (m : ℝ) / 2) + 1) * cδ + 1) * η := by
            have h1 : δ = cδ * η := hδdef
            have h2 : 3 * Real.sqrt 2 / 2 ≤ 2 * Real.sqrt (1 + (m : ℝ) / 2) := by
              have h3 : (3 : ℝ) ≤ 1 + (m : ℝ) / 2 := by
                have h4 : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
                linarith
              have h6 : Real.sqrt 3 ≤ Real.sqrt (1 + (m : ℝ) / 2) := Real.sqrt_le_sqrt h3
              have h5 : 3 * Real.sqrt 2 / 2 ≤ 2 * Real.sqrt 3 := by
                have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
                have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
                have h2n : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
                have h3n : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
                nlinarith only [hs2, hs3, h2n, h3n]
              linarith only [h5, h6]
            rw [h1]
            have h7 : 3 * Real.sqrt 2 / 2 * (cδ * η)
                ≤ 2 * Real.sqrt (1 + (m : ℝ) / 2) * (cδ * η) :=
              mul_le_mul_of_nonneg_right h2 (mul_nonneg hcδpos.le hη.le)
            linarith only [h7, hη]

  · -- ============ Case A: `G` has no translation, so it is finite ============
    exfalso
    obtain ⟨DG, hDG, _⟩ := existsFDone hA1 hI1 G hGdisc
    haveI : Finite G := (finite_fixes_of_sq_eq_one hA1 hI1 G hsquares).1
    have htop : volH 1 DG = ⊤ := finiteFDmeasureTop hA1 hI1 G DG hDG
    have hCHdg := hCHG DG hDG
    rw [htop, ENNReal.top_mul (ne_of_gt hvolImgpos)] at hCHdg
    rw [top_le_iff] at hCHdg
    exact (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _)) hCHdg

end Work.Mostow.DirichletScrew
