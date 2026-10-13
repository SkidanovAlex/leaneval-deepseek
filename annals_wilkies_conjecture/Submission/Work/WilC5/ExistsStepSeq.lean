import Mathlib
import Submission.Work.WilC5.ValProp
import Submission.Work.WilC5.StepSeq
import Submission.Work.WilC5.StepKeyOfValProp
import Submission.Work.WilC5.StepSeqUnbounded
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.logFun_expE
import Submission.Work.WilC5.ValArith
import Submission.Work.WilC5.S4StepDefs
import Submission.Work.WilC5.StepSeqDecomp
import Submission.Work.WilC5.S4ExpG.Glue
import Submission.Work.WilC5.S4Exp.hynew_exp
import Submission.Work.WilC5.S4ExpF.logclosure_exp
import Submission.Work.WilC5.S4ExpF.Bridge
import Submission.Work.WilC5.LRcOps
import Submission.Work.WilC5.LRcReduct
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC5.Reduct
import Submission.Work.WilC5.expE_add_of_model
import Submission.Work.WilC5.stdPart
import Submission.Work.WilC5.ExistsStepSeqAux.TranslateNew
import Submission.Work.WilC5.ExistsStepSeqAux.InfOfLogRel

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

namespace ESSStep

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `SameArch 0 0`. -/
theorem sameArch_zero_zero : Work.WilC5.SameArch (0 : K) 0 := ⟨0, by simp⟩

/-- `SameArch` is invariant under a sign change of its first argument. -/
theorem sameArch_neg_left (x y : K) : Work.WilC5.SameArch (-x) y ↔ Work.WilC5.SameArch x y := by
  unfold Work.WilC5.SameArch
  rw [abs_neg]

/-- `SameArch` is invariant under a sign change of its second argument. -/
theorem sameArch_neg_right (x y : K) : Work.WilC5.SameArch x (-y) ↔ Work.WilC5.SameArch x y := by
  unfold Work.WilC5.SameArch
  rw [abs_neg]

/-- `IsFiniteVal` is invariant under sign. -/
theorem isFiniteVal_neg_iff (x : K) : Work.WilC5.IsFiniteVal (-x) ↔ Work.WilC5.IsFiniteVal x := by
  unfold Work.WilC5.IsFiniteVal
  rw [abs_neg]

theorem ESSNormalizeNew
    {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE]
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (B : WilkiesDesign.CG.LRc.Substructure K)
    (hBdcl : @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) (B : Set K) ⊆ (B : Set K))
    {c : K} (hc0 : c ≠ 0)
    (hcnew : ∀ b : ↥B, ¬ Work.WilC5.SameArch (b : K) c) :
    ∃ x0 : K, 0 < x0 ∧ ¬ Work.WilC5.IsFiniteVal x0 ∧
      (∀ b : ↥B, ¬ Work.WilC5.SameArch (b : K) x0) ∧
      x0 ∈ @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) ((B : Set K) ∪ {c}) ∧
      c ∈ @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) ((B : Set K) ∪ {x0}) := by
  classical
  have hTE : K ⊨ WilkiesDesign.CG.TE := inferInstance
  have hmem1 : (1 : K) ∈ (B : Set K) := by
    have h := B.fun_mem (Work.WilC5.ringSymL Ring.oneFunc) (fun i : Fin 0 => i.elim0)
      (fun i => i.elim0)
    have h' : (Work.WilC5.oneE : K) ∈ (B : Set K) := h
    rwa [hone] at h'
  have hnotunit : ¬ WilkiesDesign.CG.IsUnitVal c := by
    intro hu
    have hSA : Work.WilC5.SameArch c 1 := (Work.WilC5.IsUnitVal_iff_SameArch c).mp hu
    exact hcnew ⟨1, hmem1⟩ (Work.WilC5.SameArch_equiv.symm hSA)
  have hzeroR : (Work.WilC5.zeroE : K) = 0 := Work.WilC5.S4Exp.zeroE_eq_zero hTE hadd
  let myCR : FirstOrder.Ring.CompatibleRing K :=
    { toStructure := @Work.WilC5.lrcRingReduct K (Work.WilC5.instStructureLRcOfLEc K)
      funMap_add := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hys : ys = ![ys 0, ys 1] := by funext i; fin_cases i <;> rfl
        rw [hys]; exact hadd _ _
      funMap_mul := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hys : ys = ![ys 0, ys 1] := by funext i; fin_cases i <;> rfl
        rw [hys]; exact hmul _ _
      funMap_neg := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hys : ys = ![ys 0] := by funext i; fin_cases i <;> rfl
        rw [hys]; exact Work.WilC5.S4Exp.negE_eq_neg hTE hadd _
      funMap_zero := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        rw [show ys = default from Subsingleton.elim _ _]
        exact hzeroR
      funMap_one := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        rw [show ys = default from Subsingleton.elim _ _]
        exact hone }
  letI : FirstOrder.Ring.CompatibleRing K := myCR
  letI hRX : WilkiesDesign.CG.rexpL.Structure K := Work.WilC5.lrcRexpReduct K
  letI hCT : (FirstOrder.Language.constantsOn ℝ).Structure K := Work.WilC5.lrcConstReduct K
  letI hLR : LRc.Structure K := LR.withConstantsStructure ℝ
  have hstruct : (Work.WilC5.reductStruct K : LRc.Structure K) =
      (inferInstance : LRc.Structure K) :=
    Work.WilC5.reductStruct_eq_withConstants (M := K)
  have hDclEq : ∀ A : Set K, @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) A =
      @Work.WilC2.Dcl K (inferInstance) A :=
    fun A => congrArg (fun i => @Work.WilC2.Dcl K i A) hstruct
  have hBdclC : @Work.WilC2.Dcl K (inferInstance) (B : Set K) ⊆ (B : Set K) := by
    intro z hz
    exact hBdcl (by rwa [← hDclEq] at hz)
  have hinvB : ∀ {b : K}, b ∈ (B : Set K) → b ≠ 0 → b⁻¹ ∈ (B : Set K) := by
    intro b hb hb0
    have hbD : b ∈ @Work.WilC2.Dcl K (inferInstance) (B : Set K) :=
      Work.WilC2.mem_dcl.mpr (Set.Definable.singleton_of_mem LRc hb)
    exact hBdclC (Work.WilC5.S4ExpF.dcl_inv_mem (B : Set K) hbD hb0)
  have hcInDcl : c ∈ @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ {c}) :=
    Work.WilC2.mem_dcl.mpr
      (Set.Definable.singleton_of_mem LRc (Set.mem_union_right _ (Set.mem_singleton c)))
  have hcnewinv : ∀ b : ↥B, ¬ Work.WilC5.SameArch (b : K) c⁻¹ := by
    intro b hb
    rcases eq_or_ne (b : K) 0 with hb0 | hb0
    · have hzero : (c⁻¹ : K) = 0 := by
        obtain ⟨N, h1, h2⟩ := hb
        exact abs_eq_zero.mp (le_antisymm (by simpa [hb0] using h2) (abs_nonneg _))
      exact hc0 (inv_eq_zero.mp hzero)
    · have hb' : Work.WilC5.SameArch ((b : K)⁻¹) c := by
        have h := Work.WilC5.SameArch_inv hb
        rwa [inv_inv] at h
      exact hcnew ⟨(b : K)⁻¹, hinvB b.2 hb0⟩ hb'
  by_cases hfin : Work.WilC5.IsFiniteVal c
  · -- ## Case 1: `c` finite; then it is infinitesimal (value-new ⟹ not a unit)
    have hsmall : ∀ N : ℕ, |c| < ((((N : ℕ)) : K) + 1)⁻¹ := by
      intro N
      rcases hfin with ⟨M, hM⟩
      by_contra hcon
      have h1 : ((((N : ℕ)) : K) + 1)⁻¹ ≤ |c| := le_of_not_gt hcon
      refine hnotunit ⟨max M N, ?_, ?_⟩
      · have hNle : (((N : ℕ)) : K) ≤ ((((max M N : ℕ))) : K) := Nat.cast_le.mpr (le_max_right M N)
        linarith [((inv_le_inv₀ (by positivity) (by positivity)).mpr (by linarith : (((N : ℕ)) : K) + 1 ≤ ((((max M N : ℕ))) : K) + 1)) ]
      · have hMle : (((M : ℕ)) : K) ≤ ((((max M N : ℕ))) : K) := Nat.cast_le.mpr (le_max_left M N)
        linarith
    have hcInvInf : ¬ Work.WilC5.IsFiniteVal (c⁻¹) := by
      intro h
      obtain ⟨L, hL⟩ := h
      have hcabs : 0 < |c| := abs_pos.mpr hc0
      have h3 : |c| < (((((L + 1 : ℕ)) : K)) + 1)⁻¹ := hsmall (L + 1)
      have h4 : ((((L : ℕ)) : K) + 1) + 1 = ((((L + 1 : ℕ)) : K)) + 1 := by push_cast; ring
      rw [← h4] at h3
      have h5 : ((((L : ℕ)) : K) + 1) + 1 < (|c|)⁻¹ :=
        (lt_inv_comm₀ (by positivity) hcabs).mpr h3
      rw [abs_inv] at hL
      linarith
    by_cases hcpos : 0 < c
    · refine ⟨c⁻¹, inv_pos.mpr hcpos, hcInvInf, ?_, ?_, ?_⟩
      · intro b hb
        exact hcnewinv b hb
      · rw [hDclEq]
        exact Work.WilC5.S4ExpF.dcl_inv_mem ((B : Set K) ∪ {c}) hcInDcl hc0
      · rw [hDclEq]
        have hx0D : c⁻¹ ∈ @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ {c⁻¹}) :=
          Work.WilC2.mem_dcl.mpr
            (Set.Definable.singleton_of_mem LRc (Set.mem_union_right _ (Set.mem_singleton c⁻¹)))
        have h := Work.WilC5.S4ExpF.dcl_inv_mem ((B : Set K) ∪ {c⁻¹}) hx0D (inv_ne_zero hc0)
        rwa [inv_inv] at h
    · have hclt : c < 0 := lt_of_le_of_ne (le_of_not_gt hcpos) hc0
      have hinvlt : c⁻¹ < 0 := by
        have h : (1 : K) / c < 0 := div_neg_of_pos_of_neg one_pos hclt
        rwa [one_div] at h
      refine ⟨-(c⁻¹), by linarith, ?_, ?_, ?_, ?_⟩
      · rw [ESSStep.isFiniteVal_neg_iff]
        exact hcInvInf
      · intro b hb
        rw [ESSStep.sameArch_neg_right] at hb
        exact hcnewinv b hb
      · rw [hDclEq]
        exact Work.WilC5.S4ExpF.dcl_neg_mem _
          (Work.WilC5.S4ExpF.dcl_inv_mem ((B : Set K) ∪ {c}) hcInDcl hc0)
      · rw [hDclEq]
        have hx0D : (-(c⁻¹)) ∈ @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ {-(c⁻¹)}) :=
          Work.WilC2.mem_dcl.mpr
            (Set.Definable.singleton_of_mem LRc (Set.mem_union_right _ (Set.mem_singleton (-(c⁻¹)))))
        have h1 : c⁻¹ ∈ @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ {-(c⁻¹)}) := by
          have h := Work.WilC5.S4ExpF.dcl_neg_mem _ hx0D
          rwa [neg_neg] at h
        have h2 : c ∈ @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ {-(c⁻¹)}) := by
          have h := Work.WilC5.S4ExpF.dcl_inv_mem ((B : Set K) ∪ {-(c⁻¹)}) h1 (inv_ne_zero hc0)
          rwa [inv_inv] at h
        exact h2
  · -- ## Case 2: `c` is infinite
    by_cases hcpos : 0 < c
    · refine ⟨c, hcpos, hfin, ?_, ?_, ?_⟩
      · intro b hb
        exact hcnew b hb
      · rw [hDclEq]; exact hcInDcl
      · rw [hDclEq]; exact hcInDcl
    · have hclt : c < 0 := lt_of_le_of_ne (le_of_not_gt hcpos) hc0
      refine ⟨-c, by linarith, ?_, ?_, ?_, ?_⟩
      · rw [ESSStep.isFiniteVal_neg_iff]
        exact hfin
      · intro b hb
        rw [ESSStep.sameArch_neg_right] at hb
        exact hcnew b hb
      · rw [hDclEq]
        exact Work.WilC5.S4ExpF.dcl_neg_mem _ hcInDcl
      · rw [hDclEq]
        have hx0D : (-c) ∈ @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ {-c}) :=
          Work.WilC2.mem_dcl.mpr
            (Set.Definable.singleton_of_mem LRc (Set.mem_union_right _ (Set.mem_singleton (-c))))
        have h := Work.WilC5.S4ExpF.dcl_neg_mem _ hx0D
        rwa [neg_neg] at h


end ESSStep

theorem ExistsStepSeq
    {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE]
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    (hOM : WilkiesDesign.CG.OMinModels) (hVI : WilkiesDesign.CG.ValIneq)
    (hVP : Work.WilC5.ValProp)
    (B : WilkiesDesign.CG.LRc.Substructure K)
    (hBdcl : @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) (B : Set K) ⊆ (B : Set K))
    (hBexp : ∀ x ∈ (B : Set K), Work.WilC5.expE x ∈ (B : Set K))
    (hvalnew : ∀ y : K, y ∉ (B : Set K) →
      ¬ (∀ w : K, w ∈ @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) ((B : Set K) ∪ {y}) →
          ∃ b : ↥B, Work.WilC5.SameArch (b : K) w))
    {x : K} (hx : x ∉ (B : Set K)) :
    ∃ S : Work.WilC5.StepSeq B, Work.WilC5.StepSeq.ValueNewAll S ∧
      Work.WilC5.StepSeq.Unbounded S ∧
      @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) ((B : Set K) ∪ {x}) =
        @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) ((B : Set K) ∪ {S.xs 0}) := by
  classical
  have hTE : K ⊨ WilkiesDesign.CG.TE := inferInstance
  -- ## 1. Facts at the `rexp`-reduct (no instance is shadowed here)
  have hTRRed : @Theory.Model LRc K (Work.WilC5.reductStruct K) TR :=
    Work.WilC5.reduct_model_TR K hTE
  have hzeroR : (Work.WilC5.zeroE : K) = 0 := Work.WilC5.S4Exp.zeroE_eq_zero hTE hadd
  have hmem0 : (0 : K) ∈ (B : Set K) := by
    have h := B.fun_mem (Work.WilC5.ringSymL Ring.zeroFunc) (fun i : Fin 0 => i.elim0)
      (fun i => i.elim0)
    have h' : (Work.WilC5.zeroE : K) ∈ (B : Set K) := h
    rwa [hzeroR] at h'
  -- ## 2. The one-step lemma
  have step_exists : ∀ y : K, 0 < y → (∀ b : ↥B, ¬ Work.WilC5.SameArch (b : K) y) →
      ∃ p : (↥B) × Bool × K,
        (0 < p.2.2 ∧ ∀ b : ↥B, ¬ Work.WilC5.SameArch (b : K) p.2.2) ∧
        ¬ Work.WilC5.IsFiniteVal p.2.2 ∧
        (if p.2.1 then Work.WilC5.logFun y = Work.WilC5.addE ((p.1 : K)) p.2.2
         else Work.WilC5.logFun y = Work.WilC5.subE ((p.1 : K)) p.2.2) := by
    intro y hypos hynew
    have hyle : Work.WilC5.leE Work.WilC5.zeroE y ∧ ¬ Work.WilC5.leE y Work.WilC5.zeroE :=
      (Work.WilC5.S4ExpF.leE_zero_iff hTE hadd hleneg y).mpr hypos
    have hzB : Work.WilC5.logFun y ∉ (B : Set K) := by
      intro hz
      have hexpy : Work.WilC5.expE (Work.WilC5.logFun y) = y :=
        Work.WilC5.expE_logFun_of_pos hTE hyle
      have hyB : y ∈ (B : Set K) := by
        rw [← hexpy]
        exact hBexp (Work.WilC5.logFun y) hz
      exact hynew ⟨y, hyB⟩ (Work.WilC5.SameArch_equiv.refl y)
    have hnew' : ∃ w : K, w ∈ @Work.WilC2.Dcl K (Work.WilC5.reductStruct K)
        ((B : Set K) ∪ {Work.WilC5.logFun y}) ∧
        ∀ b : ↥B, ¬ Work.WilC5.SameArch (b : K) w := by
      by_contra hc
      refine hvalnew (Work.WilC5.logFun y) hzB (fun w hw => ?_)
      by_contra hb
      exact hc ⟨w, hw, fun b hS => hb ⟨b, hS⟩⟩
    obtain ⟨a, haB, htnew⟩ :=
      Work.WilC5.ExistsStepSeqAux.TranslateNew hrexp hadd hmul hone hleneg hMCr hOM hVI hVP
        B hBdcl hnew'
    set t : K := Work.WilC5.logFun y - a with htdef
    have htnew' : ∀ b : ↥B, ¬ Work.WilC5.SameArch (b : K) t := htnew
    have ht0 : t ≠ 0 := by
      intro h
      exact htnew' ⟨0, hmem0⟩ (by rw [h]; exact ESSStep.sameArch_zero_zero)
    have htinf : ¬ Work.WilC5.IsFiniteVal t := by
      have hrel0 : Work.WilC5.logFun y = Work.WilC5.addE ((⟨a, haB⟩ : ↥B) : K) t := by
        rw [hadd]
        rw [show ((⟨a, haB⟩ : ↥B) : K) = a from rfl]
        rw [htdef]; ring
      exact Work.WilC5.ExistsStepSeqAux.InfOfLogRel hrexp hadd hmul hone hleneg B hBexp
        hypos hynew ht0 (Or.inl hrel0)
    by_cases htpos : 0 < t
    · refine ⟨(⟨a, haB⟩, true, t), ⟨⟨htpos, ?_⟩, htinf, ?_⟩⟩
      · intro b
        exact htnew' b
      · have hrel : Work.WilC5.logFun y = Work.WilC5.addE ((⟨a, haB⟩ : ↥B) : K) t := by
          rw [hadd, htdef]; ring
        simpa using hrel
    · have htlt : t < 0 := lt_of_le_of_ne (le_of_not_gt htpos) ht0
      refine ⟨(⟨a, haB⟩, false, -t), ⟨⟨by linarith, ?_⟩, ?_, ?_⟩⟩
      · intro b
        rw [ESSStep.sameArch_neg_right]
        exact htnew' b
      · rw [ESSStep.isFiniteVal_neg_iff]
        exact htinf
      · have hrel : Work.WilC5.logFun y = Work.WilC5.subE ((⟨a, haB⟩ : ↥B) : K) (-t) := by
          rw [Work.WilC5.S4ExpF.subE_eq_sub hTE hadd]
          rw [htdef]; ring
        simpa using hrel
  -- ## 3. The first translate and its normalisation
  have hnew_x : ∃ w : K, w ∈ @Work.WilC2.Dcl K (Work.WilC5.reductStruct K)
      ((B : Set K) ∪ {x}) ∧ ∀ b : ↥B, ¬ Work.WilC5.SameArch (b : K) w := by
    by_contra hc
    refine hvalnew x hx (fun w hw => ?_)
    by_contra hb
    exact hc ⟨w, hw, fun b hS => hb ⟨b, hS⟩⟩
  obtain ⟨a0, ha0B, hcnew⟩ :=
    Work.WilC5.ExistsStepSeqAux.TranslateNew hrexp hadd hmul hone hleneg hMCr hOM hVI hVP
      B hBdcl hnew_x
  set c : K := x - a0 with hcdef
  have hc0 : c ≠ 0 := by
    intro h
    exact hcnew ⟨0, hmem0⟩ (by rw [h]; exact ESSStep.sameArch_zero_zero)
  obtain ⟨x0, hx0pos, hx0inf, hx0new, hx0D, hcD⟩ :=
    ESSStep.ESSNormalizeNew hrexp hadd hmul hone hleneg B hBdcl hc0 hcnew
  -- ## 4. The recursive construction
  have stepFun_exists :
      ∃ sf : ((y : K) → (0 < y ∧ ∀ b : ↥B, ¬ Work.WilC5.SameArch (b : K) y) →
        (↥B) × Bool × K),
        ∀ (y : K) (hy : 0 < y ∧ ∀ b : ↥B, ¬ Work.WilC5.SameArch (b : K) y),
          (0 < (sf y hy).2.2 ∧ ∀ b : ↥B, ¬ Work.WilC5.SameArch (b : K) (sf y hy).2.2) ∧
          ¬ Work.WilC5.IsFiniteVal (sf y hy).2.2 ∧
          (if (sf y hy).2.1 then
              Work.WilC5.logFun y = Work.WilC5.addE (((sf y hy).1 : ↥B) : K) (sf y hy).2.2
           else Work.WilC5.logFun y = Work.WilC5.subE (((sf y hy).1 : ↥B) : K) (sf y hy).2.2) :=
    ⟨fun y hy => Classical.choose (step_exists y hy.1 hy.2),
     fun y hy => Classical.choose_spec (step_exists y hy.1 hy.2)⟩
  let stepFun : ((y : K) → (0 < y ∧ ∀ b : ↥B, ¬ Work.WilC5.SameArch (b : K) y) →
      (↥B) × Bool × K) := Classical.choose stepFun_exists
  have stepSpec : ∀ (y : K) (hy : 0 < y ∧ ∀ b : ↥B, ¬ Work.WilC5.SameArch (b : K) y),
      (0 < (stepFun y hy).2.2 ∧ ∀ b : ↥B, ¬ Work.WilC5.SameArch (b : K) (stepFun y hy).2.2) ∧
      ¬ Work.WilC5.IsFiniteVal (stepFun y hy).2.2 ∧
      (if (stepFun y hy).2.1 then
          Work.WilC5.logFun y = Work.WilC5.addE (((stepFun y hy).1 : ↥B) : K) (stepFun y hy).2.2
       else Work.WilC5.logFun y = Work.WilC5.subE (((stepFun y hy).1 : ↥B) : K) (stepFun y hy).2.2) :=
    Classical.choose_spec stepFun_exists
  let data : ℕ → { z : K // (0 < z ∧ ∀ b : ↥B, ¬ Work.WilC5.SameArch (b : K) z) ∧
      ¬ Work.WilC5.IsFiniteVal z } :=
    fun n => Nat.rec ⟨x0, ⟨hx0pos, hx0new⟩, hx0inf⟩
      (fun _ d => ⟨(stepFun d.1 d.2.1).2.2,
        ⟨(stepSpec d.1 d.2.1).1, (stepSpec d.1 d.2.1).2.1⟩⟩) n
  let xs : ℕ → K := fun n => (data n).1
  have hxspos : ∀ n, 0 < xs n := fun n => (data n).2.1.1
  have hxsnew : ∀ n, ∀ b : ↥B, ¬ Work.WilC5.SameArch (b : K) (xs n) := fun n => (data n).2.1.2
  have hxsinf : ∀ n, ¬ Work.WilC5.IsFiniteVal (xs n) := fun n => (data n).2.2
  let beta : ℕ → ↥B := fun n => (stepFun (xs n) (data n).2.1).1
  let pos : ℕ → Bool := fun n => (stepFun (xs n) (data n).2.1).2.1
  have hxs_succ : ∀ n, xs (n + 1) = (stepFun (xs n) (data n).2.1).2.2 := by
    intro n
    rfl
  have hrel : ∀ n, Work.WilC5.logFun (xs n) =
      (if pos n then Work.WilC5.addE ((beta n : ↥B) : K) (xs (n + 1))
       else Work.WilC5.subE ((beta n : ↥B) : K) (xs (n + 1))) := by
    intro n
    have h := (stepSpec (xs n) (data n).2.1).2.2
    have hc_eq : pos n = (stepFun (xs n) (data n).2.1).2.1 := rfl
    rw [hc_eq]
    by_cases hc : (stepFun (xs n) (data n).2.1).2.1 = true
    · rw [if_pos hc] at h ⊢
      exact h
    · rw [if_neg hc] at h ⊢
      exact h
  let S : Work.WilC5.StepSeq B :=
    { xs := xs
      beta := beta
      pos := pos
      hpos := fun n => (Work.WilC5.S4ExpF.leE_zero_iff hTE hadd hleneg (xs n)).mpr (hxspos n)
      hrel := hrel }
  -- ## 6. The canonical instance bundle (as in `StepSeqDecomp`)
  let myCR : FirstOrder.Ring.CompatibleRing K :=
    { toStructure := @Work.WilC5.lrcRingReduct K (Work.WilC5.instStructureLRcOfLEc K)
      funMap_add := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hys : ys = ![ys 0, ys 1] := by funext i; fin_cases i <;> rfl
        rw [hys]; exact hadd _ _
      funMap_mul := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hys : ys = ![ys 0, ys 1] := by funext i; fin_cases i <;> rfl
        rw [hys]; exact hmul _ _
      funMap_neg := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        have hys : ys = ![ys 0] := by funext i; fin_cases i <;> rfl
        rw [hys]; exact Work.WilC5.S4Exp.negE_eq_neg hTE hadd _
      funMap_zero := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        rw [show ys = default from Subsingleton.elim _ _]
        exact hzeroR
      funMap_one := fun ys => by
        rw [Work.WilC5.lrcRingReduct_funMap]
        rw [show ys = default from Subsingleton.elim _ _]
        exact hone }
  letI : FirstOrder.Ring.CompatibleRing K := myCR
  letI hRX : WilkiesDesign.CG.rexpL.Structure K := Work.WilC5.lrcRexpReduct K
  letI hCT : (FirstOrder.Language.constantsOn ℝ).Structure K := Work.WilC5.lrcConstReduct K
  letI hLR : LRc.Structure K := LR.withConstantsStructure ℝ
  have hstruct : (Work.WilC5.reductStruct K : LRc.Structure K) =
      (inferInstance : LRc.Structure K) :=
    Work.WilC5.reductStruct_eq_withConstants (M := K)
  have hDclEq : ∀ A : Set K, @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) A =
      @Work.WilC2.Dcl K (inferInstance) A :=
    fun A => congrArg (fun i => @Work.WilC2.Dcl K i A) hstruct
  have hTRCanon : @Theory.Model LRc K (inferInstance) TR := hstruct ▸ hTRRed
  haveI : @Theory.Model LRc K (inferInstance) TR := hTRCanon
  -- ## 5. The invariants
  have hVNA : Work.WilC5.StepSeq.ValueNewAll S := hxsnew
  have hUnb : Work.WilC5.StepSeq.Unbounded S := by
    intro n N
    have hxinf : ∀ M : ℕ, ((M : ℕ) : K) + 1 < |xs n| := by
      intro M
      have h : ¬ (|xs n| ≤ ((M : ℕ) : K) + 1) := fun hle => hxsinf n ⟨M, hle⟩
      exact lt_of_not_ge h
    have hlt : Work.WilC5.realConst K ((N : ℕ) : ℝ) < xs n := by
      have h1 : ((N : ℕ) : K) + 1 < |xs n| := hxinf N
      rw [abs_of_pos (hxspos n)] at h1
      rw [Work.WilC5.realConst_natCast (M := K) N]
      linarith
    exact ⟨(hleneg _ _).mpr (le_of_lt hlt), by rw [hleneg]; exact not_le.mpr hlt⟩
  -- ## 7. The equality of the definable closures
  have hInsertEq : ∀ {A : Set K} {u v : K},
      u ∈ @Work.WilC2.Dcl K (inferInstance) (A ∪ {v}) →
      v ∈ @Work.WilC2.Dcl K (inferInstance) (A ∪ {u}) →
      @Work.WilC2.Dcl K (inferInstance) (A ∪ {u}) =
        @Work.WilC2.Dcl K (inferInstance) (A ∪ {v}) := by
    intro A u v hu hv
    have hsub₁ : A ∪ {u} ⊆ @Work.WilC2.Dcl K (inferInstance) (A ∪ {v}) := by
      intro z hz
      rcases hz with hzA | hzu
      · exact Work.WilC2.mem_dcl.mpr
          (Set.Definable.singleton_of_mem LRc (Set.mem_union_left _ hzA))
      · rw [Set.mem_singleton_iff] at hzu
        rw [hzu]
        exact hu
    have hsub₂ : A ∪ {v} ⊆ @Work.WilC2.Dcl K (inferInstance) (A ∪ {u}) := by
      intro z hz
      rcases hz with hzA | hzv
      · exact Work.WilC2.mem_dcl.mpr
          (Set.Definable.singleton_of_mem LRc (Set.mem_union_left _ hzA))
      · rw [Set.mem_singleton_iff] at hzv
        rw [hzv]
        exact hv
    apply le_antisymm
    · calc @Work.WilC2.Dcl K (inferInstance) (A ∪ {u})
          ⊆ @Work.WilC2.Dcl K (inferInstance)
              (@Work.WilC2.Dcl K (inferInstance) (A ∪ {v})) :=
            Work.WilC2.dcl_mono hsub₁
        _ = @Work.WilC2.Dcl K (inferInstance) (A ∪ {v}) := Work.WilC2.dcl_idem _
    · calc @Work.WilC2.Dcl K (inferInstance) (A ∪ {v})
          ⊆ @Work.WilC2.Dcl K (inferInstance)
              (@Work.WilC2.Dcl K (inferInstance) (A ∪ {u})) :=
            Work.WilC2.dcl_mono hsub₂
        _ = @Work.WilC2.Dcl K (inferInstance) (A ∪ {u}) := Work.WilC2.dcl_idem _
  have hx0D' : x0 ∈ @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ {c}) := by
    rwa [hDclEq] at hx0D
  have hcD' : c ∈ @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ {x0}) := by
    rwa [hDclEq] at hcD
  have ha0D : a0 ∈ @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ {x}) :=
    Work.WilC2.mem_dcl.mpr (Set.Definable.singleton_of_mem LRc (Set.mem_union_left _ ha0B))
  have hxD : x ∈ @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ {x}) :=
    Work.WilC2.mem_dcl.mpr
      (Set.Definable.singleton_of_mem LRc (Set.mem_union_right _ (Set.mem_singleton x)))
  have hc_eq1 : c = x + (-a0) := by rw [hcdef, sub_eq_add_neg]
  have hcInDcl : c ∈ @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ {x}) := by
    have h1 : -a0 ∈ @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ {x}) :=
      Work.WilC5.S4ExpF.dcl_neg_mem _ ha0D
    have h2 : x + (-a0) ∈ @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ {x}) :=
      Work.WilC5.S4ExpF.dcl_add_mem _ hxD h1
    rw [← hc_eq1] at h2
    exact h2
  have hcx_eq : c + a0 = x := by rw [hcdef]; ring
  have hxInDcl : x ∈ @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ {c}) := by
    have hcSelf : c ∈ @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ {c}) :=
      Work.WilC2.mem_dcl.mpr
        (Set.Definable.singleton_of_mem LRc (Set.mem_union_right _ (Set.mem_singleton c)))
    have ha0D' : a0 ∈ @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ {c}) :=
      Work.WilC2.mem_dcl.mpr (Set.Definable.singleton_of_mem LRc (Set.mem_union_left _ ha0B))
    have h2 : c + a0 ∈ @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ {c}) :=
      Work.WilC5.S4ExpF.dcl_add_mem _ hcSelf ha0D'
    rwa [hcx_eq] at h2
  have hEq1 : @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ {x}) =
      @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ {c}) := hInsertEq hxInDcl hcInDcl
  have hEq2 : @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ {c}) =
      @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ {x0}) := hInsertEq hcD' hx0D'
  have hGoalC : @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ {x}) =
      @Work.WilC2.Dcl K (inferInstance) ((B : Set K) ∪ {x0}) := hEq1.trans hEq2
  have hfinal : @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) ((B : Set K) ∪ {x}) =
      @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) ((B : Set K) ∪ {x0}) := by
    rw [hDclEq ((B : Set K) ∪ {x}), hDclEq ((B : Set K) ∪ {x0}), hGoalC]
  exact ⟨S, hVNA, hUnb, hfinal⟩

end Work.WilC5
