import Mathlib
import Submission.Work.Thom.BundleIso_comap_exists
import Submission.Work.Thom.continuousOn_quoCLM
import Submission.Work.Thom.tautQuotientCore_iso
import Submission.Work.Thom.chernClass
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.NowhereZeroChart

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Data for the identification `(A ⊕ B)/ℂ(σ,0) ≅ (A/ℂσ) ⊕ B`

... 
-/

namespace Work.Whitney
namespace WB

open Work.TangentClasses Work.Thom

noncomputable section

variable {Y : Type} [TopologicalSpace Y]
variable {ι_A ι_B : Type} [Fintype ι_A] [Fintype ι_B]

/-- The Whitney sum `A ⊕ B` in the standard fibre, as in the main statement. -/
abbrev SumB (r s : ℕ) (A : VectorBundleCore ℂ Y (EuclideanSpace ℂ (Fin (r + 1))) ι_A)
    (B : VectorBundleCore ℂ Y (EuclideanSpace ℂ (Fin (s + 1))) ι_B) :
    VectorBundleCore ℂ Y (EuclideanSpace ℂ (Fin ((r + 1) + (s + 1)))) (ι_A × ι_B) :=
  whitneySum (m₁ := r + 1) (m₂ := s + 1) A B

/-! ## The standard-fibre linear algebra of the sum -/

/-- The inclusion `v ↦ (v,0)` of `A`'s fibre in the fibre of the sum. -/
def sumIncl {r s : ℕ} :
    EuclideanSpace ℂ (Fin (r + 1)) →L[ℂ] EuclideanSpace ℂ (Fin ((r + 1) + (s + 1))) :=
  ((sumFibreC (r + 1) (s + 1) : (EuclideanSpace ℂ (Fin (r + 1)) ×
      EuclideanSpace ℂ (Fin (s + 1))) →L[ℂ]
        EuclideanSpace ℂ (Fin ((r + 1) + (s + 1)))).comp
    (ContinuousLinearMap.inl ℂ (EuclideanSpace ℂ (Fin (r + 1)))
      (EuclideanSpace ℂ (Fin (s + 1)))))

theorem sumIncl_apply {r s : ℕ} (v : EuclideanSpace ℂ (Fin (r + 1))) :
    sumIncl (r := r) (s := s) v = sumFibreC (r + 1) (s + 1) (v, 0) := by
  rw [sumIncl, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  rfl

theorem sumIncl_injective {r s : ℕ} : Function.Injective (sumIncl (r := r) (s := s)) := by
  intro v w h
  have h2 : sumFibreC (r + 1) (s + 1) (v, 0) = sumFibreC (r + 1) (s + 1) (w, 0) := by
    simpa only [sumIncl_apply] using h
  exact (Prod.ext_iff.mp ((sumFibreC (r + 1) (s + 1)).injective h2)).1

theorem sumIncl_ne_zero {r s : ℕ} {v : EuclideanSpace ℂ (Fin (r + 1))} (hv : v ≠ 0) :
    sumIncl (r := r) (s := s) v ≠ 0 := fun h => hv (sumIncl_injective (by rw [h, map_zero]))

/-- Reassembling `ℂ^{r+1} × ℂ^{s+1}` into the fibre of the sum. -/
def joinSumCLM (r s : ℕ) :
    (EuclideanSpace ℂ (Fin (r + 1)) × EuclideanSpace ℂ (Fin (s + 1))) →L[ℂ]
      EuclideanSpace ℂ (Fin ((r + 1) + (s + 1))) :=
  (sumFibreC (r + 1) (s + 1) : _ →L[ℂ] _)

/-- Splitting the fibre of the sum into `ℂ^{r+1} × ℂ^{s+1}`. -/
def splitSumCLM (r s : ℕ) :
    EuclideanSpace ℂ (Fin ((r + 1) + (s + 1))) →L[ℂ]
      (EuclideanSpace ℂ (Fin (r + 1)) × EuclideanSpace ℂ (Fin (s + 1))) :=
  ((sumFibreC (r + 1) (s + 1)).symm : _ →L[ℂ] _)

theorem joinSumCLM_apply (r s : ℕ) (v : EuclideanSpace ℂ (Fin (r + 1)))
    (w : EuclideanSpace ℂ (Fin (s + 1))) :
    joinSumCLM r s (v, w) = sumFibreC (r + 1) (s + 1) (v, w) := rfl

theorem splitSumCLM_apply (r s : ℕ) (v : EuclideanSpace ℂ (Fin (r + 1)))
    (w : EuclideanSpace ℂ (Fin (s + 1))) :
    splitSumCLM r s (sumFibreC (r + 1) (s + 1) (v, w)) = (v, w) :=
  ContinuousLinearEquiv.symm_apply_apply _ _

theorem joinSumCLM_splitSumCLM (r s : ℕ)
    (z : EuclideanSpace ℂ (Fin ((r + 1) + (s + 1)))) :
    joinSumCLM r s (splitSumCLM r s z) = z :=
  ContinuousLinearEquiv.apply_symm_apply _ _

theorem splitSumCLM_injective (r s : ℕ) : Function.Injective (splitSumCLM r s) :=
  fun a b h => by
    have h2 := congrArg (joinSumCLM r s) h
    rwa [joinSumCLM_splitSumCLM, joinSumCLM_splitSumCLM] at h2

/-- Reassembling `ℂ^r × ℂ^{s+1}` into the fibre `ℂ^{r+(s+1)}`. -/
def joinQuotCLM (r s : ℕ) :
    (EuclideanSpace ℂ (Fin r) × EuclideanSpace ℂ (Fin (s + 1))) →L[ℂ]
      EuclideanSpace ℂ (Fin (r + (s + 1))) :=
  (sumFibreC r (s + 1) : _ →L[ℂ] _)

/-- Splitting `ℂ^{r+(s+1)}` into `ℂ^r × ℂ^{s+1}`. -/
def splitQuotCLM (r s : ℕ) :
    EuclideanSpace ℂ (Fin (r + (s + 1))) →L[ℂ]
      (EuclideanSpace ℂ (Fin r) × EuclideanSpace ℂ (Fin (s + 1))) :=
  ((sumFibreC r (s + 1)).symm : _ →L[ℂ] _)

theorem joinQuotCLM_apply (r s : ℕ) (v : EuclideanSpace ℂ (Fin r))
    (w : EuclideanSpace ℂ (Fin (s + 1))) :
    joinQuotCLM r s (v, w) = sumFibreC r (s + 1) (v, w) := rfl

theorem splitQuotCLM_apply (r s : ℕ) (v : EuclideanSpace ℂ (Fin r))
    (w : EuclideanSpace ℂ (Fin (s + 1))) :
    splitQuotCLM r s (sumFibreC r (s + 1) (v, w)) = (v, w) :=
  ContinuousLinearEquiv.symm_apply_apply _ _

theorem joinQuotCLM_splitQuotCLM (r s : ℕ) (z : EuclideanSpace ℂ (Fin (r + (s + 1)))) :
    joinQuotCLM r s (splitQuotCLM r s z) = z :=
  ContinuousLinearEquiv.apply_symm_apply _ _

theorem sumFibreC_splitSum (r s : ℕ) (z : EuclideanSpace ℂ (Fin ((r + 1) + (s + 1)))) :
    sumFibreC (r + 1) (s + 1) (splitSumCLM r s z) = z :=
  ContinuousLinearEquiv.apply_symm_apply _ _

theorem sumFibreC_splitQuot (r s : ℕ) (z : EuclideanSpace ℂ (Fin (r + (s + 1)))) :
    sumFibreC r (s + 1) (splitQuotCLM r s z) = z :=
  ContinuousLinearEquiv.apply_symm_apply _ _

theorem sumFibreC_apply_castAdd (r s : ℕ) (v : EuclideanSpace ℂ (Fin (r + 1)))
    (w : EuclideanSpace ℂ (Fin (s + 1))) (i : Fin (r + 1)) :
    (sumFibreC (r + 1) (s + 1) (v, w)) (Fin.castAdd (s + 1) i) = v i := by
  rw [Work.Whitney.sumFibreC]
  exact Work.Thom.finAddEquivProd_symm_apply_inl v w i

theorem sumFibreC_apply_natAdd (r s : ℕ) (v : EuclideanSpace ℂ (Fin (r + 1)))
    (w : EuclideanSpace ℂ (Fin (s + 1))) (j : Fin (s + 1)) :
    (sumFibreC (r + 1) (s + 1) (v, w)) (Fin.natAdd (r + 1) j) = w j := by
  rw [Work.Whitney.sumFibreC]
  exact Work.Thom.finAddEquivProd_symm_apply_inr v w j

theorem sumFibreC_apply_of_val_lt (r s : ℕ) (v : EuclideanSpace ℂ (Fin (r + 1)))
    (w : EuclideanSpace ℂ (Fin (s + 1))) (K : Fin ((r + 1) + (s + 1)))
    (hk : K.val < r + 1) :
    (sumFibreC (r + 1) (s + 1) (v, w)) K = v ⟨K.val, hk⟩ := by
  conv_lhs => rw [show K = Fin.castAdd (s + 1) ⟨K.val, hk⟩ from Fin.ext rfl]
  exact sumFibreC_apply_castAdd r s v w ⟨K.val, hk⟩

/-! ## Type abbreviations for the data of the problem -/

/-- Bundles in the standard fibre `ℂ^n`. -/
abbrev BunC (Y : Type) [TopologicalSpace Y] (n : ℕ) (ι : Type) : Type _ :=
  VectorBundleCore ℂ Y (EuclideanSpace ℂ (Fin n)) ι

/-- Continuous maps into the punctured total space of a bundle. -/
abbrev PunctC {n : ℕ} {ι : Type}
    (Z : VectorBundleCore ℂ Y (EuclideanSpace ℂ (Fin n)) ι) : Type _ :=
  C(Y, ↥(zeroComplement (realification Z)))

/-- The hypothesis that `σ` is a section of the projection. -/
def IsSec {n : ℕ} {ι : Type}
    (Z : VectorBundleCore ℂ Y (EuclideanSpace ℂ (Fin n)) ι) (σ : PunctC Z) : Prop :=
  ∀ y, (((σ y : ↥(zeroComplement (realification Z))) : (realification Z).TotalSpace)).1 = y

/-! ## The section `y ↦ (σ y, 0)` and the two bundles -/

/-- The fibre vector of `σ` at `y`, in the model fibre of `A`. -/
def secA (r : ℕ) (A : BunC Y (r + 1) ι_A) (σ : PunctC A) (y : Y) : EuclideanSpace ℂ (Fin (r + 1)) :=
  (((σ y : ↥(zeroComplement (realification A))) : (realification A).TotalSpace)).2

theorem secA_ne_zero (r : ℕ) (A : BunC Y (r + 1) ι_A) (σ : PunctC A) (y : Y) :
    secA r A σ y ≠ 0 := (σ y).2

/-- The section, as a point of the total space of `A`. -/
def secPoint (r : ℕ) (A : BunC Y (r + 1) ι_A) (σ : PunctC A) (y : Y) : A.TotalSpace :=
  ((σ y : ↥(zeroComplement (realification A))) : (realification A).TotalSpace)

theorem secPoint_fst (r : ℕ) (A : BunC Y (r + 1) ι_A) (σ : PunctC A) (hσ : IsSec A σ) (y : Y) :
    (secPoint r A σ y).1 = y := hσ y

theorem secPoint_snd (r : ℕ) (A : BunC Y (r + 1) ι_A) (σ : PunctC A) (y : Y) :
    (secPoint r A σ y).2 = secA r A σ y := rfl

/-- The chosen non-vanishing coordinate of the section of `A`. -/
def secIdx (r : ℕ) (A : BunC Y (r + 1) ι_A) (σ : PunctC A) (y : Y) : Fin (r + 1) :=
  tqCoord A (σ y)

theorem secA_secIdx_ne_zero (r : ℕ) (A : BunC Y (r + 1) ι_A) (σ : PunctC A) (hσ : IsSec A σ) (y : Y) :
    secA r A σ y (secIdx r A σ y) ≠ 0 := by
  have h := tqCoord_spec A (σ y)
  rw [localTriv_indexAt_snd A
    ((σ y : ↥(zeroComplement (realification A))) : (realification A).TotalSpace)] at h
  simpa only [secA, secIdx] using h

theorem whSum_coordChange_comp_sumIncl (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (i₂ : ι_A × ι_B) (y : Y) :
    ((SumB r s A B).coordChange ((SumB r s A B).indexAt y) i₂ y).comp
        (sumIncl (r := r) (s := s))
      = (sumIncl (r := r) (s := s)).comp (A.coordChange (A.indexAt y) i₂.1 y) := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [show (SumB r s A B).indexAt y = (A.indexAt y, B.indexAt y) from rfl,
    whitneySum_coordChange]
  simp only [ContinuousLinearMap.comp_apply, sumIncl_apply,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, map_zero]

/-- **The inclusion of `A` into the sum, as a map of total spaces, is continuous.** -/
theorem continuous_sumIncl_totalSpace (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) :
    Continuous (fun p : A.TotalSpace =>
      (⟨p.1, sumIncl (r := r) (s := s) p.2⟩ : (SumB r s A B).TotalSpace)) := by
  refine Work.Thom.continuous_totalSpaceMap_clm A (SumB r s A B) (ContinuousMap.id Y)
    (fun _ => sumIncl (r := r) (s := s)) ?_
  intro i₁ i₂
  have hsub : A.baseSet i₁ ∩ (SumB r s A B).baseSet i₂ ⊆ A.baseSet i₁ ∩ A.baseSet i₂.1 :=
    fun y hy => ⟨hy.1, by rw [whitneySum_baseSet (Z₁ := A) (Z₂ := B)] at hy; exact hy.2.1⟩
  have hcont : ContinuousOn (fun y : Y =>
      (sumIncl (r := r) (s := s)).comp (A.coordChange i₁ i₂.1 y))
      (A.baseSet i₁ ∩ (SumB r s A B).baseSet i₂) :=
    ContinuousOn.clm_comp continuousOn_const
      ((A.continuousOn_coordChange i₁ i₂.1).mono hsub)
  refine hcont.congr ?_
  intro y hy
  have hyA : y ∈ A.baseSet i₁ ∩ A.baseSet i₂.1 := hsub hy
  calc ((SumB r s A B).coordChange ((SumB r s A B).indexAt y) i₂ y).comp
          ((sumIncl (r := r) (s := s)).comp (A.coordChange i₁ (A.indexAt y) y))
      = (((SumB r s A B).coordChange ((SumB r s A B).indexAt y) i₂ y).comp
          (sumIncl (r := r) (s := s))).comp (A.coordChange i₁ (A.indexAt y) y) := by
        rw [ContinuousLinearMap.comp_assoc]
    _ = ((sumIncl (r := r) (s := s)).comp (A.coordChange (A.indexAt y) i₂.1 y)).comp
          (A.coordChange i₁ (A.indexAt y) y) := by
        rw [whSum_coordChange_comp_sumIncl]
    _ = (sumIncl (r := r) (s := s)).comp
          ((A.coordChange (A.indexAt y) i₂.1 y).comp (A.coordChange i₁ (A.indexAt y) y)) := by
        rw [ContinuousLinearMap.comp_assoc]
    _ = (sumIncl (r := r) (s := s)).comp (A.coordChange i₁ i₂.1 y) := by
        congr 1
        refine ContinuousLinearMap.ext fun v => ?_
        exact A.coordChange_comp i₁ (A.indexAt y) i₂.1 y
          ⟨⟨hyA.1, A.mem_baseSet_at y⟩, hyA.2⟩ v

/-- **The continuous nowhere-zero section `y ↦ (σ y, 0)` of `A ⊕ B`.** -/
def sumSection (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (hσ : IsSec A σ) : C(Y, ↥(zeroComplement (realification (SumB r s A B)))) where
  toFun y :=
    ⟨⟨y, sumIncl (r := r) (s := s) (secA r A σ y)⟩, by
      rw [mem_zeroComplement_mk]
      exact sumIncl_ne_zero (secA_ne_zero r A σ y)⟩
  continuous_toFun := by
    have hσc : Continuous (fun y : Y =>
        ((σ y : ↥(zeroComplement (realification A))) : (realification A).TotalSpace)) :=
      continuous_subtype_val.comp σ.continuous
    have hσA : Continuous (fun y : Y => secPoint r A σ y) :=
      (continuous_id_realification_symm A).comp hσc
    have h1 : Continuous (fun y : Y =>
        (⟨(secPoint r A σ y).1, sumIncl (r := r) (s := s) (secPoint r A σ y).2⟩ :
          (SumB r s A B).TotalSpace)) :=
      (continuous_sumIncl_totalSpace r s A B).comp hσA
    have h2 : Continuous (fun y : Y =>
        (⟨y, sumIncl (r := r) (s := s) (secA r A σ y)⟩ : (SumB r s A B).TotalSpace)) := by
      refine h1.congr ?_
      intro y
      rw [secPoint_fst r A σ hσ y, secPoint_snd]
    exact Continuous.subtype_mk
      ((continuous_id_realification (SumB r s A B)).comp h2) _

theorem sumSection_proj (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (hσ : IsSec A σ) (y : Y) :
    (((sumSection r s A B σ hσ y : ↥(zeroComplement (realification (SumB r s A B)))) :
      (realification (SumB r s A B)).TotalSpace)).1 = y := rfl

/-- The fibre vector of the section `(σ,0)` at `y`. -/
def aFull (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (hσ : IsSec A σ) (y : Y) : EuclideanSpace ℂ (Fin ((r + 1) + (s + 1))) :=
  (((sumSection r s A B σ hσ y : ↥(zeroComplement (realification (SumB r s A B)))) :
    (realification (SumB r s A B)).TotalSpace)).2

theorem aFull_apply (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (hσ : IsSec A σ) (y : Y) :
    aFull r s A B σ hσ y = sumIncl (r := r) (s := s) (secA r A σ y) := rfl

theorem aFull_eq_join (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (hσ : IsSec A σ) (y : Y) :
    aFull r s A B σ hσ y = joinSumCLM r s (secA r A σ y, 0) := rfl

theorem sumFibreC_secA_zero (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (hσ : IsSec A σ) (y : Y) :
    sumFibreC (r + 1) (s + 1) (secA r A σ y, 0) = aFull r s A B σ hσ y := by
  rw [aFull_apply, sumIncl_apply]

theorem joinSumCLM_secA_zero (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B)
    (σ : PunctC A) (hσ : IsSec A σ) (y : Y) :
    joinSumCLM r s (secA r A σ y, 0) = aFull r s A B σ hσ y :=
  sumFibreC_secA_zero r s A B σ hσ y

/-- The chosen non-vanishing coordinate of the section of the sum. -/
def idxSum (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (hσ : IsSec A σ) (y : Y) : Fin ((r + 1) + (s + 1)) :=
  tqCoord (SumB r s A B) (sumSection r s A B σ hσ y)

theorem idxSum_spec (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (hσ : IsSec A σ) (y : Y) : aFull r s A B σ hσ y (idxSum r s A B σ hσ y) ≠ 0 := by
  have h := tqCoord_spec (SumB r s A B) (sumSection r s A B σ hσ y)
  rw [localTriv_indexAt_snd (SumB r s A B)
    (((sumSection r s A B σ hσ y) : ↥(zeroComplement (realification (SumB r s A B)))) :
      (realification (SumB r s A B)).TotalSpace)] at h
  simpa only [aFull, idxSum] using h

/-- The index of the section is in the `A`-block. -/
theorem idxSum_val_lt (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (hσ : IsSec A σ) (y : Y) : (idxSum r s A B σ hσ y).val < r + 1 := by
  by_contra h
  push_neg at h
  have hspec := idxSum_spec r s A B σ hσ y
  rw [aFull_apply, sumIncl_apply] at hspec
  have hK : idxSum r s A B σ hσ y
      = Fin.natAdd (r + 1) ⟨(idxSum r s A B σ hσ y).val - (r + 1), by omega⟩ :=
    Fin.ext (by simp only [Fin.val_natAdd]; omega)
  rw [hK, sumFibreC_apply_natAdd] at hspec
  simpa using hspec

/-- The `A`-coordinate of the index of the section. -/
def kSum (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (hσ : IsSec A σ) (y : Y) : Fin (r + 1) :=
  ⟨(idxSum r s A B σ hσ y).val, idxSum_val_lt r s A B σ hσ y⟩

theorem kSum_castAdd (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (hσ : IsSec A σ) (y : Y) :
    Fin.castAdd (s + 1) (kSum r s A B σ hσ y) = idxSum r s A B σ hσ y := Fin.ext rfl

theorem aFull_apply_kSum (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A)
    (hσ : IsSec A σ) (y : Y) :
    aFull r s A B σ hσ y (idxSum r s A B σ hσ y) = secA r A σ y (kSum r s A B σ hσ y) := by
  rw [aFull_apply, sumIncl_apply, sumFibreC_apply_of_val_lt r s (secA r A σ y) 0
    (idxSum r s A B σ hσ y) (idxSum_val_lt r s A B σ hσ y)]
  rfl

/-! ## The two bundles -/

/-- The left-hand side: the pullback of the tautological quotient of the sum along the section. -/
abbrev Xb (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A) (hσ : IsSec A σ) :
    VectorBundleCore ℂ Y (EuclideanSpace ℂ (Fin ((r + 1) + s)))
      ((ι_A × ι_B) × Fin ((r + 1) + (s + 1))) :=
  bundleComap (tautQuotient (m := (r + 1) + s) (SumB r s A B)) (sumSection r s A B σ hσ)

/-- The right-hand side: the sum of the pullback of the tautological quotient of `A` and `B`. -/
abbrev Wb (r s : ℕ) (A : BunC Y (r + 1) ι_A) (B : BunC Y (s + 1) ι_B) (σ : PunctC A) :
    VectorBundleCore ℂ Y (EuclideanSpace ℂ (Fin (r + (s + 1))))
      ((ι_A × Fin (r + 1)) × ι_B) :=
  whitneySum (m₁ := r) (m₂ := s + 1) (bundleComap (tautQuotient (m := r) A) σ) B

end

end WB
end Work.Whitney
