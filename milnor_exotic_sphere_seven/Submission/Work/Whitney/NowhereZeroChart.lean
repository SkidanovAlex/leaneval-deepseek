import Mathlib
import Submission.Work.Whitney.NowhereZeroDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open Work.TangentClasses Work.Thom

namespace Work.Whitney
namespace NZ

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}
variable {V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι}
variable {σ : C(B, ↥(zeroComplement (realification V)))}

/-! ## The direct sum with the trivial line -/

theorem W_indexAt {ι₀ : Type} [Inhabited ι₀] (b : B) :
    (W (ι₀ := ι₀) V σ).indexAt b = ((Q V σ).indexAt b, default) := by
  rw [W, whitneySum_indexAt]
  rfl

theorem W_baseSet {ι₀ : Type} [Inhabited ι₀] (a : ι × Fin (m+1)) (j : ι₀) :
    (W (ι₀ := ι₀) V σ).baseSet (a, j) = (Q V σ).baseSet a := by
  rw [W, whitneySum_baseSet]
  exact Set.inter_univ _

theorem W_coordChange_apply {ι₀ : Type} [Inhabited ι₀] (b : B) (a : ι × Fin (m+1)) (j : ι₀)
    (u : EuclideanSpace ℂ (Fin (m+1))) :
    (W (ι₀ := ι₀) V σ).coordChange ((W (ι₀ := ι₀) V σ).indexAt b) (a, j) b u
      = sumFibreC m 1 ((Q V σ).coordChange ((Q V σ).indexAt b) a b (fstC m u), sndC m u) := by
  rw [W_indexAt (V := V) (σ := σ) b]
  rw [W, whitneySum_coordChange]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.coe_prodMap', trivialVectorBundleCore]
  rw [show (sumFibreC m 1).symm u = (fstC m u, sndC m u) from rfl]
  simp only [Prod.map_apply, ContinuousLinearMap.id_apply]

/-! ## The index and transition functions of `Q` -/

theorem Q_mem_baseSet (hσ : IsSection σ) (a : ι × Fin (m+1)) (b : B)
    (hb : b ∈ (Q V σ).baseSet a) :
    b ∈ V.baseSet a.1 ∧ (zCoord a.1 (σ b)) a.2 ≠ 0 := by
  rw [Q, bundleComap_baseSet] at hb
  rw [tautQuotient_baseSet] at hb
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hb
  refine ⟨?_, ?_⟩
  · simpa only [show ((σ b : ↥(zeroComplement (realification V))) :
        (realification V).TotalSpace).proj = b from hσ b] using hb.1
  · simpa only [zCoord] using hb.2

theorem Q_coordChange_apply' (hσ : IsSection σ) (a : ι × Fin (m+1)) (b : B)
    (z : EuclideanSpace ℂ (Fin m)) :
    (Q V σ).coordChange ((Q V σ).indexAt b) a b z
      = quoFun a.2 (zCoord a.1 (σ b))
          (V.coordChange (V.indexAt b) a.1 b (fillFun (secIdx V σ b) z)) := by
  rw [Q, bundleComap_coordChange, bundleComap_indexAt, tautQuotient_indexAt_eq]
  rw [show ((σ b : ↥(zeroComplement (realification V))) :
      (realification V).TotalSpace).proj = b from hσ b]
  rw [tautQuotient_coordChange]
  rw [show ((σ b : ↥(zeroComplement (realification V))) :
      (realification V).TotalSpace).proj = b from hσ b]
  rfl

theorem Q_coordChange_qCLM (hσ : IsSection σ) (a : ι × Fin (m+1)) (b : B)
    (hb : b ∈ (Q V σ).baseSet a) (w : EuclideanSpace ℂ (Fin (m+1))) :
    (Q V σ).coordChange ((Q V σ).indexAt b) a b (quoFun (secIdx V σ b) (secVec V σ b) w)
      = quoFun a.2 (zCoord a.1 (σ b)) (V.coordChange (V.indexAt b) a.1 b w) := by
  rw [Q_coordChange_apply' hσ a b]
  obtain ⟨-, hb'⟩ := Q_mem_baseSet hσ a b hb
  have hv : secVec V σ b (secIdx V σ b) ≠ 0 := secVec_secIdx_ne_zero hσ b
  rw [fillFun_quoFun (secIdx V σ b) (secVec V σ b) w hv, map_sub, map_smul,
    show V.coordChange (V.indexAt b) a.1 b (secVec V σ b) = zCoord a.1 (σ b) from
      (localTriv_secVec hσ a.1 b).symm]
  exact quoFun_sub_smul_self a.2 (zCoord a.1 (σ b)) (V.coordChange (V.indexAt b) a.1 b w)
    _ hb'

/-! ## Continuity of the local data -/

theorem coordChange_indexAt_comp (b : B) (i j : ι) (hb1 : b ∈ V.baseSet i)
    (hb2 : b ∈ V.baseSet j) (w : EuclideanSpace ℂ (Fin (m+1))) :
    V.coordChange (V.indexAt b) j b (V.coordChange i (V.indexAt b) b w)
      = V.coordChange i j b w :=
  V.coordChange_comp i (V.indexAt b) j b ⟨⟨hb1, V.mem_baseSet_at b⟩, hb2⟩ w

theorem continuousOn_localTriv_snd_sec (hσ : IsSection σ) (j : ι) :
    ContinuousOn (fun b : B => ((realification V).localTriv j
      ((σ b : ↥(zeroComplement (realification V))) : (realification V).TotalSpace)).2)
      (V.baseSet j) := by
  have h1 : ContinuousOn (fun b : B => (realification V).localTriv j
      ((σ b : ↥(zeroComplement (realification V))) : (realification V).TotalSpace))
      (V.baseSet j) := by
    refine ((realification V).localTriv j).continuousOn.comp
      (continuous_subtype_val.comp σ.continuous).continuousOn ?_
    intro b hb
    rw [VectorBundleCore.mem_localTriv_source, realification_baseSet,
      show ((σ b : ↥(zeroComplement (realification V))) :
        (realification V).TotalSpace).proj = b from hσ b]
    exact hb
  exact h1.snd

theorem continuousOn_zCoord_sec (hσ : IsSection σ) (j : ι) :
    ContinuousOn (fun b : B => zCoord j (σ b)) (V.baseSet j) := by
  refine (continuousOn_localTriv_snd_sec (V := V) (σ := σ) hσ j).congr ?_
  intro b hb
  dsimp only
  rw [zCoord]
  exact (localTriv_snd_eq V j _).symm


/-! ## The chart expression of the forward map -/

section Hom

variable (ℓ : B → (EuclideanSpace ℂ (Fin (m+1)) →L[ℂ] ℂ))

theorem sndC_homCLM (b : B) (w : EuclideanSpace ℂ (Fin (m+1))) :
    sndC m (homCLM V σ ℓ b w) = (ℓ b w) • basisVec (0 : Fin 1) := by
  rw [homCLM_apply, sndC_sumFibreC]

theorem W_mem_baseSet_left {ι₀ : Type} [Inhabited ι₀] (hσ : IsSection σ)
    (a : ι × Fin (m+1)) (j : ι₀) (b : B) (hb : b ∈ (W (ι₀ := ι₀) V σ).baseSet (a, j)) :
    b ∈ V.baseSet a.1 := by
  rw [W_baseSet] at hb
  exact (Q_mem_baseSet hσ a b hb).1

theorem hom_chart_eq (hσ : IsSection σ) (hℓ : ∀ b, ℓ b (secVec V σ b) = 1)
    {ι₀ : Type} [Inhabited ι₀] (i₁ : ι) (a : ι × Fin (m+1)) (j : ι₀) (b : B)
    (hb : b ∈ V.baseSet i₁ ∩ (W (ι₀ := ι₀) V σ).baseSet (a, j))
    (w : EuclideanSpace ℂ (Fin (m+1))) :
    (W (ι₀ := ι₀) V σ).coordChange ((W (ι₀ := ι₀) V σ).indexAt b) (a, j) b
        (homCLM V σ ℓ b (V.coordChange i₁ (V.indexAt b) b w))
      = sumFibreC m 1 (quoFun a.2 (zCoord a.1 (σ b)) (V.coordChange i₁ a.1 b w),
          (ℓ b (V.coordChange i₁ (V.indexAt b) b w)) • basisVec (0 : Fin 1)) := by
  have hbQ : b ∈ (Q V σ).baseSet a := by
    rw [← W_baseSet (V := V) (σ := σ) a j]; exact hb.2
  rw [W_coordChange_apply, fstC_homCLM, sndC_homCLM, Q_coordChange_qCLM hσ a b hbQ,
    coordChange_indexAt_comp b i₁ a.1 hb.1 (Q_mem_baseSet hσ a b hbQ).1]

/-- The "nice" form of the chart expression of the forward map, on the relevant set. -/
noncomputable def homNice (i₁ : ι) (a : ι × Fin (m+1)) (b : B) :
    EuclideanSpace ℂ (Fin (m+1)) →L[ℂ] EuclideanSpace ℂ (Fin (m+1)) :=
  ((sumFibreC m 1 : (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)) →L[ℂ]
      EuclideanSpace ℂ (Fin (m+1)))).comp
    (((quoCLM a.2 (zCoord a.1 (σ b))).comp (V.coordChange i₁ a.1 b)).prod
      (((ℓ b).comp (V.coordChange i₁ (V.indexAt b) b)).smulRight (basisVec (0 : Fin 1))))

theorem hom_chart_clm_eq (hσ : IsSection σ) (hℓ : ∀ b, ℓ b (secVec V σ b) = 1)
    {ι₀ : Type} [Inhabited ι₀] (i₁ : ι) (a : ι × Fin (m+1)) (j : ι₀) (b : B)
    (hb : b ∈ V.baseSet i₁ ∩ (W (ι₀ := ι₀) V σ).baseSet (a, j)) :
    ((W (ι₀ := ι₀) V σ).coordChange ((W (ι₀ := ι₀) V σ).indexAt b) (a, j) b).comp
        ((homCLM V σ ℓ b).comp (V.coordChange i₁ (V.indexAt b) b))
      = homNice (V := V) (σ := σ) (ℓ := ℓ) i₁ a b := by
  refine ContinuousLinearMap.ext fun w => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    hom_chart_eq ℓ hσ hℓ i₁ a j b hb w]
  simp only [homNice, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    quoCLM_apply, ContinuousLinearMap.smulRight_apply]
  rfl

end Hom


/-! ## Continuity of the forward chart expression -/

theorem continuousOn_quoFun_pair (l : Fin (m+1)) :
    ContinuousOn (fun p : EuclideanSpace ℂ (Fin (m+1)) × EuclideanSpace ℂ (Fin (m+1)) =>
      quoFun l p.1 p.2) ({Y | Y l ≠ 0} ×ˢ Set.univ) := by
  have hfun : (fun p : EuclideanSpace ℂ (Fin (m+1)) × EuclideanSpace ℂ (Fin (m+1)) =>
        quoFun l p.1 p.2)
      = fun p => dropCLM l p.2 - (evalCLM l p.2) •
          ((evalCLM l p.1)⁻¹ • dropCLM l p.1) := by
    funext p
    rw [show quoFun l p.1 p.2 = (quoCLM l p.1) p.2 from (quoCLM_apply l p.1 p.2).symm,
      quoCLM_eq l p.1]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply,
      evalCLM_apply, dropFun]
    rfl
  rw [hfun]
  refine ContinuousOn.sub ?_ ?_
  · exact ((dropCLM l).continuous.comp continuous_snd).continuousOn
  · have h1 : ContinuousOn (fun p : EuclideanSpace ℂ (Fin (m+1)) × EuclideanSpace ℂ (Fin (m+1)) =>
          (evalCLM l p.1)⁻¹) ({Y | Y l ≠ 0} ×ˢ Set.univ) :=
      ContinuousOn.inv₀ ((evalCLM l).continuous.comp continuous_fst).continuousOn
        (fun p hp => hp.1)
    have h2 : ContinuousOn (fun p : EuclideanSpace ℂ (Fin (m+1)) × EuclideanSpace ℂ (Fin (m+1)) =>
          dropCLM l p.1) ({Y | Y l ≠ 0} ×ˢ Set.univ) :=
      ((dropCLM l).continuous.comp continuous_fst).continuousOn
    have h3 : ContinuousOn (fun p : EuclideanSpace ℂ (Fin (m+1)) × EuclideanSpace ℂ (Fin (m+1)) =>
          (evalCLM l p.1)⁻¹ • dropCLM l p.1) ({Y | Y l ≠ 0} ×ˢ Set.univ) := h1.smul h2
    exact (ContinuousOn.smul ((evalCLM l).continuous.comp continuous_snd).continuousOn h3)

theorem continuousOn_clm_of_continuous_eval {X : Type} [TopologicalSpace X] {s : Set X}
    {D : X → EuclideanSpace ℂ (Fin (m+1)) →L[ℂ] EuclideanSpace ℂ (Fin (m+1))}
    (h : Continuous fun p : ↥s × EuclideanSpace ℂ (Fin (m+1)) => D p.1.1 p.2) :
    ContinuousOn D s := by
  rw [continuousOn_iff_continuous_domRestrict]
  rw [show s.domRestrict D = fun b : ↥s => D b.1 from rfl]
  exact continuous_clm_of_continuous_apply_gen (D := fun b : ↥s => D b.1) h

section HomCont

variable (ℓ : B → (EuclideanSpace ℂ (Fin (m+1)) →L[ℂ] ℂ))

theorem continuousOn_homNice (hσ : IsSection σ)
    (hℓ : ∀ i : ι, ContinuousOn (fun b : B => (ℓ b).comp (V.coordChange i (V.indexAt b) b))
      (V.baseSet i))
    {ι₀ : Type} [Inhabited ι₀] (i₁ : ι) (a : ι × Fin (m+1)) (j : ι₀) :
    ContinuousOn (homNice (V := V) (σ := σ) ℓ i₁ a)
      (V.baseSet i₁ ∩ (W (ι₀ := ι₀) V σ).baseSet (a, j)) := by
  set S : Set B := V.baseSet i₁ ∩ (W (ι₀ := ι₀) V σ).baseSet (a, j) with hS
  have hbQ : ∀ b ∈ S, b ∈ (Q V σ).baseSet a := by
    intro b hb
    rw [← W_baseSet (V := V) (σ := σ) a j]
    exact hb.2
  have hSb : ∀ b ∈ S, b ∈ V.baseSet a.1 := fun b hb => (Q_mem_baseSet hσ a b (hbQ b hb)).1
  have hbc : ∀ b ∈ S, (zCoord a.1 (σ b)) a.2 ≠ 0 :=
    fun b hb => (Q_mem_baseSet hσ a b (hbQ b hb)).2
  have hproj : Continuous (fun p : ↥S × EuclideanSpace ℂ (Fin (m+1)) => (p.1 : B)) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous (fun p : ↥S × EuclideanSpace ℂ (Fin (m+1)) => zCoord a.1 (σ p.1.1)) :=
    (continuousOn_zCoord_sec hσ a.1).comp_continuous hproj (fun p => hSb p.1 p.1.2)
  have hA : Continuous (fun p : ↥S × EuclideanSpace ℂ (Fin (m+1)) =>
      V.coordChange i₁ a.1 p.1.1 p.2) :=
    ((V.continuousOn_coordChange i₁ a.1).comp_continuous hproj
      (fun p => ⟨p.1.2.1, hSb p.1 p.1.2⟩)).clm_apply continuous_snd
  have hLclm : Continuous (fun p : ↥S × EuclideanSpace ℂ (Fin (m+1)) =>
      (ℓ p.1.1).comp (V.coordChange i₁ (V.indexAt p.1.1) p.1.1)) :=
    (hℓ i₁).comp_continuous hproj (fun p => p.1.2.1)
  have hL : Continuous (fun p : ↥S × EuclideanSpace ℂ (Fin (m+1)) =>
      ℓ p.1.1 (V.coordChange i₁ (V.indexAt p.1.1) p.1.1 p.2)) :=
    hLclm.clm_apply continuous_snd
  have hq : Continuous (fun p : ↥S × EuclideanSpace ℂ (Fin (m+1)) =>
      quoFun a.2 (zCoord a.1 (σ p.1.1)) (V.coordChange i₁ a.1 p.1.1 p.2)) :=
    (continuousOn_quoFun_pair (m := m) a.2).comp_continuous (hz.prodMk hA)
      (fun p => ⟨hbc p.1 p.1.2, Set.mem_univ _⟩)
  have hLb' : Continuous (fun p : ↥S × EuclideanSpace ℂ (Fin (m+1)) =>
      (ContinuousLinearMap.id ℂ ℂ).smulRight (basisVec (0 : Fin 1))
        (ℓ p.1.1 (V.coordChange i₁ (V.indexAt p.1.1) p.1.1 p.2))) :=
    ((ContinuousLinearMap.id ℂ ℂ).smulRight (basisVec (0 : Fin 1))).continuous.comp hL
  have hLb : Continuous (fun p : ↥S × EuclideanSpace ℂ (Fin (m+1)) =>
      (ℓ p.1.1 (V.coordChange i₁ (V.indexAt p.1.1) p.1.1 p.2)) • basisVec (0 : Fin 1)) := by
    refine hLb'.congr (fun p => ?_)
    simp [ContinuousLinearMap.smulRight_apply]
  refine (continuousOn_clm_of_continuous_eval (s := S) ?_)
  refine (((sumFibreC m 1 : (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin 1)) →L[ℂ]
      EuclideanSpace ℂ (Fin (m+1))).continuous.comp (hq.prodMk hLb))).congr ?_
  intro p
  simp only [homNice, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    quoCLM_apply, ContinuousLinearMap.smulRight_apply, Function.comp_apply]

end HomCont


theorem W_coordChange_apply' {ι₀ : Type} [Inhabited ι₀] (b : B) (a : ι × Fin (m+1)) (j : ι₀)
    (u : EuclideanSpace ℂ (Fin (m+1))) :
    (W (ι₀ := ι₀) V σ).coordChange (a, j) ((W (ι₀ := ι₀) V σ).indexAt b) b u
      = sumFibreC m 1 ((Q V σ).coordChange a ((Q V σ).indexAt b) b (fstC m u), sndC m u) := by
  rw [W_indexAt (V := V) (σ := σ) b]
  rw [W, whitneySum_coordChange]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.coe_prodMap', trivialVectorBundleCore]
  rw [show (sumFibreC m 1).symm u = (fstC m u, sndC m u) from rfl]
  simp only [Prod.map_apply, ContinuousLinearMap.id_apply]

section Inv

variable {ι₀ : Type} [Inhabited ι₀]
variable (ℓ : B → (EuclideanSpace ℂ (Fin (m+1)) →L[ℂ] ℂ))

/-- The "nice" form of the chart expression of the backward map. -/
noncomputable def invNice (i₁ : (ι × Fin (m+1)) × ι₀) (i₂ : ι) (b : B) :
    EuclideanSpace ℂ (Fin (m+1)) →L[ℂ] EuclideanSpace ℂ (Fin (m+1)) :=
  (V.coordChange i₁.1.1 i₂ b).comp ((fillCLM i₁.1.2).comp (fstC m))
    - (((((ℓ b).comp (V.coordChange i₁.1.1 (V.indexAt b) b)).comp
        (fillCLM i₁.1.2)).comp (fstC m)).smulRight (zCoord i₂ (σ b)))
    + ((scalarC m).smulRight (zCoord i₂ (σ b)))

theorem inv_chart_eq (hσ : IsSection σ) (hℓ : ∀ b, ℓ b (secVec V σ b) = 1)
    {ι₀ : Type} [Inhabited ι₀] (i₁ : (ι × Fin (m+1)) × ι₀) (i₂ : ι) (b : B)
    (hb : b ∈ (W (ι₀ := ι₀) V σ).baseSet i₁ ∩ V.baseSet i₂)
    (u : EuclideanSpace ℂ (Fin (m+1))) :
    V.coordChange (V.indexAt b) i₂ b
        (invCLM V σ ℓ b ((W (ι₀ := ι₀) V σ).coordChange i₁
          ((W (ι₀ := ι₀) V σ).indexAt b) b u))
      = V.coordChange i₁.1.1 i₂ b (fillFun i₁.1.2 (fstC m u))
        - (ℓ b (V.coordChange i₁.1.1 (V.indexAt b) b (fillFun i₁.1.2 (fstC m u))))
            • zCoord i₂ (σ b)
        + (scalarC m u) • zCoord i₂ (σ b) := by
  have hbQ : b ∈ (Q V σ).baseSet i₁.1 := by
    rw [← W_baseSet (V := V) (σ := σ) i₁.1 i₁.2]; exact hb.1
  have hb1 : b ∈ V.baseSet i₁.1.1 := (Q_mem_baseSet hσ i₁.1 b hbQ).1
  have hv : secVec V σ b (secIdx V σ b) ≠ 0 := secVec_secIdx_ne_zero hσ b
  have hWc : (W (ι₀ := ι₀) V σ).coordChange i₁ ((W (ι₀ := ι₀) V σ).indexAt b) b u
      = sumFibreC m 1 (quoFun (secIdx V σ b) (secVec V σ b)
          (V.coordChange i₁.1.1 (V.indexAt b) b (fillFun i₁.1.2 (fstC m u))), sndC m u) := by
    rw [W_coordChange_apply' (V := V) (σ := σ) b i₁.1 i₁.2 u,
      Q_coordChange_apply hσ i₁.1 b (fstC m u)]
  have hcv : V.coordChange (V.indexAt b) i₂ b (secVec V σ b) = zCoord i₂ (σ b) :=
    (localTriv_secVec hσ i₂ b).symm
  have hcomp : ∀ z : EuclideanSpace ℂ (Fin (m+1)),
      V.coordChange (V.indexAt b) i₂ b (V.coordChange i₁.1.1 (V.indexAt b) b z)
        = V.coordChange i₁.1.1 i₂ b z := fun z =>
    coordChange_indexAt_comp (V := V) b i₁.1.1 i₂ hb1 hb.2 z
  rw [hWc, invCLM_apply, fstC_sumFibreC, scalarC_sumFibreC]
  have hlift : fillFun (secIdx V σ b)
      (quoFun (secIdx V σ b) (secVec V σ b)
        (V.coordChange i₁.1.1 (V.indexAt b) b (fillFun i₁.1.2 (fstC m u))))
      = V.coordChange i₁.1.1 (V.indexAt b) b (fillFun i₁.1.2 (fstC m u))
        - ((V.coordChange i₁.1.1 (V.indexAt b) b (fillFun i₁.1.2 (fstC m u))) (secIdx V σ b)
            / secVec V σ b (secIdx V σ b)) • secVec V σ b :=
    fillFun_quoFun _ _ _ hv
  have hell : ℓ b (fillFun (secIdx V σ b)
      (quoFun (secIdx V σ b) (secVec V σ b)
        (V.coordChange i₁.1.1 (V.indexAt b) b (fillFun i₁.1.2 (fstC m u)))))
      = ℓ b (V.coordChange i₁.1.1 (V.indexAt b) b (fillFun i₁.1.2 (fstC m u)))
        - ((V.coordChange i₁.1.1 (V.indexAt b) b (fillFun i₁.1.2 (fstC m u))) (secIdx V σ b)
            / secVec V σ b (secIdx V σ b)) := by
    rw [hlift, map_sub, map_smul, hℓ b]
    simp
  rw [hell, hlift]
  simp only [map_add, map_sub, map_smul]
  rw [hcv, hcomp]
  simp only [sub_smul, smul_sub, scalarC, ContinuousLinearMap.comp_apply]
  module

end Inv


variable (ℓ : B → (EuclideanSpace ℂ (Fin (m+1)) →L[ℂ] ℂ))

theorem inv_chart_clm_eq (hσ : IsSection σ) (hℓ : ∀ b, ℓ b (secVec V σ b) = 1)
    {ι₀ : Type} [Inhabited ι₀] (i₁ : (ι × Fin (m+1)) × ι₀) (i₂ : ι) (b : B)
    (hb : b ∈ (W (ι₀ := ι₀) V σ).baseSet i₁ ∩ V.baseSet i₂) :
    (V.coordChange (V.indexAt b) i₂ b).comp
        ((invCLM V σ ℓ b).comp ((W (ι₀ := ι₀) V σ).coordChange i₁
          ((W (ι₀ := ι₀) V σ).indexAt b) b))
      = invNice (V := V) (σ := σ) ℓ i₁ i₂ b := by
  refine ContinuousLinearMap.ext fun u => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    inv_chart_eq ℓ hσ hℓ i₁ i₂ b hb u]
  simp only [invNice, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply, fillCLM_apply, scalarC]

theorem continuousOn_invNice (hσ : IsSection σ)
    (hℓ : ∀ i : ι, ContinuousOn (fun b : B => (ℓ b).comp (V.coordChange i (V.indexAt b) b))
      (V.baseSet i))
    {ι₀ : Type} [Inhabited ι₀] (i₁ : (ι × Fin (m+1)) × ι₀) (i₂ : ι) :
    ContinuousOn (invNice (V := V) (σ := σ) ℓ i₁ i₂)
      ((W (ι₀ := ι₀) V σ).baseSet i₁ ∩ V.baseSet i₂) := by
  set S : Set B := (W (ι₀ := ι₀) V σ).baseSet i₁ ∩ V.baseSet i₂ with hS
  have hbQ : ∀ b ∈ S, b ∈ (Q V σ).baseSet i₁.1 := by
    intro b hb
    rw [← W_baseSet (V := V) (σ := σ) i₁.1 i₁.2]
    exact hb.1
  have hb1 : ∀ b ∈ S, b ∈ V.baseSet i₁.1.1 := fun b hb => (Q_mem_baseSet hσ i₁.1 b (hbQ b hb)).1
  have hproj : Continuous (fun p : ↥S × EuclideanSpace ℂ (Fin (m+1)) => (p.1 : B)) :=
    continuous_subtype_val.comp continuous_fst
  have hfst : Continuous (fun p : ↥S × EuclideanSpace ℂ (Fin (m+1)) =>
      fillFun i₁.1.2 (fstC m p.2)) :=
    ((fillCLM i₁.1.2).comp (fstC m)).continuous.comp continuous_snd
  have hc1 : Continuous (fun p : ↥S × EuclideanSpace ℂ (Fin (m+1)) =>
      V.coordChange i₁.1.1 i₂ p.1.1 (fillFun i₁.1.2 (fstC m p.2))) :=
    ((V.continuousOn_coordChange i₁.1.1 i₂).comp_continuous hproj
      (fun p => ⟨hb1 p.1 p.1.2, p.1.2.2⟩)).clm_apply hfst
  have hL' : Continuous (fun p : ↥S × EuclideanSpace ℂ (Fin (m+1)) =>
      (ℓ p.1.1).comp (V.coordChange i₁.1.1 (V.indexAt p.1.1) p.1.1)) :=
    (hℓ i₁.1.1).comp_continuous hproj (fun p => hb1 p.1 p.1.2)
  have hL'' : Continuous (fun p : ↥S × EuclideanSpace ℂ (Fin (m+1)) =>
      ℓ p.1.1 (V.coordChange i₁.1.1 (V.indexAt p.1.1) p.1.1 (fillFun i₁.1.2 (fstC m p.2)))) :=
    hL'.clm_apply hfst
  have hz : Continuous (fun p : ↥S × EuclideanSpace ℂ (Fin (m+1)) => zCoord i₂ (σ p.1.1)) :=
    (continuousOn_zCoord_sec hσ i₂).comp_continuous hproj (fun p => p.1.2.2)
  have hm1 : Continuous (fun p : ↥S × EuclideanSpace ℂ (Fin (m+1)) =>
      (ℓ p.1.1 (V.coordChange i₁.1.1 (V.indexAt p.1.1) p.1.1
        (fillFun i₁.1.2 (fstC m p.2)))) • zCoord i₂ (σ p.1.1)) := hL''.smul hz
  have hm2 : Continuous (fun p : ↥S × EuclideanSpace ℂ (Fin (m+1)) =>
      (scalarC m p.2) • zCoord i₂ (σ p.1.1)) :=
    (((scalarC m).continuous).comp continuous_snd).smul hz
  refine (continuousOn_clm_of_continuous_eval (s := S) ?_)
  refine ((hc1.sub hm1).add hm2).congr ?_
  intro p
  simp only [invNice, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply, fillCLM_apply,
    Pi.sub_apply, Pi.add_apply]

theorem continuousOn_inv_chart (hσ : IsSection σ)
    (hℓc : ∀ i : ι, ContinuousOn (fun b : B => (ℓ b).comp (V.coordChange i (V.indexAt b) b))
      (V.baseSet i))
    (hℓ1 : ∀ b, ℓ b (secVec V σ b) = 1)
    {ι₀ : Type} [Inhabited ι₀] (i₁ : (ι × Fin (m+1)) × ι₀) (i₂ : ι) :
    ContinuousOn (fun b => (V.coordChange (V.indexAt b) i₂ b).comp
        ((invCLM V σ ℓ b).comp ((W (ι₀ := ι₀) V σ).coordChange i₁
          ((W (ι₀ := ι₀) V σ).indexAt b) b)))
      ((W (ι₀ := ι₀) V σ).baseSet i₁ ∩ V.baseSet i₂) := by
  refine (continuousOn_invNice (V := V) (σ := σ) ℓ hσ hℓc i₁ i₂).congr (fun b hb => ?_)
  exact (inv_chart_clm_eq (V := V) (σ := σ) ℓ hσ hℓ1 i₁ i₂ b hb)

theorem continuousOn_hom_chart (hσ : IsSection σ)
    (hℓc : ∀ i : ι, ContinuousOn (fun b : B => (ℓ b).comp (V.coordChange i (V.indexAt b) b))
      (V.baseSet i))
    (hℓ1 : ∀ b, ℓ b (secVec V σ b) = 1)
    {ι₀ : Type} [Inhabited ι₀] (i₁ : ι) (i₂ : (ι × Fin (m+1)) × ι₀) :
    ContinuousOn (fun b => ((W (ι₀ := ι₀) V σ).coordChange ((W (ι₀ := ι₀) V σ).indexAt b) i₂ b).comp
        ((homCLM V σ ℓ b).comp (V.coordChange i₁ (V.indexAt b) b)))
      (V.baseSet i₁ ∩ (W (ι₀ := ι₀) V σ).baseSet i₂) := by
  obtain ⟨a, j⟩ := i₂
  refine (continuousOn_homNice (V := V) (σ := σ) ℓ hσ hℓc i₁ a j).congr (fun b hb => ?_)
  exact (hom_chart_clm_eq (V := V) (σ := σ) ℓ hσ hℓ1 i₁ a j b hb)

end NZ
end Work.Whitney
