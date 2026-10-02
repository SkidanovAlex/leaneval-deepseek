import Mathlib
import Submission.Work.ThomBordism.Grassmann.sumPiecesSetup
import Submission.Work.ThomBordism.Grassmann.isOpen_pieceFst_pieceSnd
import Submission.Work.Thom.LineGeom
import Submission.Work.Thom.sphereInDisc_homotopyEquiv

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Continuity of the maps of `Submission/Work/ThomBordism/Grassmann/sumPiecesSetup.lean`

The topology of the total space of a `VectorBundleCore` is given by its local trivialisations (and
not by the product topology), so the coordinate projections, the coordinate inclusions and the pair
identifications of the Whitney sum are not continuous for trivial reasons.  Each is proved here
through the general criterion `Work.Thom.continuous_totalSpaceMap_clm` (together with the
transition-function compatibility supplied by `fstAB_coordChange_gen`, `sndAB_coordChange_gen` and
`Work.Whitney.whitneySum_coordChange`), or, for `sumPsi`, in the local trivialisation of the target
(`continuous_iff_continuousAt`).  The complex-level statements are proved first and then transported
to the realifications along `Work.Thom.continuous_id_realification`/`_symm`.
-/

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

noncomputable section

variable {B : Type} [TopologicalSpace B] {a b : ℕ} {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]

/-! ## The two constant fibre inclusions -/

/-- The inclusion of the first summand in the model fibre of the Whitney sum. -/
def sumInclC (a b : ℕ) : EuclideanSpace ℂ (Fin a) →L[ℂ] EuclideanSpace ℂ (Fin (a + b)) :=
  ((Work.Whitney.sumFibreC a b :
      (EuclideanSpace ℂ (Fin a) × EuclideanSpace ℂ (Fin b)) →L[ℂ]
        EuclideanSpace ℂ (Fin (a + b)))).comp
    (ContinuousLinearMap.inl ℂ (EuclideanSpace ℂ (Fin a)) (EuclideanSpace ℂ (Fin b)))

/-- The inclusion of the second summand in the model fibre of the Whitney sum. -/
def sumInclRC (a b : ℕ) : EuclideanSpace ℂ (Fin b) →L[ℂ] EuclideanSpace ℂ (Fin (a + b)) :=
  ((Work.Whitney.sumFibreC a b :
      (EuclideanSpace ℂ (Fin a) × EuclideanSpace ℂ (Fin b)) →L[ℂ]
        EuclideanSpace ℂ (Fin (a + b)))).comp
    (ContinuousLinearMap.inr ℂ (EuclideanSpace ℂ (Fin a)) (EuclideanSpace ℂ (Fin b)))

theorem sumInclC_apply {a b : ℕ} (v : EuclideanSpace ℂ (Fin a)) :
    sumInclC a b v = Work.Whitney.sumFibreC a b (v, 0) := by
  rw [sumInclC, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  rfl

theorem sumInclRC_apply {a b : ℕ} (w : EuclideanSpace ℂ (Fin b)) :
    sumInclRC a b w = Work.Whitney.sumFibreC a b (0, w) := by
  rw [sumInclRC, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  rfl

/-! ## The transition functions of the sum untwist by the two inclusions -/

theorem whitneySum_coordChange_comp_sumInclC
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (i j : ι₁ × ι₂) (y : B) :
    ((Work.Whitney.whitneySum A C).coordChange i j y).comp (sumInclC a b)
      = (sumInclC a b).comp (A.coordChange i.1 j.1 y) := by
  refine ContinuousLinearMap.ext fun v => ?_
  show (Work.Whitney.whitneySum A C).coordChange i j y (sumInclC a b v)
    = sumInclC a b (A.coordChange i.1 j.1 y v)
  rw [Work.Whitney.whitneySum_coordChange]
  simp only [sumInclC, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearEquiv.symm_apply_apply, map_zero]

theorem whitneySum_coordChange_comp_sumInclRC
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (i j : ι₁ × ι₂) (y : B) :
    ((Work.Whitney.whitneySum A C).coordChange i j y).comp (sumInclRC a b)
      = (sumInclRC a b).comp (C.coordChange i.2 j.2 y) := by
  refine ContinuousLinearMap.ext fun v => ?_
  show (Work.Whitney.whitneySum A C).coordChange i j y (sumInclRC a b v)
    = sumInclRC a b (C.coordChange i.2 j.2 y v)
  rw [Work.Whitney.whitneySum_coordChange]
  simp only [sumInclRC, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply, ContinuousLinearMap.inr_apply,
    ContinuousLinearEquiv.symm_apply_apply, map_zero]

/-! ## The complex-level inclusions -/

theorem continuous_sumInclC_totalMap
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Continuous (fun p : A.TotalSpace =>
      (⟨p.1, sumInclC a b p.2⟩ : (Work.Whitney.whitneySum A C).TotalSpace)) := by
  refine Work.Thom.continuous_totalSpaceMap_clm A (Work.Whitney.whitneySum A C)
    (ContinuousMap.id B) (fun _ => sumInclC a b) ?_
  intro i₁ i₂
  have hsub : A.baseSet i₁ ∩ (Work.Whitney.whitneySum A C).baseSet i₂
      ⊆ A.baseSet i₁ ∩ A.baseSet i₂.1 := fun y hy => ⟨hy.1, by
    rw [Work.Whitney.whitneySum_baseSet] at hy
    exact hy.2.1⟩
  have hcont : ContinuousOn (fun y : B =>
      (sumInclC a b).comp (A.coordChange i₁ i₂.1 y))
      (A.baseSet i₁ ∩ (Work.Whitney.whitneySum A C).baseSet i₂) :=
    ContinuousOn.clm_comp continuousOn_const ((A.continuousOn_coordChange i₁ i₂.1).mono hsub)
  refine hcont.congr ?_
  intro y hy
  have hyA : y ∈ A.baseSet i₁ ∩ A.baseSet i₂.1 := hsub hy
  calc ((Work.Whitney.whitneySum A C).coordChange
        ((Work.Whitney.whitneySum A C).indexAt y) i₂ y).comp
        ((sumInclC a b).comp (A.coordChange i₁ (A.indexAt y) y))
      = (((Work.Whitney.whitneySum A C).coordChange
          ((Work.Whitney.whitneySum A C).indexAt y) i₂ y).comp (sumInclC a b)).comp
          (A.coordChange i₁ (A.indexAt y) y) := by
        rw [ContinuousLinearMap.comp_assoc]
    _ = ((sumInclC a b).comp (A.coordChange (A.indexAt y) i₂.1 y)).comp
          (A.coordChange i₁ (A.indexAt y) y) := by
        rw [Work.Whitney.whitneySum_indexAt, whitneySum_coordChange_comp_sumInclC]
    _ = (sumInclC a b).comp
          ((A.coordChange (A.indexAt y) i₂.1 y).comp (A.coordChange i₁ (A.indexAt y) y)) := by
        rw [ContinuousLinearMap.comp_assoc]
    _ = (sumInclC a b).comp (A.coordChange i₁ i₂.1 y) := by
        congr 1
        refine ContinuousLinearMap.ext fun v => ?_
        exact A.coordChange_comp i₁ (A.indexAt y) i₂.1 y
          ⟨⟨hyA.1, A.mem_baseSet_at y⟩, hyA.2⟩ v

theorem continuous_sumInclRC_totalMap
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Continuous (fun p : C.TotalSpace =>
      (⟨p.1, sumInclRC a b p.2⟩ : (Work.Whitney.whitneySum A C).TotalSpace)) := by
  refine Work.Thom.continuous_totalSpaceMap_clm C (Work.Whitney.whitneySum A C)
    (ContinuousMap.id B) (fun _ => sumInclRC a b) ?_
  intro i₁ i₂
  have hsub : C.baseSet i₁ ∩ (Work.Whitney.whitneySum A C).baseSet i₂
      ⊆ C.baseSet i₁ ∩ C.baseSet i₂.2 := fun y hy => ⟨hy.1, by
    rw [Work.Whitney.whitneySum_baseSet] at hy
    exact hy.2.2⟩
  have hcont : ContinuousOn (fun y : B =>
      (sumInclRC a b).comp (C.coordChange i₁ i₂.2 y))
      (C.baseSet i₁ ∩ (Work.Whitney.whitneySum A C).baseSet i₂) :=
    ContinuousOn.clm_comp continuousOn_const ((C.continuousOn_coordChange i₁ i₂.2).mono hsub)
  refine hcont.congr ?_
  intro y hy
  have hyC : y ∈ C.baseSet i₁ ∩ C.baseSet i₂.2 := hsub hy
  calc ((Work.Whitney.whitneySum A C).coordChange
        ((Work.Whitney.whitneySum A C).indexAt y) i₂ y).comp
        ((sumInclRC a b).comp (C.coordChange i₁ (C.indexAt y) y))
      = (((Work.Whitney.whitneySum A C).coordChange
          ((Work.Whitney.whitneySum A C).indexAt y) i₂ y).comp (sumInclRC a b)).comp
          (C.coordChange i₁ (C.indexAt y) y) := by
        rw [ContinuousLinearMap.comp_assoc]
    _ = ((sumInclRC a b).comp (C.coordChange (C.indexAt y) i₂.2 y)).comp
          (C.coordChange i₁ (C.indexAt y) y) := by
        rw [Work.Whitney.whitneySum_indexAt, whitneySum_coordChange_comp_sumInclRC]
    _ = (sumInclRC a b).comp
          ((C.coordChange (C.indexAt y) i₂.2 y).comp (C.coordChange i₁ (C.indexAt y) y)) := by
        rw [ContinuousLinearMap.comp_assoc]
    _ = (sumInclRC a b).comp (C.coordChange i₁ i₂.2 y) := by
        congr 1
        refine ContinuousLinearMap.ext fun v => ?_
        exact C.coordChange_comp i₁ (C.indexAt y) i₂.2 y
          ⟨⟨hyC.1, C.mem_baseSet_at y⟩, hyC.2⟩ v

/-! ## The realified inclusions -/

theorem continuous_sumIncl₁
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Continuous (sumIncl₁ A C) := by
  refine ((Work.Thom.continuous_id_realification (Work.Whitney.whitneySum A C)).comp
    ((continuous_sumInclC_totalMap A C).comp
      (Work.Thom.continuous_id_realification_symm A))).congr ?_
  intro p
  rfl

theorem continuous_sumIncl₂
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Continuous (sumIncl₂ A C) := by
  refine ((Work.Thom.continuous_id_realification (Work.Whitney.whitneySum A C)).comp
    ((continuous_sumInclRC_totalMap A C).comp
      (Work.Thom.continuous_id_realification_symm C))).congr ?_
  intro p
  rfl

/-! ## The transition functions of the sum untwist by the two projections -/

theorem fstAB_comp_whitneySum_coordChange
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (i j : ι₁ × ι₂) (y : B) :
    (fstAB a b).comp ((Work.Whitney.whitneySum A C).coordChange i j y)
      = (A.coordChange i.1 j.1 y).comp (fstAB a b) := by
  refine ContinuousLinearMap.ext fun v => ?_
  exact fstAB_coordChange_gen A C i j y v

theorem sndAB_comp_whitneySum_coordChange
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂)
    (i j : ι₁ × ι₂) (y : B) :
    (sndAB a b).comp ((Work.Whitney.whitneySum A C).coordChange i j y)
      = (C.coordChange i.2 j.2 y).comp (sndAB a b) := by
  refine ContinuousLinearMap.ext fun v => ?_
  exact sndAB_coordChange_gen A C i j y v

/-! ## The complex-level projections -/

theorem continuous_sumFstC_totalMap
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Continuous (fun p : (Work.Whitney.whitneySum A C).TotalSpace =>
      (⟨p.1, fstAB a b p.2⟩ : A.TotalSpace)) := by
  refine Work.Thom.continuous_totalSpaceMap_clm (Work.Whitney.whitneySum A C) A
    (ContinuousMap.id B) (fun _ => fstAB a b) ?_
  intro i₁ i₂
  have hsub : (Work.Whitney.whitneySum A C).baseSet i₁ ∩ A.baseSet i₂
      ⊆ A.baseSet i₁.1 ∩ A.baseSet i₂ := fun y hy => ⟨by
    rw [Work.Whitney.whitneySum_baseSet] at hy
    exact hy.1.1, hy.2⟩
  have hcont : ContinuousOn (fun y : B => (A.coordChange i₁.1 i₂ y).comp (fstAB a b))
      ((Work.Whitney.whitneySum A C).baseSet i₁ ∩ A.baseSet i₂) :=
    ContinuousOn.clm_comp ((A.continuousOn_coordChange i₁.1 i₂).mono hsub) continuousOn_const
  refine hcont.congr ?_
  intro y hy
  have hyA : y ∈ A.baseSet i₁.1 ∩ A.baseSet i₂ := hsub hy
  calc (A.coordChange (A.indexAt y) i₂ y).comp ((fstAB a b).comp
        ((Work.Whitney.whitneySum A C).coordChange i₁
          ((Work.Whitney.whitneySum A C).indexAt y) y))
      = (A.coordChange (A.indexAt y) i₂ y).comp
          ((A.coordChange i₁.1 (A.indexAt y) y).comp (fstAB a b)) := by
        rw [fstAB_comp_whitneySum_coordChange, Work.Whitney.whitneySum_indexAt]
    _ = ((A.coordChange (A.indexAt y) i₂ y).comp
          (A.coordChange i₁.1 (A.indexAt y) y)).comp (fstAB a b) := by
        rw [ContinuousLinearMap.comp_assoc]
    _ = (A.coordChange i₁.1 i₂ y).comp (fstAB a b) := by
        rw [show (A.coordChange (A.indexAt y) i₂ y).comp
              (A.coordChange i₁.1 (A.indexAt y) y) = A.coordChange i₁.1 i₂ y from by
          refine ContinuousLinearMap.ext fun v => ?_
          exact A.coordChange_comp i₁.1 (A.indexAt y) i₂ y
            ⟨⟨hyA.1, A.mem_baseSet_at y⟩, hyA.2⟩ v]

theorem continuous_sumSndC_totalMap
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Continuous (fun p : (Work.Whitney.whitneySum A C).TotalSpace =>
      (⟨p.1, sndAB a b p.2⟩ : C.TotalSpace)) := by
  refine Work.Thom.continuous_totalSpaceMap_clm (Work.Whitney.whitneySum A C) C
    (ContinuousMap.id B) (fun _ => sndAB a b) ?_
  intro i₁ i₂
  have hsub : (Work.Whitney.whitneySum A C).baseSet i₁ ∩ C.baseSet i₂
      ⊆ C.baseSet i₁.2 ∩ C.baseSet i₂ := fun y hy => ⟨by
    rw [Work.Whitney.whitneySum_baseSet] at hy
    exact hy.1.2, hy.2⟩
  have hcont : ContinuousOn (fun y : B => (C.coordChange i₁.2 i₂ y).comp (sndAB a b))
      ((Work.Whitney.whitneySum A C).baseSet i₁ ∩ C.baseSet i₂) :=
    ContinuousOn.clm_comp ((C.continuousOn_coordChange i₁.2 i₂).mono hsub) continuousOn_const
  refine hcont.congr ?_
  intro y hy
  have hyC : y ∈ C.baseSet i₁.2 ∩ C.baseSet i₂ := hsub hy
  calc (C.coordChange (C.indexAt y) i₂ y).comp ((sndAB a b).comp
        ((Work.Whitney.whitneySum A C).coordChange i₁
          ((Work.Whitney.whitneySum A C).indexAt y) y))
      = (C.coordChange (C.indexAt y) i₂ y).comp
          ((C.coordChange i₁.2 (C.indexAt y) y).comp (sndAB a b)) := by
        rw [sndAB_comp_whitneySum_coordChange, Work.Whitney.whitneySum_indexAt]
    _ = ((C.coordChange (C.indexAt y) i₂ y).comp
          (C.coordChange i₁.2 (C.indexAt y) y)).comp (sndAB a b) := by
        rw [ContinuousLinearMap.comp_assoc]
    _ = (C.coordChange i₁.2 i₂ y).comp (sndAB a b) := by
        rw [show (C.coordChange (C.indexAt y) i₂ y).comp
              (C.coordChange i₁.2 (C.indexAt y) y) = C.coordChange i₁.2 i₂ y from by
          refine ContinuousLinearMap.ext fun v => ?_
          exact C.coordChange_comp i₁.2 (C.indexAt y) i₂ y
            ⟨⟨hyC.1, C.mem_baseSet_at y⟩, hyC.2⟩ v]

/-! ## The realified projections -/

theorem continuous_sumFstFn
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Continuous (sumFstFn A C) := by
  refine ((Work.Thom.continuous_id_realification A).comp
    ((continuous_sumFstC_totalMap A C).comp
      (Work.Thom.continuous_id_realification_symm (Work.Whitney.whitneySum A C)))).congr ?_
  intro p
  rfl

theorem continuous_sumSndFn
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Continuous (sumSndFn A C) := by
  refine ((Work.Thom.continuous_id_realification C).comp
    ((continuous_sumSndC_totalMap A C).comp
      (Work.Thom.continuous_id_realification_symm (Work.Whitney.whitneySum A C)))).congr ?_
  intro p
  rfl


/-! ## The "insert into the second summand" total-space map, and `sumPhi` -/

theorem continuous_sumPhiSndC
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Continuous (fun p : (sumZ1c A C).TotalSpace =>
      (⟨p.1.1, sumInclRC a b p.2⟩ : (Work.Whitney.whitneySum A C).TotalSpace)) := by
  refine Work.Thom.continuous_totalSpaceMap_clm (sumZ1c A C) (Work.Whitney.whitneySum A C)
    (Work.Thom.bundleProj (sumAR A)) (fun _ => sumInclRC a b) ?_
  intro i₁ i₂
  have hsub : (Work.Thom.bundleProj (sumAR A)) ⁻¹'
      (C.baseSet i₁ ∩ (Work.Whitney.whitneySum A C).baseSet i₂)
      ⊆ (Work.Thom.bundleProj (sumAR A)) ⁻¹' (C.baseSet i₁ ∩ C.baseSet i₂.2) := by
    rintro q ⟨h1, h2⟩
    rw [Work.Whitney.whitneySum_baseSet] at h2
    exact ⟨h1, h2.2⟩
  have hbase : (sumZ1c A C).baseSet i₁ ∩ (Work.Thom.bundleProj (sumAR A)) ⁻¹'
      (Work.Whitney.whitneySum A C).baseSet i₂
      = (Work.Thom.bundleProj (sumAR A)) ⁻¹'
        (C.baseSet i₁ ∩ (Work.Whitney.whitneySum A C).baseSet i₂) := by
    rw [Work.Thom.bundleComap_baseSet, Set.preimage_inter]
  have hcont : ContinuousOn (fun q : (sumAR A).TotalSpace =>
      (sumInclRC a b).comp (C.coordChange i₁ i₂.2 q.1))
      ((sumZ1c A C).baseSet i₁ ∩ (Work.Thom.bundleProj (sumAR A)) ⁻¹'
        (Work.Whitney.whitneySum A C).baseSet i₂) := by
    rw [hbase]
    exact ContinuousOn.clm_comp continuousOn_const
      ((C.continuousOn_coordChange i₁ i₂.2).comp
        (Work.Thom.bundleProj (sumAR A)).continuous.continuousOn (fun q hq => hsub hq))
  refine hcont.congr ?_
  intro q hq
  have hqC : q.1 ∈ C.baseSet i₁ ∩ C.baseSet i₂.2 := hsub (hbase ▸ hq)
  calc ((Work.Whitney.whitneySum A C).coordChange
        ((Work.Whitney.whitneySum A C).indexAt q.1) i₂ q.1).comp
        ((sumInclRC a b).comp ((sumZ1c A C).coordChange i₁ ((sumZ1c A C).indexAt q) q))
      = ((Work.Whitney.whitneySum A C).coordChange
          ((Work.Whitney.whitneySum A C).indexAt q.1) i₂ q.1).comp
          ((sumInclRC a b).comp (C.coordChange i₁ (C.indexAt q.1) q.1)) := by
        rw [Work.Thom.bundleComap_coordChange, Work.Thom.bundleComap_indexAt,
          Work.Thom.bundleProj_apply]
    _ = (sumInclRC a b).comp ((C.coordChange (C.indexAt q.1) i₂.2 q.1).comp
          (C.coordChange i₁ (C.indexAt q.1) q.1)) := by
        rw [← ContinuousLinearMap.comp_assoc, whitneySum_coordChange_comp_sumInclRC,
          Work.Whitney.whitneySum_indexAt, ContinuousLinearMap.comp_assoc]
    _ = (sumInclRC a b).comp (C.coordChange i₁ i₂.2 q.1) := by
        congr 1
        refine ContinuousLinearMap.ext fun v => ?_
        exact C.coordChange_comp i₁ (C.indexAt q.1) i₂.2 q.1
          ⟨⟨hqC.1, C.mem_baseSet_at q.1⟩, hqC.2⟩ v

theorem continuous_sumPhiSnd
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Continuous (fun p : (sumZ1c A C).TotalSpace =>
      (⟨p.1.1, sumInclRC a b p.2⟩ : (sumW A C).TotalSpace)) := by
  refine ((Work.Thom.continuous_id_realification (Work.Whitney.whitneySum A C)).comp
    (continuous_sumPhiSndC A C)).congr ?_
  intro p
  rfl

theorem continuous_sumPhi
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Continuous (sumPhi A C) := by
  have h₁ : Continuous (fun p : (sumZ1c A C).TotalSpace =>
      (⟨p.1.1, sumInclC a b (sumFibA A p.1)⟩ : (sumW A C).TotalSpace)) :=
    (continuous_sumIncl₁ A C).comp (sumZ1c A C).continuous_proj
  have h₂ : Continuous (fun p : (sumZ1c A C).TotalSpace =>
      (⟨p.1.1, sumInclRC a b p.2⟩ : (sumW A C).TotalSpace)) := continuous_sumPhiSnd A C
  let σ : C((sumZ1c A C).TotalSpace, (sumW A C).TotalSpace) :=
    ⟨fun p => (⟨p.1.1, sumInclC a b (sumFibA A p.1)⟩ : (sumW A C).TotalSpace), h₁⟩
  let τ : C((sumZ1c A C).TotalSpace, (sumW A C).TotalSpace) :=
    ⟨fun p => (⟨p.1.1, sumInclRC a b p.2⟩ : (sumW A C).TotalSpace), h₂⟩
  have hadd := Work.Thom.continuous_add_section (sumW A C) σ τ (fun p => rfl)
  refine hadd.congr ?_
  intro p
  show (⟨p.1.1, (show EuclideanSpace ℂ (Fin (a + b)) from
      (σ p).2) + (show EuclideanSpace ℂ (Fin (a + b)) from (τ p).2)⟩ :
        (sumW A C).TotalSpace) =
    (⟨p.1.1, Work.Whitney.sumFibreC a b (sumFibA A p.1, sumFibZ1 A C p)⟩ :
        (sumW A C).TotalSpace)
  show (⟨p.1.1, sumInclC a b (sumFibA A p.1) + sumInclRC a b p.2⟩ :
      (sumW A C).TotalSpace) = _
  rw [sumInclC_apply, sumInclRC_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  rfl


/-! ## Continuity of `sumPsi` -/

/-- The second projection of the sum, read with the *complex* topology of `C` on the target. -/
def sumSndF (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    (sumW A C).TotalSpace → C.TotalSpace :=
  fun p => ⟨p.1, sndAB a b (sumFibW A C p)⟩

theorem continuous_sumSndF
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Continuous (sumSndF A C) :=
  ((Work.Thom.continuous_id_realification_symm C).comp (continuous_sumSndFn A C)).congr
    (fun p => rfl)

/-- The chart formula for `sumPsi`: in the trivialisation of the pullback `sumZ1c A C` at the
preferred index of the image point, the composite is the base point of the source together with
the second component of the `C`-chart of `sumSndF`. -/
theorem sumZ1_localTriv_sumPsi
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) (i : ι₂)
    (p : (sumW A C).TotalSpace) :
    (sumZ1c A C).localTriv i (sumPsi A C p) =
      (sumFstFn A C p, ((C).localTriv i (sumSndF A C p)).2) := by
  rw [VectorBundleCore.localTriv_apply, VectorBundleCore.localTriv_apply,
    Work.Thom.bundleComap_coordChange, Work.Thom.bundleComap_indexAt,
    Work.Thom.bundleProj_apply]
  rfl

theorem continuous_sumPsi
    (A : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin a)) ι₁)
    (C : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin b)) ι₂) :
    Continuous (sumPsi A C) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  set q₀ : (sumAR A).TotalSpace := ⟨p₀.1, fstAB a b (sumFibW A C p₀)⟩ with hq₀
  set i : ι₂ := (sumZ1c A C).indexAt q₀ with hi
  have hbase : q₀ ∈ (sumZ1c A C).baseSet i := by
    rw [hi]; exact (sumZ1c A C).mem_baseSet_at q₀
  refine ((sumZ1c A C).localTriv i).continuousAt_of_comp_left ?_ ?_ ?_
  · have h : Continuous (fun p : (sumW A C).TotalSpace => (sumZ1c A C).proj (sumPsi A C p)) :=
      (continuous_sumFstFn A C).congr (fun p => rfl)
    exact h.continuousAt
  · exact hbase
  · have hmem : sumSndF A C p₀ ∈ ((C).localTriv i).source := by
      rw [Bundle.Trivialization.mem_source]
      exact hbase
    have hloc : ContinuousAt (fun p => ((C).localTriv i) (sumSndF A C p)) p₀ :=
      (((C).localTriv i).toOpenPartialHomeomorph.continuousAt hmem).comp
        (continuous_sumSndF A C).continuousAt
    have h2 : ContinuousAt (fun p => (((C).localTriv i) (sumSndF A C p)).2) p₀ :=
      continuous_snd.continuousAt.comp hloc
    have hpair : ContinuousAt (fun p : (sumW A C).TotalSpace =>
        (sumFstFn A C p, ((C).localTriv i (sumSndF A C p)).2)) p₀ :=
      (continuous_sumFstFn A C).continuousAt.prodMk h2
    refine hpair.congr ?_
    filter_upwards with p
    exact (sumZ1_localTriv_sumPsi A C i p).symm

end

end Work.ThomBordism.Grassmann
