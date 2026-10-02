import Submission.Work.ThomBordism.Grassmann.TB.tbGaugeMain

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

/-!
# The transition identities of the gauge `tbZ ≅ tbW`

The compatibility of the gauge with the two trivialisations: the transition functions of `tbW`
(the block diagonal of `expCMul (homCoord 4 i i')`, i.e. the realification of the tautological line
bundle doubled) and those of `tbZ` (the oriented Grassmannian charts of `tbMap`).
-/

namespace Work.ThomBordism.Grassmann.TBG

open Work.TangentClasses Work.Projective

noncomputable section

/-! ## 1. The transition functions of `tbW` -/

/-- The transition function of the realified tautological line bundle is `expCMul (homCoord)`. -/
theorem tbgZL_coordChange (i i' : Fin 5) (x : CP 4) :
    tbZL.coordChange i i' x = expCMul (Work.Gen.homCoord 4 i i' x) := by
  rw [tbZL, RealBundle.mapFibre_coordChange]
  apply ContinuousLinearMap.ext
  intro z
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Work.Thom.realification_coordChange, Work.Gen.tautLine_coordChange,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  rw [expCMul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    cmulLM_apply]

/-- **The transition function of `tbW`**, pointwise: the block diagonal `expCMul (homCoord)`. -/
theorem tbgW_coordChange_apply (t t' : Fin 5 × Fin 5) (x : CP 4) (d : Amb 4) :
    tbW.coordChange t t' x d = (Work.Whitney.sumFibreR 2 2)
      (expCMul (Work.Gen.homCoord 4 t.1 t'.1 x) ((Work.Whitney.sumFibreR 2 2).symm d).1,
       expCMul (Work.Gen.homCoord 4 t.2 t'.2 x) ((Work.Whitney.sumFibreR 2 2).symm d).2) := by
  rw [tbW, Work.Whitney.whitneySumR_coordChange, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_prodMap',
    tbgZL_coordChange, tbgZL_coordChange]
  rfl

/-- The base set of `tbW` in terms of the charts of `ℂP⁴`. -/
theorem tbgMem_tbW_baseSet (t : Fin 5 × Fin 5) (x : CP 4) :
    x ∈ tbW.baseSet t ↔ x ∈ Work.Projective.chartSet t.1 ∩ Work.Projective.chartSet t.2 := by
  simp only [tbW, Work.Whitney.whitneySumR_baseSet, tbZL, RealBundle.mapFibre_baseSet,
    Work.Thom.realification_baseSet, Work.Gen.tautLine_baseSet]

/-! ## 2. The gauge is compatible with the transition functions of `tbW` -/

/-- The block coefficients of `tbPhi` are the components of `(sumFibreR 2 2).symm ∘ tbPhi`. -/
theorem tbgSumFibreR_symm_tbPhi (S : ChartIdx 4 16) (t : Fin 5 × Fin 5) (x : CP 4) (c : Amb 4) :
    (Work.Whitney.sumFibreR 2 2).symm (tbPhi S t x c)
      = (tbCoefL S t.1 x c, tbCoefR S t.2 x c) := by
  rw [tbPhi_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- **The `tbW`-transition identity of the gauge.** -/
theorem tbgPhi_htgt (S : ChartIdx 4 16) (t t' : Fin 5 × Fin 5) (x : CP 4)
    (hS : tbMap x ∈ baseSet S)
    (ht₁ : x ∈ Work.Projective.chartSet t.1) (ht₂ : x ∈ Work.Projective.chartSet t.2)
    (ht₁' : x ∈ Work.Projective.chartSet t'.1) (ht₂' : x ∈ Work.Projective.chartSet t'.2) :
    (tbW.coordChange t t' x).comp (tbPhi S t x) = tbPhi S t' x := by
  apply ContinuousLinearMap.ext
  intro c
  rw [ContinuousLinearMap.comp_apply, tbPhi_apply, tbgW_coordChange_apply,
    ContinuousLinearEquiv.symm_apply_apply, tbPhi_apply]
  congr 1
  exact Prod.ext (tbgCoefL_change S t.1 t'.1 x hS ht₁ ht₁' c).symm
    (tbgCoefR_change S t.2 t'.2 x hS ht₂ ht₂' c).symm

/-! ## 3. The gauge is compatible with the transition functions of `tbZ` -/

theorem tbgZ_coordChange (S S' : ChartIdx 4 16) (x : CP 4) :
    tbZ.coordChange S' S x = coordChangeO S' S (tbMap x) :=
  Work.Thom.bundleComap_coordChange (tautologicalBundle 4 16) tbMap S' S x

/-- The plane vector read in the two charts is the same vector. -/
theorem tbgEW_glue (S S' : ChartIdx 4 16) (i : Fin 5) (x : CP 4)
    (hS : tbMap x ∈ baseSet S) (hS' : tbMap x ∈ baseSet S')
    (hx : x ∈ Work.Projective.chartSet i) (c : Amb 4) :
    tbEW S i x (coordChangeO S' S (tbMap x) c) = tbEW S' i x c := by
  rw [tbgEW_eq_evalChartO S i x hS hx (coordChangeO S' S (tbMap x) c),
    tbgEW_eq_evalChartO S' i x hS' hx c]
  exact (evalChartO_glue S' S (tbMap x) ⟨hS', hS⟩ c).symm

theorem tbgCoefL_glue (S S' : ChartIdx 4 16) (i : Fin 5) (x : CP 4) (c : Amb 4)
    (hS : tbMap x ∈ baseSet S) (hS' : tbMap x ∈ baseSet S')
    (hi : x ∈ Work.Projective.chartSet i) :
    tbCoefL S i x (coordChangeO S' S (tbMap x) c) = tbCoefL S' i x c := by
  rw [tbCoefL_apply, tbCoefL_apply, tbVecL_apply, tbVecL_apply, tbgEW_glue S S' i x hS hS' hi c]

theorem tbgCoefR_glue (S S' : ChartIdx 4 16) (j : Fin 5) (x : CP 4) (c : Amb 4)
    (hS : tbMap x ∈ baseSet S) (hS' : tbMap x ∈ baseSet S')
    (hj : x ∈ Work.Projective.chartSet j) :
    tbCoefR S j x (coordChangeO S' S (tbMap x) c) = tbCoefR S' j x c := by
  rw [tbCoefR_apply, tbCoefR_apply, tbVecR_apply, tbVecR_apply, tbgEW_glue S S' j x hS hS' hj c]

/-- **The `tbZ`-transition identity of the gauge.** -/
theorem tbgPhi_hsrc (S S' : ChartIdx 4 16) (t : Fin 5 × Fin 5) (x : CP 4)
    (hS : tbMap x ∈ baseSet S) (hS' : tbMap x ∈ baseSet S')
    (ht₁ : x ∈ Work.Projective.chartSet t.1) (ht₂ : x ∈ Work.Projective.chartSet t.2) :
    (tbPhi S t x).comp (tbZ.coordChange S' S x) = tbPhi S' t x := by
  apply ContinuousLinearMap.ext
  intro c
  rw [ContinuousLinearMap.comp_apply, tbgZ_coordChange, tbPhi_apply, tbPhi_apply]
  congr 1
  exact Prod.ext (tbgCoefL_glue S S' t.1 x c hS hS' ht₁)
    (tbgCoefR_glue S S' t.2 x c hS hS' ht₂)

/-! ## 4. The inverse transition identities -/

/-- **The inverse `tbW`-transition identity of the gauge.** -/
theorem tbgPhi_htgtinv (S : ChartIdx 4 16) (t t' : Fin 5 × Fin 5) (x : CP 4)
    (hS : tbMap x ∈ baseSet S)
    (ht₁ : x ∈ Work.Projective.chartSet t.1) (ht₂ : x ∈ Work.Projective.chartSet t.2)
    (ht₁' : x ∈ Work.Projective.chartSet t'.1) (ht₂' : x ∈ Work.Projective.chartSet t'.2) :
    (tbPhiInv S t x).comp (tbW.coordChange t' t x) = tbPhiInv S t' x := by
  apply ContinuousLinearMap.ext
  intro d
  have hM : tbPhi S t x (tbPhiInv S t' x d) = tbW.coordChange t' t x d := by
    rw [← tbgPhi_htgt S t' t x hS ht₁' ht₂' ht₁ ht₂]
    show tbW.coordChange t' t x (tbPhi S t' x (tbPhiInv S t' x d)) = tbW.coordChange t' t x d
    rw [tbgPhi_tbPhiInv S t' x hS ⟨ht₁', ht₂'⟩ d]
  rw [ContinuousLinearMap.comp_apply, ← hM]
  exact tbgPhiInv_tbPhi S t x hS ⟨ht₁, ht₂⟩ (tbPhiInv S t' x d)

/-- **The inverse `tbZ`-transition identity of the gauge.** -/
theorem tbgPhi_hsrcinv (S S' : ChartIdx 4 16) (t : Fin 5 × Fin 5) (x : CP 4)
    (hS : tbMap x ∈ baseSet S) (hS' : tbMap x ∈ baseSet S')
    (ht₁ : x ∈ Work.Projective.chartSet t.1) (ht₂ : x ∈ Work.Projective.chartSet t.2) :
    (tbZ.coordChange S S' x).comp (tbPhiInv S t x) = tbPhiInv S' t x := by
  apply ContinuousLinearMap.ext
  intro d
  have hM : tbPhi S' t x (tbZ.coordChange S S' x (tbPhiInv S t x d)) = d := by
    rw [← ContinuousLinearMap.comp_apply, tbgPhi_hsrc S' S t x hS' hS ht₁ ht₂]
    exact tbgPhi_tbPhiInv S t x hS ⟨ht₁, ht₂⟩ d
  calc tbZ.coordChange S S' x (tbPhiInv S t x d)
      = tbPhiInv S' t x (tbPhi S' t x (tbZ.coordChange S S' x (tbPhiInv S t x d))) :=
        (tbgPhiInv_tbPhi S' t x hS' ⟨ht₁, ht₂⟩ _).symm
    _ = tbPhiInv S' t x d := by rw [hM]

end

end Work.ThomBordism.Grassmann.TBG
