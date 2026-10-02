import Mathlib
import Submission.Work.Gen.Cp2Cp2TangentSplits
import Submission.Work.Gen.Cp2Cp2TangentSetup
import Submission.Work.Whitney.sumFibre_cxTrans
import Submission.Work.Whitney.nonempty_bundleIso_whitneySum_comm
import Submission.Work.Gen.nonempty_bundleIso_of_oneSidedMatch

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The product splitting of the complexified tangent bundle of `ℂP² × ℂP²`

`Work.Gen.Cp2Cp2TangentSplits` states that the complexified tangent bundle of `ℂP² × ℂP²`, in the
presentation of `Work.Gen.cp2cp2TangentC` (over the explicit `ℝ⁸`-atlas
`Work.Gen.cp2cp2ChartedSpaceEuclid`, which is the pushforward of the product atlas along the linear
isometry `Φ : ℝ⁴ × ℝ⁴ ≅ ℝ⁸`), is isomorphic to the direct sum of the pullbacks of the complexified
tangent bundles of the two factors.

The proof chain is:

* `Work.Gen.pushTangentCoordChange` — **the chain rule**: the transition function of `T(ℂP² × ℂP²)`
  over the pushed-forward `ℝ⁸`-charts, from the preferred chart at `b` to the (pushed) product chart
  `A₁ × A₂`, is the conjugate by `Φ` of the product of the transition functions of `TℂP²` in the two
  factors.  This is the analytical content: the derivative of `Φ ∘ (A₁ × A₂) ∘ (chartAt b)⁻¹`,
  computed by the chain rule for the linear isometry `Φ` and `fderivWithin_prodMap`/`HasFDerivAt.prodMap`
  for the product.  The hypothesis `b ∈ (pushIdx (A₁,A₂)).1.source` is what makes the two chart
  transitions genuine near the point where the derivative is taken.
* `Work.Gen.complexifiedPushCoordChange` — its complexification, using `Work.Whitney.sumFibre_cxTrans`
  (`cxTrans (transportEnd Φ T₁ T₂) = transportEnd sumFibreC (cxTrans T₁) (cxTrans T₂)`) and the
  definitional unfolding of the direct sum `Work.Whitney.whitneySum` and of the complexification of
  the pullbacks.
* `Work.Gen.nonempty_bundleIso_of_oneSidedMatch` — a general criterion producing a bundle
  isomorphism from the matching of the transition functions *in the preferred charts*
  `X.indexAt b`, `Y.indexAt b` of each point; applied with the index map `pushIdx`, the complexified
  chain rule is exactly its hypothesis, and the cover alignment is `Work.Gen.pushIdx_source`.
-/

open scoped Manifold ContDiff Topology

namespace Work.Gen

open Work.Projective

noncomputable section

/-! ## The pushed-forward tangent bundle: the chain rule -/

@[simp] theorem PhiH_source : PhiH.source = Set.univ :=
  Homeomorph.toOpenPartialHomeomorph_source _

@[simp] theorem PhiH_target : PhiH.target = Set.univ :=
  Homeomorph.toOpenPartialHomeomorph_target _

@[simp] theorem PhiH_apply (u : ModelProd H4 H4) : PhiH u = (prodLinEquiv 4 4) u := rfl

@[simp] theorem PhiH_symm_apply (u : H8) : PhiH.symm u = (prodLinEquiv 4 4).symm u := rfl

@[simp] theorem trans_PhiH_apply (A : OpenPartialHomeomorph P2 (ModelProd H4 H4)) (u : P2) :
    (A.trans PhiH) u = (prodLinEquiv 4 4) (A u) := by
  rw [OpenPartialHomeomorph.trans_apply]
  rfl

@[simp] theorem trans_PhiH_symm_apply (A : OpenPartialHomeomorph P2 (ModelProd H4 H4)) (u : H8) :
    (A.trans PhiH).symm u = A.symm ((prodLinEquiv 4 4).symm u) := by
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_apply]
  rfl

theorem trans_PhiH_source (A : OpenPartialHomeomorph P2 (ModelProd H4 H4)) :
    (A.trans PhiH).source = A.source := by
  rw [OpenPartialHomeomorph.trans_source]
  simp

theorem extend_self_apply {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : OpenPartialHomeomorph X E) (u : X) :
    (f.extend (𝓘(ℝ, E))) u = f u := by
  rw [OpenPartialHomeomorph.extend_coe]
  simp

theorem extend_self_symm_apply {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : OpenPartialHomeomorph X E) (u : E) :
    ((f.extend (𝓘(ℝ, E))).symm) u = f.symm u := by
  rw [OpenPartialHomeomorph.extend_coe_symm]
  simp

theorem range_self_univ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Set.range (𝓘(ℝ, E)) = Set.univ :=
  ModelWithCorners.range_eq_univ _

theorem pushIdx_source (A₁ A₂ : atlas H4 (CP 2)) :
    (pushIdx (A₁, A₂)).1.source = A₁.1.source ×ˢ A₂.1.source := by
  show ((A₁.1.prod A₂.1).trans PhiH).source = _
  rw [trans_PhiH_source, OpenPartialHomeomorph.prod_source]

theorem mem_pushIdx_source_iff (A₁ A₂ : atlas H4 (CP 2)) (b : P2) :
    b ∈ (pushIdx (A₁, A₂)).1.source ↔ b.1 ∈ A₁.1.source ∧ b.2 ∈ A₂.1.source := by
  rw [pushIdx_source, Set.mem_prod]

theorem pushIdx_val (A₁ A₂ : atlas H4 (CP 2)) :
    (pushIdx (A₁, A₂)).1 = (A₁.1.prod A₂.1).trans PhiH := rfl

theorem achart_H8_val (b : P2) :
    (achart H8 b).1 = (chartAt (ModelProd H4 H4) b).trans PhiH := rfl

/-- **Each factor of the product transition is differentiable**, with derivative the transition
function of the tangent bundle of `ℂP²` in the preferred chart. -/
theorem factor_hasFDerivAt (A : atlas H4 (CP 2)) (p : CP 2) (hb : p ∈ A.1.source) :
    HasFDerivAt (fun v : H4 => A.1 ((chartAt H4 p).symm v))
      ((Work.TangentClasses.tangentBundle 𝓘(ℝ, H4) (CP 2)).coordChange (achart H4 p) A p)
      (chartAt H4 p p) := by
  have hfun : ⇑(ModelWithCorners.extendCoordChange (I := 𝓘(ℝ, H4)) (chartAt H4 p) A.1)
      = fun v : H4 => A.1 ((chartAt H4 p).symm v) := by
    funext v
    rw [ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply,
      OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_coe]
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply]
    rfl
  have hmem : (chartAt H4 p p)
      ∈ (ModelWithCorners.extendCoordChange (I := 𝓘(ℝ, H4)) (chartAt H4 p) A.1).source := by
    rw [ModelWithCorners.extendCoordChange_source]
    refine ⟨chartAt H4 p p, ?_, rfl⟩
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · rw [OpenPartialHomeomorph.symm_source]
      exact (chartAt H4 p).map_source (mem_chart_source H4 p)
    · rw [Set.mem_preimage]
      rw [show (chartAt H4 p).symm (chartAt H4 p p) = p from
        OpenPartialHomeomorph.left_inv _ (mem_chart_source H4 p)]
      exact hb
  have hcd := ModelWithCorners.contDiffWithinAt_extendCoordChange (I := 𝓘(ℝ, H4)) (n := ∞)
    (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, H4)) (n := ∞)
      (show (chartAt H4 p) ∈ atlas H4 (CP 2) from chart_mem_atlas _ _))
    (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, H4)) (n := ∞) A.2) hmem
  have hfda : HasFDerivWithinAt
      (⇑(ModelWithCorners.extendCoordChange (I := 𝓘(ℝ, H4)) (chartAt H4 p) A.1))
      (fderivWithin ℝ (⇑(ModelWithCorners.extendCoordChange (I := 𝓘(ℝ, H4)) (chartAt H4 p) A.1))
        (Set.range (𝓘(ℝ, H4))) (chartAt H4 p p))
      (Set.range (𝓘(ℝ, H4))) (chartAt H4 p p) :=
    (hcd.differentiableWithinAt (by simp)).hasFDerivWithinAt
  rw [range_self_univ, hasFDerivWithinAt_univ] at hfda
  rw [hfun] at hfda
  have hderiv : fderivWithin ℝ (fun v : H4 => A.1 ((chartAt H4 p).symm v))
      Set.univ (chartAt H4 p p)
      = (Work.TangentClasses.tangentBundle 𝓘(ℝ, H4) (CP 2)).coordChange (achart H4 p) A p := by
    have hfun2 : (fun v : H4 => A.1 ((chartAt H4 p).symm v))
        = (⇑(A.1.extend (𝓘(ℝ, H4))) ∘ ⇑(((chartAt H4 p).extend (𝓘(ℝ, H4))).symm)) := by
      funext v
      rw [Function.comp_apply, extend_self_apply, extend_self_symm_apply]
    rw [fderivWithin_univ, hfun2]
    show fderiv ℝ
        (⇑(A.1.extend (𝓘(ℝ, H4))) ∘ ⇑(((chartAt H4 p).extend (𝓘(ℝ, H4))).symm))
        (chartAt H4 p p)
      = fderivWithin ℝ
          (⇑(A.1.extend (𝓘(ℝ, H4))) ∘ ⇑(((chartAt H4 p).extend (𝓘(ℝ, H4))).symm))
          (Set.range (𝓘(ℝ, H4))) (⇑((chartAt H4 p).extend (𝓘(ℝ, H4))) p)
    rw [range_self_univ, fderivWithin_univ, extend_self_apply]
  rw [hderiv] at hfda
  exact hfda

/-- **The chain rule for the pushed-forward tangent bundle.**  Over the `ℝ⁸`-atlas of
`ℂP² × ℂP²` (the pushforward of the product atlas along `Φ = prodLinEquiv 4 4`), the transition
function of the tangent bundle, from the (pushed) product chart at `b` to the (pushed) product
chart `A₁ × A₂`, is the conjugate by `Φ` of the product of the transition functions of the tangent
bundle of `ℂP²` in the two factors.  The hypothesis that `b` lies in the source of the target chart
makes both chart transitions genuine near the point. -/
theorem pushTangentCoordChange (A₁ A₂ : atlas H4 (CP 2)) (b : P2)
    (hb : b ∈ (pushIdx (A₁, A₂)).1.source) :
    (Work.TangentClasses.tangentBundle 𝓘(ℝ, H8) P2).coordChange (achart H8 b)
        (pushIdx (A₁, A₂)) b
      = ((prodLinEquiv 4 4 : (H4 × H4) ≃L[ℝ] H8) : (H4 × H4) →L[ℝ] H8).comp
          ((((Work.TangentClasses.tangentBundle 𝓘(ℝ, H4) (CP 2)).coordChange
                (achart H4 b.1) A₁ b.1).prodMap
              ((Work.TangentClasses.tangentBundle 𝓘(ℝ, H4) (CP 2)).coordChange
                (achart H4 b.2) A₂ b.2)).comp
            (((prodLinEquiv 4 4 : (H4 × H4) ≃L[ℝ] H8)).symm : H8 →L[ℝ] (H4 × H4))) := by
  have hb₁ : b.1 ∈ A₁.1.source := ((mem_pushIdx_source_iff A₁ A₂ b).mp hb).1
  have hb₂ : b.2 ∈ A₂.1.source := ((mem_pushIdx_source_iff A₁ A₂ b).mp hb).2
  have h1 : (Work.TangentClasses.tangentBundle 𝓘(ℝ, H8) P2).coordChange (achart H8 b)
        (pushIdx (A₁, A₂)) b
      = fderiv ℝ (fun u : H8 => (prodLinEquiv 4 4)
            ((A₁.1.prod A₂.1) ((chartAt (ModelProd H4 H4) b).symm
              ((prodLinEquiv 4 4).symm u))))
          ((prodLinEquiv 4 4) ((chartAt (ModelProd H4 H4) b) b)) := by
    show fderivWithin ℝ
        (⇑((pushIdx (A₁, A₂)).1.extend (𝓘(ℝ, H8))) ∘
          ⇑(((achart H8 b).1.extend (𝓘(ℝ, H8))).symm))
        (Set.range (𝓘(ℝ, H8))) (⇑((achart H8 b).1.extend (𝓘(ℝ, H8))) b) = _
    have hfun : (⇑((pushIdx (A₁, A₂)).1.extend (𝓘(ℝ, H8))) ∘
          ⇑(((achart H8 b).1.extend (𝓘(ℝ, H8))).symm))
        = fun u : H8 => (prodLinEquiv 4 4)
            ((A₁.1.prod A₂.1) ((chartAt (ModelProd H4 H4) b).symm
              ((prodLinEquiv 4 4).symm u))) := by
      funext u
      rw [Function.comp_apply, extend_self_apply, extend_self_symm_apply,
        achart_H8_val, pushIdx_val, trans_PhiH_apply, trans_PhiH_symm_apply]
    have hpt : (⇑((achart H8 b).1.extend (𝓘(ℝ, H8))) b)
        = (prodLinEquiv 4 4) ((chartAt (ModelProd H4 H4) b) b) := by
      rw [extend_self_apply, achart_H8_val, trans_PhiH_apply]
    rw [hfun, hpt, range_self_univ, fderivWithin_univ]
  have hg₁ := factor_hasFDerivAt A₁ b.1 hb₁
  have hg₂ := factor_hasFDerivAt A₂ b.2 hb₂
  have hG : HasFDerivAt
      (fun w : ModelProd H4 H4 => (A₁.1.prod A₂.1) ((chartAt (ModelProd H4 H4) b).symm w))
      (((Work.TangentClasses.tangentBundle 𝓘(ℝ, H4) (CP 2)).coordChange (achart H4 b.1) A₁ b.1).prodMap
        ((Work.TangentClasses.tangentBundle 𝓘(ℝ, H4) (CP 2)).coordChange (achart H4 b.2) A₂ b.2))
      ((chartAt (ModelProd H4 H4) b) b) := by
    rw [show (chartAt (ModelProd H4 H4) b) = (chartAt H4 b.1).prod (chartAt H4 b.2) from
      prodChartedSpace_chartAt]
    have hfun : (fun w : ModelProd H4 H4 => (A₁.1.prod A₂.1)
          (((chartAt H4 b.1).prod (chartAt H4 b.2)).symm w))
        = Prod.map (fun v₁ : H4 => A₁.1 ((chartAt H4 b.1).symm v₁))
            (fun v₂ : H4 => A₂.1 ((chartAt H4 b.2).symm v₂)) := by
      funext w
      rw [OpenPartialHomeomorph.prod_symm]
      rfl
    rw [hfun]
    exact HasFDerivAt.prodMap ((chartAt H4 b.1 b.1), (chartAt H4 b.2 b.2)) hg₁ hg₂
  have h2 : fderiv ℝ (fun u : H8 => (prodLinEquiv 4 4)
          ((A₁.1.prod A₂.1) ((chartAt (ModelProd H4 H4) b).symm ((prodLinEquiv 4 4).symm u))))
        ((prodLinEquiv 4 4) ((chartAt (ModelProd H4 H4) b) b))
      = ((prodLinEquiv 4 4 : (H4 × H4) ≃L[ℝ] H8) : (H4 × H4) →L[ℝ] H8).comp
          ((((Work.TangentClasses.tangentBundle 𝓘(ℝ, H4) (CP 2)).coordChange
                (achart H4 b.1) A₁ b.1).prodMap
              ((Work.TangentClasses.tangentBundle 𝓘(ℝ, H4) (CP 2)).coordChange
                (achart H4 b.2) A₂ b.2)).comp
            (((prodLinEquiv 4 4 : (H4 × H4) ≃L[ℝ] H8)).symm : H8 →L[ℝ] (H4 × H4))) := by
    have hlin : HasFDerivAt (fun u : H8 => (prodLinEquiv 4 4).symm u)
        (((prodLinEquiv 4 4 : (H4 × H4) ≃L[ℝ] H8)).symm : H8 →L[ℝ] (H4 × H4))
        ((prodLinEquiv 4 4) ((chartAt (ModelProd H4 H4) b) b)) :=
      ContinuousLinearMap.hasFDerivAt
        (((prodLinEquiv 4 4 : (H4 × H4) ≃L[ℝ] H8)).symm : H8 →L[ℝ] (H4 × H4))
    have hcomp1 : HasFDerivAt
        ((fun w : ModelProd H4 H4 => (A₁.1.prod A₂.1) ((chartAt (ModelProd H4 H4) b).symm w)) ∘
          (fun u : H8 => (prodLinEquiv 4 4).symm u))
        ((((Work.TangentClasses.tangentBundle 𝓘(ℝ, H4) (CP 2)).coordChange (achart H4 b.1) A₁ b.1).prodMap
            ((Work.TangentClasses.tangentBundle 𝓘(ℝ, H4) (CP 2)).coordChange (achart H4 b.2) A₂ b.2)).comp
          (((prodLinEquiv 4 4 : (H4 × H4) ≃L[ℝ] H8)).symm : H8 →L[ℝ] (H4 × H4)))
        ((prodLinEquiv 4 4) ((chartAt (ModelProd H4 H4) b) b)) := by
      refine HasFDerivAt.comp ((prodLinEquiv 4 4) ((chartAt (ModelProd H4 H4) b) b)) ?_ hlin
      rw [show ((prodLinEquiv 4 4).symm ((prodLinEquiv 4 4) ((chartAt (ModelProd H4 H4) b) b)))
          = ((chartAt (ModelProd H4 H4) b) b) from
        ContinuousLinearEquiv.symm_apply_apply (prodLinEquiv 4 4) _]
      exact hG
    have hcomp2 : HasFDerivAt
        ((fun w : ModelProd H4 H4 => (prodLinEquiv 4 4) w) ∘
          ((fun w : ModelProd H4 H4 => (A₁.1.prod A₂.1) ((chartAt (ModelProd H4 H4) b).symm w)) ∘
            (fun u : H8 => (prodLinEquiv 4 4).symm u)))
        (((prodLinEquiv 4 4 : (H4 × H4) ≃L[ℝ] H8) : (H4 × H4) →L[ℝ] H8).comp
          ((((Work.TangentClasses.tangentBundle 𝓘(ℝ, H4) (CP 2)).coordChange (achart H4 b.1) A₁ b.1).prodMap
              ((Work.TangentClasses.tangentBundle 𝓘(ℝ, H4) (CP 2)).coordChange (achart H4 b.2) A₂ b.2)).comp
            (((prodLinEquiv 4 4 : (H4 × H4) ≃L[ℝ] H8)).symm : H8 →L[ℝ] (H4 × H4))))
        ((prodLinEquiv 4 4) ((chartAt (ModelProd H4 H4) b) b)) :=
      HasFDerivAt.comp _ (ContinuousLinearMap.hasFDerivAt
        ((prodLinEquiv 4 4 : (H4 × H4) ≃L[ℝ] H8) : (H4 × H4) →L[ℝ] H8)) hcomp1
    exact hcomp2.fderiv
  rw [h1, h2]

/-! ## The complexified statement -/

/-- The Whitney sum's preferred index at a point. -/
theorem whitney_indexAt (b : P2) :
    (Work.Whitney.whitneySum (factorTangentC ContinuousMap.fst)
        (factorTangentC ContinuousMap.snd)).indexAt b
      = (achart H4 b.1, achart H4 b.2) := rfl

/-- The cover of the Whitney sum, as a subset of `ℂP² × ℂP²`. -/
theorem whitney_baseSet (t : atlas H4 (CP 2) × atlas H4 (CP 2)) :
    (Work.Whitney.whitneySum (factorTangentC ContinuousMap.fst)
        (factorTangentC ContinuousMap.snd)).baseSet t
      = t.1.1.source ×ˢ t.2.1.source := rfl

/-- **The complexified chain rule**: the transition function of `cp2cp2TangentC` in the preferred
chart at `b`, to the (pushed) product chart `pushIdx t`, is the transition function of the Whitney
sum of the two factors in the preferred chart at `b`, to `t`. -/
theorem complexifiedPushCoordChange (t : atlas H4 (CP 2) × atlas H4 (CP 2)) (b : P2)
    (hb : b ∈ (Work.Whitney.whitneySum (factorTangentC ContinuousMap.fst)
        (factorTangentC ContinuousMap.snd)).baseSet t) :
    cp2cp2TangentC.coordChange (achart H8 b) (pushIdx t) b
      = (Work.Whitney.whitneySum (factorTangentC ContinuousMap.fst)
          (factorTangentC ContinuousMap.snd)).coordChange ((achart H4 b.1), (achart H4 b.2)) t b := by
  have hb' : b ∈ (pushIdx t).1.source := by
    rw [pushIdx_source, Set.mem_prod]
    rw [whitney_baseSet, Set.mem_prod] at hb
    exact hb
  apply ContinuousLinearMap.ext
  intro v
  rw [show cp2cp2TangentC.coordChange (achart H8 b) (pushIdx t) b v
      = Work.Thom.cxTrans ((Work.TangentClasses.tangentBundle 𝓘(ℝ, H8) P2).coordChange
          (achart H8 b) (pushIdx t) b) v from rfl]
  rw [pushTangentCoordChange t.1 t.2 b hb']
  rw [show ((prodLinEquiv 4 4 : (H4 × H4) ≃L[ℝ] H8) : (H4 × H4) →L[ℝ] H8).comp
        ((((Work.TangentClasses.tangentBundle 𝓘(ℝ, H4) (CP 2)).coordChange
              (achart H4 b.1) t.1 b.1).prodMap
            ((Work.TangentClasses.tangentBundle 𝓘(ℝ, H4) (CP 2)).coordChange
              (achart H4 b.2) t.2 b.2)).comp
          (((prodLinEquiv 4 4 : (H4 × H4) ≃L[ℝ] H8)).symm : H8 →L[ℝ] (H4 × H4)))
      = Work.Whitney.transportEnd (Work.Whitney.sumFibreR 4 4)
          ((Work.TangentClasses.tangentBundle 𝓘(ℝ, H4) (CP 2)).coordChange (achart H4 b.1) t.1 b.1)
          ((Work.TangentClasses.tangentBundle 𝓘(ℝ, H4) (CP 2)).coordChange (achart H4 b.2) t.2 b.2)
      from rfl]
  rw [Work.Whitney.sumFibre_cxTrans]
  rw [show (Work.Whitney.whitneySum (factorTangentC ContinuousMap.fst)
        (factorTangentC ContinuousMap.snd)).coordChange ((achart H4 b.1), (achart H4 b.2)) t b v
      = (Work.Whitney.sumFibreC 4 4)
          (((Work.Thom.cxTrans ((Work.TangentClasses.tangentBundle 𝓘(ℝ, H4) (CP 2)).coordChange
                (achart H4 b.1) t.1 b.1)).prodMap
              (Work.Thom.cxTrans ((Work.TangentClasses.tangentBundle 𝓘(ℝ, H4) (CP 2)).coordChange
                (achart H4 b.2) t.2 b.2)))
            ((Work.Whitney.sumFibreC 4 4).symm v)) from rfl]
  rw [show Work.Whitney.transportEnd (Work.Whitney.sumFibreC 4 4)
        (Work.Thom.cxTrans ((Work.TangentClasses.tangentBundle 𝓘(ℝ, H4) (CP 2)).coordChange
          (achart H4 b.1) t.1 b.1))
        (Work.Thom.cxTrans ((Work.TangentClasses.tangentBundle 𝓘(ℝ, H4) (CP 2)).coordChange
          (achart H4 b.2) t.2 b.2)) v
      = (Work.Whitney.sumFibreC 4 4)
          (((Work.Thom.cxTrans ((Work.TangentClasses.tangentBundle 𝓘(ℝ, H4) (CP 2)).coordChange
                (achart H4 b.1) t.1 b.1)).prodMap
              (Work.Thom.cxTrans ((Work.TangentClasses.tangentBundle 𝓘(ℝ, H4) (CP 2)).coordChange
                (achart H4 b.2) t.2 b.2)))
            ((Work.Whitney.sumFibreC 4 4).symm v)) from rfl]

/-! ## The splitting -/

theorem cp2cp2TangentC_baseSet (i : atlas H8 P2) : cp2cp2TangentC.baseSet i = i.1.source := rfl

theorem cp2cp2TangentSplits : Work.Gen.Cp2Cp2TangentSplits := by
  have hbase : ∀ t : atlas H4 (CP 2) × atlas H4 (CP 2),
      (Work.Whitney.whitneySum (factorTangentC ContinuousMap.fst)
        (factorTangentC ContinuousMap.snd)).baseSet t ⊆ cp2cp2TangentC.baseSet (pushIdx t) := by
    intro t
    rw [whitney_baseSet, cp2cp2TangentC_baseSet, pushIdx_source]
  have hconj : ∀ (t : atlas H4 (CP 2) × atlas H4 (CP 2)) (b : P2),
      b ∈ (Work.Whitney.whitneySum (factorTangentC ContinuousMap.fst)
        (factorTangentC ContinuousMap.snd)).baseSet t →
      (cp2cp2TangentC.coordChange (cp2cp2TangentC.indexAt b) (pushIdx t) b).comp
          ((ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin 8))).symm :
            EuclideanSpace ℂ (Fin (4 + 4)) →L[ℂ] EuclideanSpace ℂ (Fin 8))
        = ((ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin 8))).symm :
            EuclideanSpace ℂ (Fin (4 + 4)) →L[ℂ] EuclideanSpace ℂ (Fin 8)).comp
          ((Work.Whitney.whitneySum (factorTangentC ContinuousMap.fst)
            (factorTangentC ContinuousMap.snd)).coordChange
              ((Work.Whitney.whitneySum (factorTangentC ContinuousMap.fst)
                (factorTangentC ContinuousMap.snd)).indexAt b) t b) := by
    intro t b hb
    rw [show cp2cp2TangentC.indexAt b = achart H8 b from rfl, whitney_indexAt]
    rw [complexifiedPushCoordChange t b hb]
    ext v
    simp
  exact ⟨(nonempty_bundleIso_of_oneSidedMatch cp2cp2TangentC
    (Work.Whitney.whitneySum (factorTangentC ContinuousMap.fst) (factorTangentC ContinuousMap.snd))
    (ContinuousLinearEquiv.refl ℂ (EuclideanSpace ℂ (Fin 8))) pushIdx hbase hconj).some⟩
