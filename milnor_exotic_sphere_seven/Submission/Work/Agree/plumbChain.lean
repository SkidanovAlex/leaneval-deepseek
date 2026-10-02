import Mathlib
import Submission.Work.Agree.mapFibreIso
import Submission.Work.Agree.plumb
import Submission.Work.Agree.modelTransfer
import Submission.Work.Agree.tangentRestriction
import Submission.Work.Agree.geometryB
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.nonempty_bundleIso_whitneySum_comm
import Submission.Work.Gen.EulerToolkit
import Submission.Work.Gen.TangentPresentation
import Submission.Work.Gen.cp4ChernPresentation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `restrictedC2` computed by the plumbing of `D(ξ)`: the geometric half of `GeomSplitting`

`Work.Agree.restrictedC2 F hF` is the second Chern class of the pullback to the disc bundle
`D(ξ) = Vk (-2)` of the canonical four-step presentation of the complexified tangent bundle of
`X = D(ξ) ∪_F D⁸`.

This file proves that it equals the second Chern class of the complexification of the pullback along
the bundle projection `π : D(ξ) → S⁴` of the Whitney sum `TS⁴ ⊕ ξ` of the two-chart bundles
`L¹R¹ = clutchBundle 1 1` and `L²R⁻¹ = clutchBundle 2 (-1)`.

The chain is

* **rank normalisation / plumbing**: the change of fibre `Work.Thom.modelLinearEquiv` — the
  replacement of the tangent-space fibre `ℝ⁸` of the four-step presentation by
  `EuclideanSpace ℝ (Fin (finrank ℝ ℝ⁸))` — does not change the Chern class
  (`Work.Gen.chernClass_complexificationCore_mapFibre`);
* **model transfer**: the tangent bundle of `X` in the `ℝ⁸`-charting is the `vkModelIso`-transport
  of the tangent bundle in the `MSpace8`-charting of the glueing (`Work.Agree.modelTransfer`);
* **tangent restriction**: the pullback of `TX` along the inclusion of the disc bundle is the
  tangent bundle of the disc bundle (`Work.Agree.tangentRestriction`);
* **Geometry B**: `T D(ξ) ≅ π^*(TS⁴ ⊕ ξ)` (`hB`);
* **the two-chart presentation**: `L¹R¹ ⊞ L²R⁻¹ = sum (clutchBundle 1 1) (clutchBundle 2 (-1))`
  and `whitneySumR (clutchBundle 1 1) (clutchBundle 2 (-1))` are the same bundle up to the fibre
  identification `sumFibreR 4 4`.

All identifications are `BundleIso`s, and `Work.Thom.chernClass` is isomorphism-invariant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Topology
open Work.TangentClasses

namespace Work.Agree

noncomputable section

/-! ## Tooling: reindexing, the fibre of a sum, and the complexification of an isomorphism -/

/-- **`mapFibre` commutes with the reindexing of the cover.**  The proof is `rfl`, but the two sides
have different fibres (`F'` versus `EuclideanSpace ℝ (Fin l)`), which is what the fine covers below
need. -/
theorem plumbReindex_mapFibre_gen {B : Type} [TopologicalSpace B] {F F' : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F'] {ι ι' : Type}
    (Z : RealBundle B F ι) (e : F ≃L[ℝ] F') (σ : ι' → ι)
    (hσ : ∀ x : B, ∃ i, x ∈ Z.baseSet (σ i)) :
    RealBundle.reindex (RealBundle.mapFibre e Z) σ hσ
      = RealBundle.mapFibre e (RealBundle.reindex Z σ hσ) := rfl

/-- **The `Whitney`-sum presentation of `Z₁ ⊕ Z₂` is the fibre-change of the block-diagonal
presentation `Z₁.sum Z₂`** along the splitting `Work.Whitney.sumFibreR`. -/
theorem plumbMapFibre_sumFibreR_sum {B : Type} [TopologicalSpace B] {k₁ k₂ : ℕ} {ι₁ ι₂ : Type}
    (Z₁ : RealBundle B (EuclideanSpace ℝ (Fin k₁)) ι₁)
    (Z₂ : RealBundle B (EuclideanSpace ℝ (Fin k₂)) ι₂) :
    RealBundle.mapFibre (Work.Whitney.sumFibreR k₁ k₂) (RealBundle.sum Z₁ Z₂)
      = Work.Whitney.whitneySumR Z₁ Z₂ := by
  refine Work.Thom.bundleCore_ext rfl rfl (fun p q x => ?_)
  rw [RealBundle.mapFibre_coordChange, Work.Whitney.whitneySumR_coordChange,
    RealBundle.sum_coordChange]

/-- **The complexification of a real bundle isomorphism**: the gauge `b ↦ cxTrans (e.clmGen b)`.
This is `Work.Thom.nonempty_complexificationCore_bundleIso` without the stabilisation, for two real
standard-fibre bundles of the *same* rank. -/
theorem plumbComplexificationIso {k : ℕ} {B : Type} [TopologicalSpace B]
    {ι ι' : Type}
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι)
    (Z' : RealBundle B (EuclideanSpace ℝ (Fin k)) ι')
    (e : Work.Thom.BundleIso Z Z') :
    Nonempty (Work.Thom.BundleIso (Work.Thom.complexificationCore Z)
      (Work.Thom.complexificationCore Z')) := by
  refine ⟨{ hom := fun b => (Work.Thom.cxTrans (e.clmGen b)).toLinearMap
            inv := fun b => (Work.Thom.cxTrans (e.symm.clmGen b)).toLinearMap
            left_inv := ?_
            right_inv := ?_
            continuous_hom := ?_
            continuous_inv := ?_ }⟩
  · intro b x
    show Work.Thom.cxTrans (e.symm.clmGen b) (Work.Thom.cxTrans (e.clmGen b) x) = x
    rw [← ContinuousLinearMap.comp_apply, ← Work.Thom.cxTrans_comp]
    have hcomp : (e.symm.clmGen b).comp (e.clmGen b) = 1 := by
      apply ContinuousLinearMap.ext
      intro z
      rw [ContinuousLinearMap.comp_apply, Work.Thom.BundleIso.clmGen_apply,
        Work.Thom.BundleIso.clmGen_apply]
      exact e.left_inv b z
    rw [hcomp, Work.Thom.cxTrans_one]
    rfl
  · intro b y
    show Work.Thom.cxTrans (e.clmGen b) (Work.Thom.cxTrans (e.symm.clmGen b) y) = y
    rw [← ContinuousLinearMap.comp_apply, ← Work.Thom.cxTrans_comp]
    have hcomp : (e.clmGen b).comp (e.symm.clmGen b) = 1 := by
      apply ContinuousLinearMap.ext
      intro z
      rw [ContinuousLinearMap.comp_apply, Work.Thom.BundleIso.clmGen_apply,
        Work.Thom.BundleIso.clmGen_apply]
      exact e.right_inv b z
    rw [hcomp, Work.Thom.cxTrans_one]
    rfl
  · refine Work.Thom.continuous_totalSpaceMap_clm (Work.Thom.complexificationCore Z)
      (Work.Thom.complexificationCore Z') (ContinuousMap.id B)
      (fun b => Work.Thom.cxTrans (e.clmGen b)) ?_
    intro i₁ i₂
    refine (Work.Thom.continuousOn_cxTrans_chartExpression Z Z' e i₁ i₂).congr
      (fun b hb => ?_)
    simp only [ContinuousMap.id_apply, Work.Thom.complexificationCore_indexAt]
    rw [Work.Thom.complexificationCore_coordChange_clm Z i₁ _ b,
      Work.Thom.complexificationCore_coordChange_clm Z' _ i₂ b]
    rw [← Work.Thom.cxTrans_comp, ← Work.Thom.cxTrans_comp]
  · refine Work.Thom.continuous_totalSpaceMap_clm (Work.Thom.complexificationCore Z')
      (Work.Thom.complexificationCore Z) (ContinuousMap.id B)
      (fun b => Work.Thom.cxTrans (e.symm.clmGen b)) ?_
    intro i₁ i₂
    refine (Work.Thom.continuousOn_cxTrans_chartExpression Z' Z e.symm i₁ i₂).congr
      (fun b hb => ?_)
    simp only [ContinuousMap.id_apply, Work.Thom.complexificationCore_indexAt]
    rw [Work.Thom.complexificationCore_coordChange_clm Z _ i₂ b,
      Work.Thom.complexificationCore_coordChange_clm Z' i₁ _ b]
    rw [← Work.Thom.cxTrans_comp, ← Work.Thom.cxTrans_comp]

/-- **Isomorphic real standard-fibre bundles have complexifications with equal Chern classes.** -/
theorem plumbChernClassIso {k : ℕ} {B : Type} [TopologicalSpace B]
    {ι ι' : Type} [Fintype ι] [Fintype ι']
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι)
    (Z' : RealBundle B (EuclideanSpace ℝ (Fin k)) ι')
    (e : Work.Thom.BundleIso Z Z') (j : ℕ) :
    Work.Thom.chernClass k j (Work.Thom.complexificationCore Z)
      = Work.Thom.chernClass k j (Work.Thom.complexificationCore Z') := by
  obtain ⟨e'⟩ := plumbComplexificationIso Z Z' e
  exact Work.Thom.chernClass_BundleIso (j := j) _ _ e'

/-- **The two-chart cover `vkCover` covers the disc bundle.**  The two charts are the charts of the
glueing at the two distinguished points; their sources are the images of the two pieces of `Vk`. -/
theorem plumbVkCover_cover : ∀ x : Vk, ∃ i : Fin 2,
    x ∈ (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk).baseSet (vkCover i) := by
  intro x
  have hx : x ∈ Set.range (Submission.Milnor.vData (-2)).ιX ∪
      Set.range (Submission.Milnor.vData (-2)).ιY := by
    rw [Submission.Glue.Data.range_ιX_union_range_ιY]
    trivial
  rcases hx with hx | hx
  · exact ⟨0, by rw [Work.TangentClasses.tangentBundle_baseSet, vkCover_zero_source]; exact hx⟩
  · exact ⟨1, by rw [Work.TangentClasses.tangentBundle_baseSet, vkCover_one_source]; exact hx⟩

/-! ## The target -/

theorem plumbChain (hB : Work.Agree.GeometryB)
    (F : Submission.Milnor.Mk (-2) → Work.Milnor.Sph8) (hF : Work.Milnor.IsCappingDiffeo F) :
    Work.Agree.restrictedC2 F hF
      = Work.Thom.chernClass 8 2 (Work.Thom.complexificationCore
          (Work.Thom.bundleComap
            (Work.Whitney.whitneySumR (Work.Agree.clutchBundle (1 : ℤ) 1)
              (Work.Agree.clutchBundle (2 : ℤ) (-1)))
            Work.TangentClasses.discProj)) := by
  letI := Work.Milnor.cappedChartedSpace (Work.Milnor.cappedDatum F hF)
  letI : IsManifold Work.Milnor.mE8 1
      (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)) :=
    (Work.Milnor.capped_isManifold (Work.Milnor.cappedDatum F hF)).of_le (by simp)
  letI : CompactSpace (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)) :=
    Work.Milnor.isCompact_capped F hF
  have hcov : ∀ x : Vk, ∃ i : Fin 2,
      x ∈ (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk).baseSet (vkCover i) :=
    plumbVkCover_cover
  -- **Step A**: the rank normalisation and the plumbing of the canonical presentation.
  have hA : Work.Agree.restrictedC2 F hF = Work.Thom.chernClass 8 2
      (Work.Thom.complexificationCore
        (RealBundle.reindex (Work.Thom.bundleComap
            (Work.TangentClasses.tangentBundle Work.Milnor.mE8
              (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
            (Work.Agree.incl F hF)) (Work.Thom.chartCover (H := EuclideanSpace ℝ (Fin 8))
              (M := Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
            (fun x => Work.Thom.chartCover_reindex_cover Work.Milnor.mE8
              (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))
              (Work.Agree.incl F hF x)))) := by
    rw [show Work.Agree.restrictedC2 F hF =
        Work.Thom.chernClass (Module.finrank ℝ (EuclideanSpace ℝ (Fin 8))) 2
          (Work.Thom.bundleComap (Work.Thom.complexifiedTangentBundleFinite Work.Milnor.mE8
            (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
            (Work.Agree.incl F hF)) from rfl]
    simp only [Work.Thom.complexifiedTangentBundleFinite]
    rw [plumbReindex_mapFibre_gen]
    rw [← Work.Thom.complexificationCore_bundleComap]
    rw [← Work.Agree.mapFibre_bundleComap]
    rw [Work.Agree.bundleComap_reindex]
    exact Work.Gen.chernClass_complexificationCore_mapFibre (k := 8)
      (l := Module.finrank ℝ (EuclideanSpace ℝ (Fin 8))) finrank_euclideanSpace_fin _ _ 2
  -- **Step B**: presenting the restricted tangent bundle over the two-chart cover of the disc
  -- bundle, via model transfer, the tangent restriction and Geometry B.
  have hB' : Work.Thom.chernClass 8 2
      (Work.Thom.complexificationCore
        (RealBundle.reindex (Work.Thom.bundleComap
            (Work.TangentClasses.tangentBundle Work.Milnor.mE8
              (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
            (Work.Agree.incl F hF)) (Work.Thom.chartCover (H := EuclideanSpace ℝ (Fin 8))
              (M := Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
            (fun x => Work.Thom.chartCover_reindex_cover Work.Milnor.mE8
              (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))
              (Work.Agree.incl F hF x)))) =
      Work.Thom.chernClass 8 2 (Work.Thom.complexificationCore
        (RealBundle.mapFibre Work.Milnor.vkModelIso (vkTangent hcov))) := by
    obtain ⟨eA⟩ := Work.Agree.nonempty_bundleIso_reindexCore_self
      (Work.Thom.bundleComap (Work.TangentClasses.tangentBundle Work.Milnor.mE8
        (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))) (Work.Agree.incl F hF))
      (Work.Thom.chartCover (H := EuclideanSpace ℝ (Fin 8))
        (M := Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)))
      (fun x => Work.Thom.chartCover_reindex_cover Work.Milnor.mE8
        (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF)) (Work.Agree.incl F hF x))
    obtain ⟨eMT⟩ := Work.Agree.modelTransfer F hF
    obtain ⟨eC0⟩ := Work.Thom.BundleIso_comap_exists
      (RealBundle.mapFibre Work.Milnor.vkModelIso
        (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8
          (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))))
      (Work.TangentClasses.tangentBundle Work.Milnor.mE8
        (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))) eMT (Work.Agree.incl F hF)
    rw [← Work.Agree.mapFibre_bundleComap] at eC0
    obtain ⟨eTR⟩ := Work.Agree.tangentRestriction F hF
    obtain ⟨eC1⟩ := Work.Agree.nonempty_bundleIso_mapFibre_of_iso
      (Work.Thom.bundleComap (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8
        (Work.Milnor.cappedSpace (Work.Milnor.cappedDatum F hF))) (Work.Agree.incl F hF))
      (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk)
      Work.Milnor.vkModelIso Work.Milnor.vkModelIso ⟨eTR⟩
    obtain ⟨eD0⟩ := Work.Agree.nonempty_bundleIso_reindexCore_self
      (RealBundle.mapFibre Work.Milnor.vkModelIso
        (Work.TangentClasses.tangentBundle Work.Milnor.mMSpace8 Vk)) vkCover hcov
    exact plumbChernClassIso _ _
      (eA.trans (eC0.symm.trans (eC1.trans eD0.symm))) 2
  -- **Step C**: the two-chart presentation `L¹R¹ ⊞ L²R⁻¹` of the Whitney sum.
  have hC : Work.Thom.chernClass 8 2 (Work.Thom.complexificationCore
        (RealBundle.mapFibre Work.Milnor.vkModelIso (vkTangent hcov))) =
      Work.Thom.chernClass 8 2 (Work.Thom.complexificationCore
          (Work.Thom.bundleComap
            (Work.Whitney.whitneySumR (Work.Agree.clutchBundle (1 : ℤ) 1)
              (Work.Agree.clutchBundle (2 : ℤ) (-1)))
            Work.TangentClasses.discProj)) := by
    obtain ⟨eG⟩ := hB hcov
    obtain ⟨ePI0⟩ := Work.Agree.nonempty_bundleIso_mapFibre_of_iso (vkTangent hcov)
      (Work.Thom.bundleComap (RealBundle.sum (Work.Agree.clutchBundle (1 : ℤ) 1)
        (Work.Agree.clutchBundle (2 : ℤ) (-1))) Work.TangentClasses.discProj)
      Work.Milnor.vkModelIso (Work.Whitney.sumFibreR 4 4) ⟨eG⟩
    rw [plumbChernClassIso _ _ ePI0 2]
    rw [Work.Agree.mapFibre_bundleComap, plumbMapFibre_sumFibreR_sum]
  exact hA.trans (hB'.trans hC)

end

end Work.Agree
