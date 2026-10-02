import Mathlib
import Submission.Work.ThomBordism.collapseM4Defs
import Submission.Work.ThomBordism.collapse_translated_image_eq
import Submission.Work.ThomBordism.blowPsiStage_one_relCohMap_eq_incl_fine
import Submission.Work.ThomBordism.someOpen_relCohMap_injective
import Submission.Work.ThomBordism.collapse_image_eq_tubeModel
import Submission.Work.ThomBordism.valuePmOneV2Defs
import Submission.Work.ThomBordism.chartModelClassDefs
import Submission.Work.Tubular.ThomComparison
import Submission.Work.Tubular.ThomRepOfLocalDegree
import Submission.Work.Thom.Cohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

/-!
# The dictionary step (M4) of `collapseLocalisation_ambientV2`

Assembles the three proved pieces:
* `Work.ThomBordism.collapse_image_eq_tubeModel` (the collapse's local form),
* `Work.ThomBordism.collapse_translated_image_eq` (the translate of the model class),
* the fine homotopy (F1) `Work.ThomBordism.blowPsiStage_one_relCohMap_eq_incl_fine`,
* and the injectivity `Work.ThomBordism.someOpen_relCohMap_injective` of the restriction to the open
  tube,
into the identity

  `g^*(βf) = (T_{-(E.e x)})^*σ`   in `H^{8+k}(S^{8+k}, S^{8+k}∖{some (E.e x)})`,
-/

namespace Work.ThomBordism

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **THE DICTIONARY STEP (M4)**, at the internal degree `8 + k`. -/
theorem collapse_pullback_eq_translated_8k
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube →
      g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
    {R : ℝ} (hR : 0 ≤ R) (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R) (x : V.pt)
    (β : Work.Thom.RelCoh ℤ (8 + k) (OnePoint (Work.Tubular.NormalTotal E))
      (Work.Tubular.onePointNonzero E))
    (hβ : Work.Tubular.compPull E (8 + k) β
      = chartModelClass E C x (continuous_chartAffine_cap E C x))
    (βf : Work.Thom.RelCoh ℤ (8 + k) (OnePoint (Work.Tubular.NormalTotal E))
      ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E))))
    (hβf : (Work.Thom.relCohMap (ContinuousMap.id (OnePoint (Work.Tubular.NormalTotal E)))
        (Work.Tubular.onePointNonzero E)
        ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
        (fun y hy => fun hcon => zeroSectionPunctPt_notMem E x (hcon ▸ hy)) ℤ (8 + k)).hom βf
      = β)
    (σ : Work.Thom.RelCoh ℤ (8 + k) (OnePoint (Work.Tubular.Euc (8 + k)))
      ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
        Set (OnePoint (Work.Tubular.Euc (8 + k)))))
    (hσ : (Work.Thom.relCohMap (⟨OnePoint.some, OnePoint.continuous_coe⟩ :
        C(Work.Tubular.Euc (8 + k), OnePoint (Work.Tubular.Euc (8 + k))))
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
        ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ)
        (eucInclV2_mem (8 + k)) ℤ (8 + k)).hom σ
      = stdModelGen (8 + k)) :
    (Work.Thom.relCohMap g
        ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))
        ({Work.Tubular.zeroSectionPunctPt E x}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))
        (collapse_g_mem_fine E C x g hg hg2 hR hbox) ℤ (8 + k)).hom βf
      = (Work.Thom.relCohMap (transT (-(E.e x)))
          ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))
          ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ)
          (transT_pair (E.e x)) ℤ (8 + k)).hom σ := by
  refine someOpen_relCohMap_injective E C x (8 + k) ?_
  have hL := collapse_image_eq_tubeModel E C g hg hg2 hR hbox x β hβ βf hβf
  have hRc := collapse_translated_image_eq E C x σ hσ
  have hF1 := blowPsiStage_one_relCohMap_eq_incl_fine E C x (8 + k)
    (blowPsiStage_mem_fine E C x)
  rw [hL, hF1, hRc]

end

end Work.ThomBordism
