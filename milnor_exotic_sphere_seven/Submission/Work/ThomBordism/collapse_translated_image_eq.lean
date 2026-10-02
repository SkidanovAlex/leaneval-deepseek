import Mathlib
import Submission.Work.ThomBordism.collapseM4Defs
import Submission.Work.ThomBordism.blowPsi
import Submission.Work.ThomBordism.cla_uniformity
import Submission.Work.ThomBordism.eucSliceClass_existsV2

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

theorem collapse_translated_image_eq {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (σ : Work.Thom.RelCoh ℤ (8 + k) (OnePoint (Work.Tubular.Euc (8 + k)))
      ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
        Set (OnePoint (Work.Tubular.Euc (8 + k)))))
    (hσ : (Work.Thom.relCohMap (⟨OnePoint.some, OnePoint.continuous_coe⟩ :
        C(Work.Tubular.Euc (8 + k), OnePoint (Work.Tubular.Euc (8 + k))))
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
        ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ)
        (Work.ThomBordism.eucInclV2_mem (8 + k)) ℤ (8 + k)).hom σ
      = Work.ThomBordism.stdModelGen (8 + k)) :
    (Work.Thom.relCohMap (Work.ThomBordism.someOpen E C)
        (Work.ThomBordism.openTubePtset E C x)
        ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))
        (Work.ThomBordism.someOpen_mem E C x) ℤ (8 + k)).hom
      ((Work.Thom.relCohMap (Work.ThomBordism.transT (-(E.e x)))
        ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))
        ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ)
        (Work.ThomBordism.transT_pair (E.e x)) ℤ (8 + k)).hom σ)
      = (Work.Thom.relCohMap (Work.ThomBordism.openTubeIncl E C)
          (Work.ThomBordism.openTubePtset E C x)
          (Work.ThomBordism.tubePtSet E C x) (fun y hy => hy) ℤ (8 + k)).hom
          (Work.ThomBordism.tubeTransModel E C x) := by
  have hσ' : (Work.Thom.relCohMap (Work.ThomBordism.eucInclV2 (8 + k))
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
      ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ)
      (Work.ThomBordism.eucInclV2_mem (8 + k)) ℤ (8 + k)).hom σ
      = Work.ThomBordism.stdModelGen (8 + k) := hσ
  have hcomp : (Work.ThomBordism.transT (-(E.e x))).comp (Work.ThomBordism.someOpen E C)
      = (Work.ThomBordism.eucInclV2 (8 + k)).comp
          ((Work.ThomBordism.tubeTransMap E C x).comp (Work.ThomBordism.openTubeIncl E C)) := by
    apply ContinuousMap.ext
    intro y
    rfl
  have hA : ∀ y ∈ Work.ThomBordism.openTubePtset E C x,
      ((Work.ThomBordism.tubeTransMap E C x).comp (Work.ThomBordism.openTubeIncl E C)) y ∈
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) := by
    intro y hy
    rw [show ((Work.ThomBordism.tubeTransMap E C x).comp (Work.ThomBordism.openTubeIncl E C)) y
          = (y.1 : Work.Tubular.Euc (8 + k)) - E.e x from rfl]
    exact sub_ne_zero.mpr (by simpa [Work.ThomBordism.openTubePtset] using hy)
  have hgf1 : ∀ y ∈ Work.ThomBordism.openTubePtset E C x,
      ((Work.ThomBordism.transT (-(E.e x))).comp (Work.ThomBordism.someOpen E C)) y ∈
        ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
          Set (OnePoint (Work.Tubular.Euc (8 + k)))) :=
    fun y hy => Work.ThomBordism.transT_pair (E.e x) (Work.ThomBordism.someOpen E C y)
      (Work.ThomBordism.someOpen_mem E C x y hy)
  have hgf2 : ∀ y ∈ Work.ThomBordism.openTubePtset E C x,
      ((Work.ThomBordism.eucInclV2 (8 + k)).comp
        ((Work.ThomBordism.tubeTransMap E C x).comp (Work.ThomBordism.openTubeIncl E C))) y ∈
        ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
          Set (OnePoint (Work.Tubular.Euc (8 + k)))) :=
    fun y hy => Work.ThomBordism.eucInclV2_mem (8 + k) _ (hA y hy)
  have hgf3 : ∀ y ∈ Work.ThomBordism.openTubePtset E C x,
      ((Work.ThomBordism.tubeTransMap E C x).comp (Work.ThomBordism.openTubeIncl E C)) y ∈
        ({0}ᶜ : Set (Work.Tubular.Euc (8 + k))) :=
    fun y hy => Work.ThomBordism.tubeTransMap_mem E C x
      (Work.ThomBordism.openTubeIncl E C y) hy
  rw [Work.Thom.relCohMap_compA_apply (Work.ThomBordism.openTubePtset E C x)
      ({OnePoint.some (E.e x)}ᶜ : Set (OnePoint (Work.Tubular.Euc (8 + k))))
      ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
        Set (OnePoint (Work.Tubular.Euc (8 + k))))
      (Work.ThomBordism.someOpen E C) (Work.ThomBordism.transT (-(E.e x)))
      (Work.ThomBordism.someOpen_mem E C x) (Work.ThomBordism.transT_pair (E.e x))
      hgf1 ℤ (8 + k) σ]
  rw [Work.Thom.relCohMap_congrA (Work.ThomBordism.openTubePtset E C x)
      ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
        Set (OnePoint (Work.Tubular.Euc (8 + k)))) hcomp hgf1 hgf2 ℤ (8 + k)]
  rw [← Work.Thom.relCohMap_compA_apply (Work.ThomBordism.openTubePtset E C x)
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
      ({OnePoint.some (0 : Work.Tubular.Euc (8 + k))}ᶜ :
        Set (OnePoint (Work.Tubular.Euc (8 + k))))
      ((Work.ThomBordism.tubeTransMap E C x).comp (Work.ThomBordism.openTubeIncl E C))
      (Work.ThomBordism.eucInclV2 (8 + k))
      hA (Work.ThomBordism.eucInclV2_mem (8 + k)) hgf2 ℤ (8 + k) σ]
  rw [hσ']
  unfold Work.ThomBordism.tubeTransModel
  rw [Work.Thom.relCohMap_compA_apply (Work.ThomBordism.openTubePtset E C x)
      (Work.ThomBordism.tubePtSet E C x)
      ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
      (Work.ThomBordism.openTubeIncl E C) (Work.ThomBordism.tubeTransMap E C x)
      (fun y hy => hy) (Work.ThomBordism.tubeTransMap_mem E C x) hgf3 ℤ (8 + k)
      (Work.ThomBordism.stdModelGen (8 + k))]

end Work.ThomBordism
