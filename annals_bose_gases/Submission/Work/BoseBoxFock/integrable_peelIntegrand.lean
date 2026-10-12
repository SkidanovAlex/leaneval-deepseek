import Mathlib.CategoryTheory.Countable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.imagesFibre
import Submission.Work.BoseBoxFock.imgKernel_integrable_boxL
import Submission.Work.BoseBoxFock.pairGc23Aux
import Submission.Work.BoseBoxFock.sliceDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseBoxFock

theorem integrable_peelIntegrand {n : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWi : MeasureTheory.Integrable W)
    (hR : 0 ≤ R) (hRℓ : R ≤ ℓ / 2)
    (hWs : ∀ u : EuclideanSpace ℝ (Fin 3), R ≤ ‖u‖ → W u = 0)
    {F G : Submission.BoseGases.X n → ℝ} (hF : Continuous F) (hG : Continuous G)
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hFb : ∀ x ∈ Submission.BoseGases.abox n ℓ, |F x| ≤ B₁)
    (hGb : ∀ x ∈ Submission.BoseGases.abox n ℓ, |G x| ≤ B₂) :
    MeasureTheory.Integrable
      (fun w : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) ×
          (Work.BoseBoxFock.pairFib23 n p → EuclideanSpace ℝ (Fin 3)) =>
        F (Work.BoseBoxFock.insertCoord2 p w.1.1 w.1.2 w.2)
          * G (Work.BoseBoxFock.insertCoord2 p w.1.1 w.1.2 w.2)
          * Work.BoseBoxFock.imgKernel ℓ W w.1.1 w.1.2)
      (((Work.BoseBoxFock.boxMeas ℓ).prod (Work.BoseBoxFock.boxMeas ℓ)).prod
        (MeasureTheory.Measure.pi (fun _ : Work.BoseBoxFock.pairFib23 n p =>
          Work.BoseBoxFock.boxMeas ℓ))) := by
  classical
  set ι := Work.BoseBoxFock.pairFib23 n p with hι
  -- #### basic facts about the box
  have hboxL : Work.BoseK15.corpusBox.boxL ℓ = Submission.BoseGases.acube ℓ :=
    corpusBox_boxL_eq_acube hℓ
  have hboxL_meas : MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ) := by
    rw [hboxL]
    exact Submission.BoseGases.acube_measurable ℓ
  have hboxL_fin : (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (Work.BoseK15.corpusBox.boxL ℓ) < ⊤ := by
    rw [hboxL]
    exact (Submission.BoseGases.acube_compact hℓ).measure_lt_top
  haveI hfact : Fact ((volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (Work.BoseK15.corpusBox.boxL ℓ) < ⊤) := ⟨hboxL_fin⟩
  haveI hfin : IsFiniteMeasure (Work.BoseBoxFock.boxMeas ℓ) := inferInstance
  have hboxPi_meas : MeasurableSet (boxPiSet ι ℓ) :=
    (isCompact_boxPiSet (ι := ι) hℓ).isClosed.measurableSet
  -- #### almost-everywhere membership in the boxes
  have hmem1 : ∀ᵐ a ∂(Work.BoseBoxFock.boxMeas ℓ), a ∈ Work.BoseK15.corpusBox.boxL ℓ :=
    MeasureTheory.ae_restrict_mem hboxL_meas
  have hmem2 : ∀ᵐ y ∂(MeasureTheory.Measure.pi (fun _ : ι => Work.BoseBoxFock.boxMeas ℓ)),
      y ∈ boxPiSet ι ℓ := by
    rw [← restrict_boxPiSet_eq (ι := ι) (ℓ := ℓ)]
    exact MeasureTheory.ae_restrict_mem hboxPi_meas
  have hmem12 : ∀ᵐ z ∂((Work.BoseBoxFock.boxMeas ℓ).prod (Work.BoseBoxFock.boxMeas ℓ)),
      z.1 ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ z.2 ∈ Work.BoseK15.corpusBox.boxL ℓ := by
    refine (MeasureTheory.Measure.ae_prod_iff_ae_ae ?_).2 ?_
    · exact (hboxL_meas.preimage measurable_fst).inter (hboxL_meas.preimage measurable_snd)
    · exact hmem1.mono fun a ha => hmem1.mono fun b hb => ⟨ha, hb⟩
  have hmem : ∀ᵐ w ∂(((Work.BoseBoxFock.boxMeas ℓ).prod (Work.BoseBoxFock.boxMeas ℓ)).prod
        (MeasureTheory.Measure.pi (fun _ : ι => Work.BoseBoxFock.boxMeas ℓ))),
      w.1.1 ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ w.1.2 ∈ Work.BoseK15.corpusBox.boxL ℓ
        ∧ w.2 ∈ boxPiSet ι ℓ := by
    refine (MeasureTheory.Measure.ae_prod_iff_ae_ae ?_).2 ?_
    · exact (hboxL_meas.preimage (measurable_fst.comp measurable_fst)).inter
        ((hboxL_meas.preimage (measurable_snd.comp measurable_fst)).inter
          (hboxPi_meas.preimage measurable_snd))
    · exact hmem12.mono fun z hz => hmem2.mono fun y hy => ⟨hz.1, hz.2, hy⟩
  -- #### integrability of the images kernel, and of the majorant
  have himg : MeasureTheory.Integrable
      (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Work.BoseBoxFock.imgKernel ℓ W q.1 q.2)
      ((Work.BoseBoxFock.boxMeas ℓ).prod (Work.BoseBoxFock.boxMeas ℓ)) :=
    imgKernel_integrable_boxL hℓ hWi hR hRℓ hWs
  have hmaj : MeasureTheory.Integrable
      (fun w : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × (ι → EuclideanSpace ℝ (Fin 3)) =>
        |Work.BoseBoxFock.imgKernel ℓ W w.1.1 w.1.2| * (B₁ * B₂))
      (((Work.BoseBoxFock.boxMeas ℓ).prod (Work.BoseBoxFock.boxMeas ℓ)).prod
        (MeasureTheory.Measure.pi (fun _ : ι => Work.BoseBoxFock.boxMeas ℓ))) :=
    MeasureTheory.Integrable.mul_prod
      (by simpa only [Real.norm_eq_abs] using himg.abs)
      (MeasureTheory.integrable_const_iff.mpr (Or.inr inferInstance))
  -- #### assemble
  refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
  · exact (((hF.measurable.comp (continuous_sliceInsFun p hp).measurable).aestronglyMeasurable.mul
      (hG.measurable.comp (continuous_sliceInsFun p hp).measurable).aestronglyMeasurable).mul
      himg.aestronglyMeasurable.comp_fst)
  · filter_upwards [hmem] with w hw
    obtain ⟨hw1, hw2, hw3⟩ := hw
    have hxab : Work.BoseBoxFock.insertCoord2 p w.1.1 w.1.2 w.2
        ∈ Submission.BoseGases.abox n ℓ :=
      (insertCoord2_mem_abox_iff hℓ hw1 hw2 w.2).mpr hw3
    have hFx : |F (Work.BoseBoxFock.insertCoord2 p w.1.1 w.1.2 w.2)| ≤ B₁ := hFb _ hxab
    have hGx : |G (Work.BoseBoxFock.insertCoord2 p w.1.1 w.1.2 w.2)| ≤ B₂ := hGb _ hxab
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |F (Work.BoseBoxFock.insertCoord2 p w.1.1 w.1.2 w.2)|
          * |G (Work.BoseBoxFock.insertCoord2 p w.1.1 w.1.2 w.2)|
          * |Work.BoseBoxFock.imgKernel ℓ W w.1.1 w.1.2|
        ≤ B₁ * B₂ * |Work.BoseBoxFock.imgKernel ℓ W w.1.1 w.1.2| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact mul_le_mul hFx hGx (abs_nonneg _) hB₁
      _ = |Work.BoseBoxFock.imgKernel ℓ W w.1.1 w.1.2| * (B₁ * B₂) := by ring

end Work.BoseBoxFock
