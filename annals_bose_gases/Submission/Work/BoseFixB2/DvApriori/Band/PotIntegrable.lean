import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.potWordU_form_eq_qLHSword_radial
import Submission.Work.BoseFixB2.Pot.aemeasurable_wPairC_prod
import Submission.Work.BoseFixB2.Pot.aestronglyMeasurable_potWordU
import Submission.Work.BoseFixB2.Pot.lintegral_coord_abox
import Submission.Work.BoseFixB2.Pot.lintegral_wPairC_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.DvApriori.Band.PotIntegrable`

Integrability on the box of the **one-body fibre** of the potential profile,
`x ↦ ∫_y wPairC ℓ h (xᵢ) y`.  (The pair summands are available from the corpus as
`Submission.BoseGases.integrableOn_slot_wPair`.)

The band identity is linear in the weight, so splitting `potWordU` into its slots requires
each summand to be integrable.  Unlike the pair summands, the fibre is not bounded under the
hypotheses of theorem 1.2 (no positivity of `v` is assumed), so the proof goes through the
lintegral peeling `lintegral_coord_abox` and the master inequality `lintegral_wPairC_le`,
exactly as `potWordU_integrable` does for the whole word.
-/

namespace Work.BoseFixB2.DvApriori

open Submission.BoseGases MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section


/-- The one-body fibre `a ↦ ∫⁻_y ‖wPairC ℓ h a y‖ₑ` has finite cube integral. -/
theorem cube_fibre_bound {ℓ : ℝ} (hℓ : 0 < ℓ) {h : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hh : MeasureTheory.Integrable h) :
    (∫⁻ a : EuclideanSpace ℝ (Fin 3), (∫⁻ y : EuclideanSpace ℝ (Fin 3), ‖wPairC ℓ h a y‖ₑ)
        ∂((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)))
      ≤ ENNReal.ofReal (ℓ ^ 3 * ∫ z : EuclideanSpace ℝ (Fin 3), |h z|) := by
  have hwmeas : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => wPairC ℓ h p.1 p.2)
      ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3)))) :=
    Work.BoseFixB2.Pot.aemeasurable_wPairC_prod hh.aestronglyMeasurable
  have hcube_le : ∀ f : EuclideanSpace ℝ (Fin 3) → ENNReal,
      (∫⁻ x : EuclideanSpace ℝ (Fin 3) in acube ℓ, f x) ≤ ∫⁻ x : EuclideanSpace ℝ (Fin 3), f x := by
    intro f
    refine (lintegral_mono_set (Set.subset_univ (acube ℓ))).trans ?_
    exact le_of_eq (by simp [Measure.restrict_univ])
  have hfull : (∫⁻ a : EuclideanSpace ℝ (Fin 3), (∫⁻ y : EuclideanSpace ℝ (Fin 3), ‖wPairC ℓ h a y‖ₑ)
        ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))))
      = (∫⁻ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3), ‖wPairC ℓ h p.1 p.2‖ₑ
          ∂((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))))) :=
    (MeasureTheory.lintegral_prod
      (f := fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => ‖wPairC ℓ h p.1 p.2‖ₑ)
      hwmeas.enorm).symm
  calc (∫⁻ a : EuclideanSpace ℝ (Fin 3), (∫⁻ y : EuclideanSpace ℝ (Fin 3), ‖wPairC ℓ h a y‖ₑ)
        ∂((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)))
      ≤ (∫⁻ a : EuclideanSpace ℝ (Fin 3), (∫⁻ y : EuclideanSpace ℝ (Fin 3), ‖wPairC ℓ h a y‖ₑ)
          ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3)))) := hcube_le _
    _ = (∫⁻ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3), ‖wPairC ℓ h p.1 p.2‖ₑ
          ∂((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))))) := hfull
    _ ≤ ENNReal.ofReal (ℓ ^ 3 * ∫ z : EuclideanSpace ℝ (Fin 3), |h z|) := Work.BoseFixB2.Pot.lintegral_wPairC_le hℓ hh

/-- **The one-body fibre is integrable on the box.** -/
theorem integrableOn_wPairC_fibre {ℓ : ℝ} (hℓ : 0 < ℓ) {h : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hh : MeasureTheory.Integrable h) {n : ℕ} (i : Fin n) :
    MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        ∫ y in acube ℓ, wPairC ℓ h (x i) y)
      (abox n ℓ) := by
  have hℓnn : (0 : ℝ) ≤ ℓ := le_of_lt hℓ
  have hQmeas : AEStronglyMeasurable
      (fun a : EuclideanSpace ℝ (Fin 3) => ∫⁻ y : EuclideanSpace ℝ (Fin 3), ‖wPairC ℓ h a y‖ₑ)
      (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
    (AEMeasurable.lintegral_prod_right'
      (Work.BoseFixB2.Pot.aemeasurable_wPairC_prod hh.aestronglyMeasurable).enorm).aestronglyMeasurable
  have hQcomp : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X n => ∫⁻ y : EuclideanSpace ℝ (Fin 3), ‖wPairC ℓ h (x i) y‖ₑ)
      (MeasureTheory.volume : Measure (Submission.BoseGases.X n)) :=
    hQmeas.comp_quasiMeasurePreserving (Work.BoseFixB2.Pot.qmp_coord_X i)
  have haesm : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X n => ∫ y in acube ℓ, wPairC ℓ h (x i) y)
      (MeasureTheory.volume : Measure (Submission.BoseGases.X n)) := by
    have hbase : AEStronglyMeasurable
        (fun x : Submission.BoseGases.X n => ∫ y : EuclideanSpace ℝ (Fin 3), wLoc ℓ h 0 (x i) y)
        (MeasureTheory.volume : Measure (Submission.BoseGases.X n)) :=
      Work.BoseFixB2.Pot.aesm_wLoc_integral_X (ℓ := ℓ) (u := 0) hh.aestronglyMeasurable i
    refine AEStronglyMeasurable.congr hbase (Filter.Eventually.of_forall (fun x => ?_))
    have h2 : w1Fibre ℓ (wPairC ℓ h) (x i) = Work.BoseBox.potBr ℓ h 0 (x i) :=
      Work.BoseFixB2.DvApriori.w1Fibre_wPairC_eq_potBr hℓ h (x i)
    show Work.BoseBox.potBr ℓ h 0 (x i) = w1Fibre ℓ (wPairC ℓ h) (x i)
    rw [h2]
  refine ⟨haesm.restrict, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_norm]
  have hcube_le : ∀ f : EuclideanSpace ℝ (Fin 3) → ENNReal,
      (∫⁻ y : EuclideanSpace ℝ (Fin 3) in acube ℓ, f y) ≤ ∫⁻ y : EuclideanSpace ℝ (Fin 3), f y := by
    intro f
    refine (lintegral_mono_set (Set.subset_univ (acube ℓ))).trans ?_
    exact le_of_eq (by simp [Measure.restrict_univ])
  calc (∫⁻ x : Submission.BoseGases.X n,
        ENNReal.ofReal ‖∫ y in acube ℓ, wPairC ℓ h (x i) y‖
        ∂((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict (abox n ℓ)))
      = (∫⁻ x : Submission.BoseGases.X n,
          ‖∫ y in acube ℓ, wPairC ℓ h (x i) y‖ₑ
          ∂((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict (abox n ℓ))) := by
        refine lintegral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        simp only [Real.norm_eq_abs]
        exact (Real.enorm_eq_ofReal_abs _).symm
    _ ≤ (∫⁻ x : Submission.BoseGases.X n,
          (∫⁻ y : EuclideanSpace ℝ (Fin 3), ‖wPairC ℓ h (x i) y‖ₑ)
          ∂((MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict (abox n ℓ))) := by
        refine lintegral_mono (fun x => ?_)
        refine (MeasureTheory.enorm_integral_le_lintegral_enorm
          (fun y => wPairC ℓ h (x i) y)).trans ?_
        exact hcube_le (fun y => ‖wPairC ℓ h (x i) y‖ₑ)
    _ = ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) (acube ℓ)) ^ (n - 1)
          * (∫⁻ a : EuclideanSpace ℝ (Fin 3), (∫⁻ y : EuclideanSpace ℝ (Fin 3), ‖wPairC ℓ h a y‖ₑ)
              ∂((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ))) :=
        Work.BoseFixB2.Pot.lintegral_coord_abox (ℓ := ℓ)
          (G := fun a => ∫⁻ y : EuclideanSpace ℝ (Fin 3), ‖wPairC ℓ h a y‖ₑ) hℓ i hQmeas
    _ ≤ ((MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3))) (acube ℓ)) ^ (n - 1)
          * ENNReal.ofReal (ℓ ^ 3 * ∫ z : EuclideanSpace ℝ (Fin 3), |h z|) :=
        mul_le_mul_right (cube_fibre_bound hℓ hh) _
    _ < ⊤ := ENNReal.mul_lt_top
        (ENNReal.pow_lt_top (Submission.BoseGases.acube_lt_top ℓ hℓnn)) ENNReal.ofReal_lt_top

end

end Work.BoseFixB2.DvApriori
