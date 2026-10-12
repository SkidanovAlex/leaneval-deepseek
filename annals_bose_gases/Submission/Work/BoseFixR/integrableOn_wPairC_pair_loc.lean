import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Pot.lintegral_pair_abox
import Submission.Work.BoseFixR.lintegral_wPairC_acube_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

open MeasureTheory

/-- Local integrability of the χ-renormalised two-body kernel `wPairC ℓ h` in the *pair* of
coordinates `(x i, x j)`, `i ≠ j`, as a function on the `n`-particle centred box `abox n ℓ`.

The numerator `h` is only assumed *locally* integrable.  The two ingredients are

* measurability: `fun x => wPairC ℓ h (x i) (x j)` is a.e. strongly measurable for the product
  Lebesgue measure on `X n`, because
  - `x ↦ h (x i − x j)` is a.e. measurable (the relative coordinate `x ↦ x i − x j` is
    quasi-measure-preserving, `qmp_sub_coord.comp (qmp_pair_coord i j hij)`, and `h` is a.e.
    measurable by local integrability),
  - the remaining factors `χ_ℓ(x i)`, `χ_ℓ(x j)` are continuous and `(χ⋆χ)_ℓ(x i − x j)⁻¹` is
    measurable;
  then restrict to the box (`Measure.restrict_le_self`);

* finiteness of the `enorm` integral: peel the two coordinates out of the box integral
  (`lintegral_pair_abox`), then use that the resulting double integral over the one-particle
  cube is bounded by `ofReal (ℓ³ ∫_{‖z‖ ≤ ℓ} |h|) < ⊤` (`lintegral_wPairC_acube_le`, whose
  hypothesis `IntegrableOn h (closedBall 0 ℓ)` is exactly what local integrability provides on
  a compact set). -/
theorem integrableOn_wPairC_pair_loc {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {h : EuclideanSpace ℝ (Fin 3) → ℝ} (hh : MeasureTheory.LocallyIntegrable h)
    {i j : Fin n} (hij : i ≠ j) :
    MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => Submission.BoseGases.wPairC ℓ h (x i) (x j))
      (Submission.BoseGases.abox n ℓ) MeasureTheory.volume := by
  -- ### measurability
  have hqmpdiff : Measure.QuasiMeasurePreserving
      (fun x : Submission.BoseGases.X n => x i - x j)
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
    Work.BoseFixGlue.Pot.qmp_sub_coord.comp (Work.BoseFixGlue.Pot.qmp_pair_coord i j hij)
  have hhae : AEMeasurable h
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) :=
    hh.aestronglyMeasurable.aemeasurable
  have hdiff : AEMeasurable (fun x : Submission.BoseGases.X n => h (x i - x j))
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) :=
    hhae.comp_quasiMeasurePreserving hqmpdiff
  have hchi1 : MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X n => Submission.BoseGases.chiScale ℓ (x i))
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) :=
    ((Submission.BoseGases.chiScale_continuous ℓ).comp
      (by fun_prop : Continuous fun x : Submission.BoseGases.X n => x i)).aestronglyMeasurable
  have hchi2 : MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X n => Submission.BoseGases.chiScale ℓ (x j))
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) :=
    ((Submission.BoseGases.chiScale_continuous ℓ).comp
      (by fun_prop : Continuous fun x : Submission.BoseGases.X n => x j)).aestronglyMeasurable
  have hcinv : Measurable
      (fun x : Submission.BoseGases.X n => (Submission.BoseGases.convScale ℓ (x i - x j))⁻¹) :=
    (by fun_prop : Measurable fun t : ℝ => t⁻¹).comp
      ((Submission.BoseGases.convScale_continuous ℓ).comp (by fun_prop)).measurable
  have hnum : MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X n =>
        h (x i - x j) / Submission.BoseGases.convScale ℓ (x i - x j))
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) :=
    (hdiff.mul hcinv.aemeasurable).aestronglyMeasurable
  have hmain : MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X n => Submission.BoseGases.wPairC ℓ h (x i) (x j))
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) :=
    (hchi1.mul hnum).mul hchi2
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun x : Submission.BoseGases.X n => Submission.BoseGases.wPairC ℓ h (x i) (x j))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) :=
    hmain.mono_measure MeasureTheory.Measure.restrict_le_self
  -- ### the `enorm` integral is finite
  have hφ : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ‖Submission.BoseGases.wPairC ℓ h p.1 p.2‖ₑ)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) :=
    (Work.BoseFixB2.Pot.aemeasurable_wPairC_prod (ℓ := ℓ)
      hh.aestronglyMeasurable).enorm.aestronglyMeasurable
  have hfin : MeasureTheory.HasFiniteIntegral
      (fun x : Submission.BoseGases.X n => Submission.BoseGases.wPairC ℓ h (x i) (x j))
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ)) := by
    rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
    have hpair : (∫⁻ x : Submission.BoseGases.X n,
          ‖Submission.BoseGases.wPairC ℓ h (x i) (x j)‖ₑ
          ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ)))
        = ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))
              (Submission.BoseGases.acube ℓ)) ^ (n - 2)
          * (∫⁻ a : EuclideanSpace ℝ (Fin 3),
              (∫⁻ b : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.wPairC ℓ h a b‖ₑ
                ∂((MeasureTheory.volume : MeasureTheory.Measure
                    (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ)))
              ∂((MeasureTheory.volume : MeasureTheory.Measure
                  (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ))) :=
      Work.BoseFixB2.Pot.lintegral_pair_abox (ℓ := ℓ) hℓ hij
        (φ := fun a b : EuclideanSpace ℝ (Fin 3) =>
          ‖Submission.BoseGases.wPairC ℓ h a b‖ₑ) hφ
    rw [hpair]
    refine ENNReal.mul_lt_top ?_ ?_
    · rw [Submission.BoseGases.acube_volume ℓ hℓ.le]
      exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
    · calc (∫⁻ a : EuclideanSpace ℝ (Fin 3),
              (∫⁻ b : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.wPairC ℓ h a b‖ₑ
                ∂((MeasureTheory.volume : MeasureTheory.Measure
                    (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ)))
              ∂((MeasureTheory.volume : MeasureTheory.Measure
                  (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ)))
          ≤ ∫⁻ a : EuclideanSpace ℝ (Fin 3),
              (∫⁻ b : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.wPairC ℓ h a b‖ₑ)
              ∂((MeasureTheory.volume : MeasureTheory.Measure
                  (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ)) :=
            lintegral_mono
              (fun a => lintegral_mono' MeasureTheory.Measure.restrict_le_self le_rfl)
        _ ≤ ENNReal.ofReal (ℓ ^ 3 * ∫ z in Metric.closedBall 0 ℓ, |h z|) :=
            lintegral_wPairC_acube_le hℓ
              (hh.integrableOn_isCompact (isCompact_closedBall 0 ℓ))
        _ < ⊤ := ENNReal.ofReal_lt_top
  exact ⟨hmeas, hfin⟩

end Work.BoseFixR
