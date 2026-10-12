import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB2.Pot.lintegral_coord_abox
import Submission.Work.BoseFixR.lintegral_wPairC_acube_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixR.integrableOn_chemP_loc`

The **local** version of `Work.BoseFixB2.Energy.integrableOn_chemP_coord`: for `0 < ℓ` and a
numerator `h` that is merely *locally* integrable, the one-body (chemical potential) piece

    `x ↦ chemP ℓ h (x i) = ∫_y wPairC ℓ h (x i) y`

is integrable on the centred box `abox n ℓ`.

The route is exactly the one of the `L¹` version, with the global `L¹`-bound on the joint kernel
replaced by its box-localised counterpart `Work.BoseFixR.lintegral_wPairC_acube_le`:

1. `h` is a.e. strongly measurable (`LocallyIntegrable.aestronglyMeasurable`) and integrable on
   the closed ball `closedBall 0 ℓ` (`LocallyIntegrable.integrableOn_isCompact`, the ball being
   compact);
2. `chemQ ℓ h = a ↦ ∫⁻_y ‖wPairC ℓ h a y‖ₑ` is a.e. strongly measurable
   (`aemeasurable_wPairC_prod` + `AEMeassurable.lintegral_prod_right'`), and
   `ofReal ‖chemP ℓ h a‖ ≤ chemQ ℓ h a` pointwise (`enorm_integral_le_lintegral_enorm`);
3. peel the single coordinate over the box (`lintegral_coord_abox`) and bound the remaining
   `∫⁻` over `acube ℓ` by `ofReal (ℓ³ ∫_{‖z‖≤ℓ} |h z|)`
   (`lintegral_wPairC_acube_le`).

No support, boundedness or diluteness hypothesis is used.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.BoseFixR

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `chemP ℓ h` is a.e. strongly measurable whenever `h` is. -/
lemma aesm_chemP_loc {ℓ : ℝ} {h : E3 → ℝ}
    (hh : AEStronglyMeasurable h (volume : Measure E3)) :
    AEStronglyMeasurable (chemP ℓ h) (volume : Measure E3) :=
  AEStronglyMeasurable.integral_prod_right'
    (Work.BoseFixB2.Pot.aemeasurable_wPairC_prod (ℓ := ℓ) hh)

/-- `chemQ ℓ h` is a.e. strongly measurable whenever `h` is. -/
lemma aesm_chemQ_loc {ℓ : ℝ} {h : E3 → ℝ}
    (hh : AEStronglyMeasurable h (volume : Measure E3)) :
    AEStronglyMeasurable (chemQ ℓ h) (volume : Measure E3) :=
  (AEMeasurable.lintegral_prod_right'
    (Work.BoseFixB2.Pot.aemeasurable_wPairC_prod (ℓ := ℓ) hh).enorm).aestronglyMeasurable

/-- The pointwise `enorm` domination of `chemP` by `chemQ`. -/
lemma ofReal_norm_chemP_le_chemQ (ℓ : ℝ) (h : E3 → ℝ) (a : E3) :
    ENNReal.ofReal ‖chemP ℓ h a‖ ≤ chemQ ℓ h a := by
  have h1 : ‖chemP ℓ h a‖ₑ ≤ chemQ ℓ h a :=
    MeasureTheory.enorm_integral_le_lintegral_enorm
      (f := fun y : E3 => Submission.BoseGases.wPairC ℓ h a y)
  rw [Real.enorm_eq_ofReal_abs] at h1
  simpa [Real.norm_eq_abs] using h1

theorem integrableOn_chemP_loc {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {h : EuclideanSpace ℝ (Fin 3) → ℝ} (hh : MeasureTheory.LocallyIntegrable h) (i : Fin n) :
    MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => Work.BoseFixR.chemP ℓ h (x i))
      (Submission.BoseGases.abox n ℓ) MeasureTheory.volume := by
  have hℓnn : (0 : ℝ) ≤ ℓ := le_of_lt hℓ
  have hhmeas : AEStronglyMeasurable h (volume : Measure E3) := hh.aestronglyMeasurable
  have hint : IntegrableOn h (Metric.closedBall 0 ℓ) (volume : Measure E3) :=
    hh.integrableOn_isCompact (isCompact_closedBall 0 ℓ)
  have hQmeas : AEStronglyMeasurable (chemQ ℓ h) (volume : Measure E3) := aesm_chemQ_loc hhmeas
  -- (1) the coordinate-peeled `∫⁻` of `chemQ` is finite
  have hbound : (∫⁻ a : E3, chemQ ℓ h a
        ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)))
      ≤ ENNReal.ofReal (ℓ ^ 3 * ∫ z in Metric.closedBall 0 ℓ, |h z|) := by
    simpa [chemQ] using lintegral_wPairC_acube_le hℓ hint
  have hQtop : ((volume : Measure E3) (Submission.BoseGases.acube ℓ)) ^ (n - 1)
        * ENNReal.ofReal (ℓ ^ 3 * ∫ z in Metric.closedBall 0 ℓ, |h z|) < ⊤ :=
    ENNReal.mul_lt_top
      (ENNReal.pow_lt_top (Submission.BoseGases.acube_lt_top ℓ hℓnn))
      ENNReal.ofReal_lt_top
  -- (2) finiteness of the integral of `‖chemP ℓ h (x i)‖`
  have hHFI : MeasureTheory.HasFiniteIntegral
      (fun x : Submission.BoseGases.X n => chemP ℓ h (x i))
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) := by
    rw [MeasureTheory.hasFiniteIntegral_iff_norm]
    have h1 : (∫⁻ x : Submission.BoseGases.X n, ENNReal.ofReal ‖chemP ℓ h (x i)‖
          ∂((volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ)))
        ≤ (∫⁻ x : Submission.BoseGases.X n, chemQ ℓ h (x i)
          ∂((volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ))) :=
      lintegral_mono (fun x => ofReal_norm_chemP_le_chemQ ℓ h (x i))
    have h2 : (∫⁻ x : Submission.BoseGases.X n, chemQ ℓ h (x i)
          ∂((volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ)))
        = ((volume : Measure E3) (Submission.BoseGases.acube ℓ)) ^ (n - 1)
          * (∫⁻ a : E3, chemQ ℓ h a
              ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
      Work.BoseFixB2.Pot.lintegral_coord_abox hℓ i hQmeas
    calc (∫⁻ x : Submission.BoseGases.X n, ENNReal.ofReal ‖chemP ℓ h (x i)‖
          ∂((volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ)))
        ≤ (∫⁻ x : Submission.BoseGases.X n, chemQ ℓ h (x i)
          ∂((volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ))) := h1
      _ = ((volume : Measure E3) (Submission.BoseGases.acube ℓ)) ^ (n - 1)
          * (∫⁻ a : E3, chemQ ℓ h a
              ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) := h2
      _ ≤ ((volume : Measure E3) (Submission.BoseGases.acube ℓ)) ^ (n - 1)
          * ENNReal.ofReal (ℓ ^ 3 * ∫ z in Metric.closedBall 0 ℓ, |h z|) :=
          mul_le_mul' le_rfl hbound
      _ < ⊤ := hQtop
  -- (3) a.e. strong measurability of the coordinate function on the box
  have hPmeas : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X n => chemP ℓ h (x i))
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    ((aesm_chemP_loc hhmeas).comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => (volume : Measure E3)) i)).mono_measure
      Measure.restrict_le_self
  exact ⟨hPmeas, hHFI⟩

end Work.BoseFixR
