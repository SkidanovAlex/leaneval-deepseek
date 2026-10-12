import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPIndFlat
import Submission.Work.BoseFixB1S.BoxQIndCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

theorem boxPIndSelfAdjoint {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Φ Ψ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) {CΦ : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ CΦ)
    (hΨm : Measurable Ψ) {CΨ : ℝ}
    (hΨb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ CΨ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxPInd volA A i Φ x * Ψ x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          Φ x * Work.UBBInputs8.boxPInd volA A i Ψ x := by
  have hI1 : IntegrableOn (fun x : X N => Work.UBBInputs8.boxPInd volA A i Ψ x * Φ x)
      (abox N ℓ) MeasureTheory.volume :=
    integrableOn_mul_of_bound hℓ (measurable_boxPInd volA A hA i hΨm) hΦm
      (abs_boxPInd_le hℓ hvol hA hvolA hAc i hΨb) hΦb
  have hI2 : IntegrableOn (fun x : X N => Work.UBBInputs8.boxPInd volA A i Φ x * Ψ x)
      (abox N ℓ) MeasureTheory.volume :=
    integrableOn_mul_of_bound hℓ (measurable_boxPInd volA A hA i hΦm) hΨm
      (abs_boxPInd_le hℓ hvol hA hvolA hAc i hΦb) hΨb
  cases N with
  | zero => exact absurd i.isLt (Nat.not_lt_zero _)
  | succ n =>
    have hP1 := abox_integral_peel (i := i)
      (F := fun x : X (n + 1) => Work.UBBInputs8.boxPInd volA A i Φ x * Ψ x) hI2
    have hP2 := abox_integral_peel (i := i)
      (F := fun x : X (n + 1) => Φ x * Work.UBBInputs8.boxPInd volA A i Ψ x)
      (by simpa only [mul_comm] using hI1)
    have hpoint : ∀ r : X n,
        (∫ y in acube ℓ,
            Work.UBBInputs8.boxPInd volA A i Φ (kcInsN n i (y, r)) * Ψ (kcInsN n i (y, r)))
          = ∫ y in acube ℓ,
            Φ (kcInsN n i (y, r)) * Work.UBBInputs8.boxPInd volA A i Ψ (kcInsN n i (y, r)) := by
      intro r
      have hL : (∫ y in acube ℓ,
            Work.UBBInputs8.boxPInd volA A i Φ (kcInsN n i (y, r)) * Ψ (kcInsN n i (y, r)))
          = (1 / volA) * (∫ z in A, Φ (kcInsN n i (z, r)))
            * (∫ z in A, Ψ (kcInsN n i (z, r))) := by
        have hcongr : (∫ y in acube ℓ,
              Work.UBBInputs8.boxPInd volA A i Φ (kcInsN n i (y, r)) * Ψ (kcInsN n i (y, r)))
            = ∫ y in acube ℓ, ((1 / volA) * (∫ z in A, Φ (kcInsN n i (z, r))))
                * (A.indicator (fun _ => (1 : ℝ)) y * Ψ (kcInsN n i (y, r))) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with y
          rw [boxPInd_kcInsN]
          ring
        rw [hcongr, MeasureTheory.integral_const_mul,
          setIntegral_indicator_one_mul hA hAc (fun z : E3 => Ψ (kcInsN n i (z, r)))]
        try ring
      have hR : (∫ y in acube ℓ,
            Φ (kcInsN n i (y, r)) * Work.UBBInputs8.boxPInd volA A i Ψ (kcInsN n i (y, r)))
          = (1 / volA) * (∫ z in A, Φ (kcInsN n i (z, r)))
            * (∫ z in A, Ψ (kcInsN n i (z, r))) := by
        have hcongr : (∫ y in acube ℓ,
              Φ (kcInsN n i (y, r)) * Work.UBBInputs8.boxPInd volA A i Ψ (kcInsN n i (y, r)))
            = ∫ y in acube ℓ, ((1 / volA) * (∫ z in A, Ψ (kcInsN n i (z, r))))
                * (A.indicator (fun _ => (1 : ℝ)) y * Φ (kcInsN n i (y, r))) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with y
          rw [boxPInd_kcInsN]
          ring
        rw [hcongr, MeasureTheory.integral_const_mul,
          setIntegral_indicator_one_mul hA hAc (fun z : E3 => Φ (kcInsN n i (z, r)))]
        ring
      rw [hL, hR]
    calc
      (∫ x in abox (n + 1) ℓ, Work.UBBInputs8.boxPInd volA A i Φ x * Ψ x)
          = ∫ r : X n, (∫ y in acube ℓ,
              Work.UBBInputs8.boxPInd volA A i Φ (kcInsN n i (y, r)) * Ψ (kcInsN n i (y, r)))
            ∂((MeasureTheory.volume : Measure (X n)).restrict (abox n ℓ)) := hP1
      _ = ∫ r : X n, (∫ y in acube ℓ,
              Φ (kcInsN n i (y, r)) * Work.UBBInputs8.boxPInd volA A i Ψ (kcInsN n i (y, r)))
            ∂((MeasureTheory.volume : Measure (X n)).restrict (abox n ℓ)) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with r
            exact hpoint r
      _ = (∫ x in abox (n + 1) ℓ, Φ x * Work.UBBInputs8.boxPInd volA A i Ψ x) := hP2.symm

end Work.BoseFixB1S
