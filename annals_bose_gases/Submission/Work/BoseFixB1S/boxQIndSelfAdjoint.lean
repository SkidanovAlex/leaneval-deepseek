import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxPIndSelfAdjoint
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

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

theorem boxQIndSelfAdjoint {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (i : Fin N)
    {Φ Ψ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) {CΦ : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ CΦ)
    (hΨm : Measurable Ψ) {CΨ : ℝ}
    (hΨb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ CΨ) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.UBBInputs8.boxQInd volA A i Φ x * Ψ x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          Φ x * Work.UBBInputs8.boxQInd volA A i Ψ x := by
  have hσm : Measurable (fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i)) := by fun_prop
  have hσbound : ∀ x : X N, |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
    intro x
    by_cases h : x i ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
  -- integrability of the four pieces
  have hA1 : IntegrableOn (fun x : X N =>
      (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) * Ψ x) (abox N ℓ) volume := by
    refine integrableOn_mul_of_bound (Cf := |CΦ|) hℓ (hσm.mul hΦm) hΨm ?_ hΨb
    intro x hx
    rw [abs_mul]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Φ x| ≤ 1 * |CΦ| :=
          mul_le_mul (hσbound x) (le_trans (hΦb x hx) (le_abs_self CΦ)) (abs_nonneg _)
            (by norm_num)
      _ = |CΦ| := one_mul _
  have hB1 : IntegrableOn (fun x : X N =>
      Φ x * (A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x)) (abox N ℓ) volume := by
    refine integrableOn_mul_of_bound (Cg := |CΨ|) hℓ hΦm (hσm.mul hΨm) hΦb ?_
    intro x hx
    rw [abs_mul]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Ψ x| ≤ 1 * |CΨ| :=
          mul_le_mul (hσbound x) (le_trans (hΨb x hx) (le_abs_self CΨ)) (abs_nonneg _)
            (by norm_num)
      _ = |CΨ| := one_mul _
  have hPΦI : IntegrableOn (fun x : X N =>
      Work.UBBInputs8.boxPInd volA A i Φ x * Ψ x) (abox N ℓ) volume :=
    integrableOn_mul_of_bound hℓ (measurable_boxPInd volA A hA i hΦm) hΨm
      (abs_boxPInd_le hℓ hvol hA hvolA hAc i hΦb) hΨb
  have hPΨI : IntegrableOn (fun x : X N =>
      Φ x * Work.UBBInputs8.boxPInd volA A i Ψ x) (abox N ℓ) volume :=
    integrableOn_mul_of_bound hℓ hΦm (measurable_boxPInd volA A hA i hΨm) hΦb
      (abs_boxPInd_le hℓ hvol hA hvolA hAc i hΨb)
  -- `Qᵢ = σᵢ − Pᵢ`: split, use `Pᵢ` self-adjoint, recombine
  calc
    (∫ x in abox N ℓ, Work.UBBInputs8.boxQInd volA A i Φ x * Ψ x)
        = ∫ x in abox N ℓ, ((A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) * Ψ x
            - Work.UBBInputs8.boxPInd volA A i Φ x * Ψ x) := by
          apply integral_congr_ae
          filter_upwards with x
          simp only [Work.UBBInputs8.boxQInd]
          ring
    _ = (∫ x in abox N ℓ, (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) * Ψ x)
          - ∫ x in abox N ℓ, Work.UBBInputs8.boxPInd volA A i Φ x * Ψ x :=
        MeasureTheory.integral_sub hA1 hPΦI
    _ = (∫ x in abox N ℓ, Φ x * (A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x))
          - ∫ x in abox N ℓ, Φ x * Work.UBBInputs8.boxPInd volA A i Ψ x := by
          rw [boxPIndSelfAdjoint hℓ hvol hA hvolA hAc i hΦm hΦb hΨm hΨb,
            show (∫ x in abox N ℓ, (A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) * Ψ x)
                = ∫ x in abox N ℓ, Φ x * (A.indicator (fun _ => (1 : ℝ)) (x i) * Ψ x)
                from by
              apply integral_congr_ae
              filter_upwards with x
              ring]
    _ = ∫ x in abox N ℓ, Φ x * Work.UBBInputs8.boxQInd volA A i Ψ x := by
          rw [← MeasureTheory.integral_sub hB1 hPΨI]
          apply integral_congr_ae
          filter_upwards with x
          simp only [Work.UBBInputs8.boxQInd]
          ring

end Work.BoseFixB1S
