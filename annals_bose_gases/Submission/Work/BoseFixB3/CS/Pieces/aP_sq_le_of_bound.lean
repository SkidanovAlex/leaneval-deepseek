import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxProj_sq_contraction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.CS.Pieces

open MeasureTheory

/-- The FS-faithful box projection `boxPInd` with `A = acube ℓ`, `volA = ℓ³` agrees with the
corpus mean `aP` on the centred box (the box indicator carried by `boxPInd` is `1` there). -/
lemma boxPInd_acube_eq_aP {N : ℕ} {ℓ : ℝ} (i : Fin N)
    (Ξ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N)
    (hx : x ∈ Submission.BoseGases.abox N ℓ) :
    Work.UBBInputs8.boxPInd (ℓ ^ 3) (Submission.BoseGases.acube ℓ) i Ξ x
      = Submission.BoseGases.aP ℓ i Ξ x := by
  have hxi : x i ∈ Submission.BoseGases.acube ℓ := hx i
  simp only [Work.UBBInputs8.boxPInd, Submission.BoseGases.aP, Set.indicator_of_mem hxi,
    mul_one]

/-- On the centred box the slot-`i` box indicator `1_{acube ℓ}(x i)` is `1`. -/
lemma ind_acube_mul_eq {N : ℕ} {ℓ : ℝ} (i : Fin N) (Ξ : Submission.BoseGases.X N → ℝ)
    (x : Submission.BoseGases.X N) (hx : x ∈ Submission.BoseGases.abox N ℓ) :
    (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) (x i) * Ξ x = Ξ x := by
  rw [Set.indicator_of_mem (hx i), one_mul]

theorem aP_sq_le_of_bound {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {Ξ : Submission.BoseGases.X N → ℝ} {B : ℝ} (hB : 0 ≤ B) (hΞm : Measurable Ξ)
    (hΞb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ξ x| ≤ B) :
    (∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aP ℓ i Ξ x) ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox N ℓ, (Ξ x) ^ 2 := by
  have hvolA : ℓ ^ 3 =
      (MeasureTheory.volume (Submission.BoseGases.acube ℓ)).toReal := by
    rw [← Submission.BoseGases.real_volume_acube ℓ hℓ.le, MeasureTheory.measureReal_def,
      Measure.restrict_apply_univ]
  have hmain := (Work.BoseFixB1S.boxProj_sq_contraction (ℓ := ℓ) (volA := ℓ ^ 3) hℓ
      (by positivity) (Submission.BoseGases.acube_measurable ℓ) hvolA
      (subset_refl _) i hΞm hB hΞb).1
  calc (∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.aP ℓ i Ξ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd (ℓ ^ 3) (Submission.BoseGases.acube ℓ) i Ξ x) ^ 2 := by
        apply integral_congr_ae
        filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable N ℓ)]
          with x hx
        rw [boxPInd_acube_eq_aP i Ξ x hx]
    _ ≤ ∫ x in Submission.BoseGases.abox N ℓ,
          ((Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) (x i) * Ξ x) ^ 2 :=
        hmain
    _ = ∫ x in Submission.BoseGases.abox N ℓ, (Ξ x) ^ 2 := by
        apply integral_congr_ae
        filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable N ℓ)]
          with x hx
        rw [ind_acube_mul_eq i Ξ x hx]

end Work.BoseFixB3.CS.Pieces
