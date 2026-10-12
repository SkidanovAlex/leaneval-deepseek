import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxC1_add_cnPlus
import Submission.Work.BoseFixB1S.integrableOn_phi_sq_indicator
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory

set_option linter.unusedVariables false

theorem boxFlatCount_le_NB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvolA : 0 < volA)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet Ac)
    (hAcsub : Ac ⊆ Submission.BoseGases.acube ℓ)
    (hvol : volA = (MeasureTheory.volume Ac).toReal)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Continuous Φ) :
    Work.BoseFixB1S.boxFlatCount volA ℓ Ac Φ
      ≤ (N : ℝ) * ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 := by
  -- `Φ²` is integrable on the compact box
  have hΦ2int : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => (Φ x) ^ 2)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
    obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn
      (s := Submission.BoseGases.abox N ℓ) (f := Φ) hΦ.continuousOn
    exact Work.BoseFixB1S.integrableOn_sq_of_bound (N := N) hℓ hΦ.measurable
      (fun x hx => by simpa [Real.norm_eq_abs] using hC x hx)
  -- per-slot bound `∫(P_{B,i}Φ)² ≤ ∫Φ²`
  have hper : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA Ac i Φ x) ^ 2)
        ≤ ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 := by
    intro i
    have hsplit := Work.BoseFixB1S.boxPInd_sq_add_boxQInd_sq (N := N) hℓ hAcm hvol hAcsub i hΦ
    have hQnn : 0 ≤ ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd volA Ac i Φ x) ^ 2 :=
      MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
    -- the box indicator is `≤ 1` pointwise, and `Φ² ≥ 0`
    have hpt : ∀ x : Submission.BoseGases.X N,
        0 ≤ Ac.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2 ∧
        Ac.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2 ≤ (Φ x) ^ 2 := by
      intro x
      have hsq : 0 ≤ (Φ x) ^ 2 := sq_nonneg _
      by_cases h : x i ∈ Ac
      · rw [Set.indicator_of_mem h]; constructor <;> linarith
      · rw [Set.indicator_of_notMem h]; constructor <;> linarith
    have hind_le : (∫ x in Submission.BoseGases.abox N ℓ,
          Ac.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
        ≤ ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 :=
      MeasureTheory.setIntegral_mono_of_nonneg
        (fun x _ => (hpt x).1) (fun x _ => (hpt x).2) hΦ2int
    linarith
  rw [Work.BoseFixB1S.boxFlatCount]
  calc ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA Ac i Φ x) ^ 2
      ≤ ∑ _i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 :=
        Finset.sum_le_sum (fun i _ => hper i)
    _ = (N : ℝ) * ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Work.BoseFixB1S
