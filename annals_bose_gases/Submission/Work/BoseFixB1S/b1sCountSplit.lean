import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxC1_add_cnPlus
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory

theorem b1sCountSplit {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      Φ x ≠ 0 → ∀ i : Fin N, x i ∈ A) :
    Work.BoseFixB1S.boxFlatCount volA ℓ A Φ + Work.BoseFixB1S.boxQCount volA ℓ A Φ
      = (N : ℝ) * (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) := by
  -- per-slot Pythagoras, summed over the slots
  have hsplit : (∑ i : Fin N,
        ((∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
          + ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2))
      = ∑ i : Fin N,
          ∫ x in Submission.BoseGases.abox N ℓ,
            A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => boxPInd_sq_add_boxQInd_sq hℓ hA hvolA hAc i hΦc)
  -- the support hypothesis collapses each slot-summand of the indicator sum
  have hterm : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
          A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
        = ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 := by
    intro i
    refine integral_congr_ae ?_
    filter_upwards [hsupp] with x hx
    by_cases hmem : x i ∈ A
    · rw [Set.indicator_of_mem hmem, one_mul]
    · have hΦ : Φ x = 0 := by
        by_contra hc
        exact hmem (hx hc i)
      rw [Set.indicator_of_notMem hmem]
      simp [hΦ]
  rw [boxFlatCount, boxQCount, ← Finset.sum_add_distrib, hsplit,
    Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

end Work.BoseFixB1S
