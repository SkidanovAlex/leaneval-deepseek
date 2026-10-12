import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_flatCountPaymentB1
import Submission.Work.BoseFixB1S.boxPairMixedAvgLe
import Submission.Work.BoseFixB1S.pairSetSumAvg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

/-- **The count identity** `n₀ + n₊ = N` at a normalised state supported in the `A`-occupancy
sector: `boxFlatCount + boxQCount = N`. -/
theorem boxVarLeNmulQCount_count_identity {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) = 1)
    (hsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      Φ x ≠ 0 → ∀ i : Fin N, x i ∈ A) :
    Work.BoseFixB1S.boxFlatCount V ℓ A Φ + Work.BoseFixB1S.boxQCount V ℓ A Φ = (N : ℝ) := by
  have h1 := flatCountIdentity (N := N) (ℓ := ℓ) (volA := V) hℓ hV hA hVeq hAc hΦc
  rw [h1]
  -- the weighted density collapses to `N·Φ²` on the support
  have h2 : (∫ x in Submission.BoseGases.abox N ℓ,
        (∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i)) * (Φ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ, (N : ℝ) * (Φ x) ^ 2 := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hsupp] with x hx
    by_cases h : Φ x = 0
    · simp [h]
    · have hi : ∀ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i) = 1 :=
        fun i => Set.indicator_of_mem (hx h i) _
      have hsum : (∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i)) = (N : ℝ) := by
        rw [Finset.sum_congr rfl (fun i _ => hi i)]
        simp
      rw [hsum]
  rw [h2, MeasureTheory.integral_const_mul, hnorm]
  ring

/-- **The pair bound** `cS₂ ≤ (N−1)·n₀`: the ordered pair-condensate count is dominated by
`(N−1)` times the flat (condensate) count. -/
theorem boxVarLeNmulQCount_pair_bound {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    Work.BoseFixB1S.boxPairCount V ℓ A Φ
      ≤ ((N : ℝ) - 1) * Work.BoseFixB1S.boxFlatCount V ℓ A Φ := by
  have hpair : ∀ p ∈ Submission.BoseGases.pairSet N,
      (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd V A p.1 (Work.UBBInputs8.boxPInd V A p.2 Φ) x) ^ 2)
        ≤ ((∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd V A p.1 Φ x) ^ 2)
          + (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd V A p.2 Φ x) ^ 2)) / 2 :=
    fun p hp => boxPairMixedAvgLe (N := N) (ℓ := ℓ) (volA := V) hℓ hV hA hVeq hAc
      (Finset.mem_filter.mp hp).2 hΦc
  calc Work.BoseFixB1S.boxPairCount V ℓ A Φ
      = ∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd V A p.1 (Work.UBBInputs8.boxPInd V A p.2 Φ) x) ^ 2 := rfl
    _ ≤ ∑ p ∈ Submission.BoseGases.pairSet N,
          ((∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxPInd V A p.1 Φ x) ^ 2)
            + (∫ x in Submission.BoseGases.abox N ℓ,
                (Work.UBBInputs8.boxPInd V A p.2 Φ x) ^ 2)) / 2 :=
        Finset.sum_le_sum hpair
    _ = ((N : ℝ) - 1) * Work.BoseFixB1S.boxFlatCount V ℓ A Φ := by
        rw [pairSetSumAvg (N := N)
          (g := fun i : Fin N =>
            ∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxPInd V A i Φ x) ^ 2)]
        rfl

theorem boxVarLeNmulQCountB1 {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) = 1)
    (hsupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      Φ x ≠ 0 → ∀ i : Fin N, x i ∈ A) :
    (Work.BoseFixB1S.boxPairCount V ℓ A Φ
        - (Work.BoseFixB1S.boxFlatCount V ℓ A Φ ^ 2
            - Work.BoseFixB1S.boxFlatCount V ℓ A Φ))
      ≤ (N : ℝ) * Work.BoseFixB1S.boxQCount V ℓ A Φ := by
  have hcount := boxVarLeNmulQCount_count_identity (N := N) (ℓ := ℓ) (V := V)
    hℓ hV hA hVeq hAc hΦc hnorm hsupp
  have hpair := boxVarLeNmulQCount_pair_bound (N := N) (ℓ := ℓ) (V := V)
    hℓ hV hA hVeq hAc hΦc
  nlinarith [sq_nonneg ((N : ℝ) - Work.BoseFixB1S.boxFlatCount V ℓ A Φ)]

end Work.BoseFixB1S
