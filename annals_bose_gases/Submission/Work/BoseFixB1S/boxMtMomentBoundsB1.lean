import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxMtBoundScalarB1
import Submission.Work.BoseFixB1S.fsShiftQuadB1
import Submission.Work.BoseFixB1S.mulSqrtSubSqLeSqB1
import Submission.Work.BoseFixB1S.n0FunOpSumSpectralB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The arithmetic core of the moment bounds**: everything except the spectral expansion
`hspec` of the `P`-side moment (which is `Work.BoseFixB1S.n0FunOpSumSpectralB1`). -/
theorem boxMtMomentArithB1 {N : ℕ} {ℓ V c : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) (hc : 1 ≤ c)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) = 1)
    (hspec : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
          (Work.UBBInputs8.boxPInd V A i Φ)) x ^ 2)
        = ∑ S : Finset (Fin N), (S.card : ℝ) *
            (Real.sqrt ((S.card : ℝ) + 1) - Real.sqrt c) ^ 2 *
            ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.BoseFixB1S.n0ProjOp V A S Φ) x ^ 2) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
          (Work.UBBInputs8.boxPInd V A i Φ)) x ^ 2)
        ≤ (Work.BoseFixB1S.boxPairCount V ℓ A Φ
            - (Work.BoseFixB1S.boxFlatCount V ℓ A Φ ^ 2
                - Work.BoseFixB1S.boxFlatCount V ℓ A Φ))
          + (Work.BoseFixB1S.boxFlatCount V ℓ A Φ + 1 - c) ^ 2
    ∧ (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
          (Work.UBBInputs8.boxPInd V A i Φ)) x ^ 2)
        ≤ (Work.BoseFixB1S.boxPairCount V ℓ A Φ
            - (Work.BoseFixB1S.boxFlatCount V ℓ A Φ ^ 2
                - Work.BoseFixB1S.boxFlatCount V ℓ A Φ))
          + (Work.BoseFixB1S.boxFlatCount V ℓ A Φ - c - 1) ^ 2
          + Work.BoseFixB1S.boxFlatCount V ℓ A Φ := by
  classical
  have hΦG : Work.BoseFixB1S.GoodState ℓ Φ := by
    obtain ⟨C, hC⟩ :=
      (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn hΦc.continuousOn
    exact ⟨hΦc.measurable, C, fun x hx => by simpa [Real.norm_eq_abs] using hC x hx⟩
  -- the spectral weights of the subset idempotents
  let p : Finset (Fin N) → ℝ := fun S => ∫ x in Submission.BoseGases.abox N ℓ,
    (Work.BoseFixB1S.n0ProjOp V A S Φ) x ^ 2
  -- they are nonnegative: integrals of squares
  have hpnonneg : ∀ S : Finset (Fin N), 0 ≤ p S := by
    intro S
    exact MeasureTheory.integral_nonneg
      (f := fun x : Submission.BoseGases.X N =>
        (Work.BoseFixB1S.n0ProjOp V A S Φ) x ^ 2) (fun x => sq_nonneg _)
  -- the three spectral moments of `n₀`
  have hM0 : (∑ S : Finset (Fin N), p S) = 1 :=
    (n0Moments_oneB1 hℓ hV hA hVeq hAc hΦc).trans hnorm
  have hM1 : (∑ S : Finset (Fin N), (S.card : ℝ) * p S) = boxFlatCount V ℓ A Φ :=
    n0Moments_twoB1 hℓ hV hA hVeq hAc hΦc
  have hM2 : (∑ S : Finset (Fin N), ((S.card : ℝ) ^ 2) * p S)
      = boxFlatCount V ℓ A Φ + boxPairCount V ℓ A Φ :=
    n0Moments_threeB1 hℓ hV hA hVeq hAc hΦc
  -- the spectral expansion of the `P`-side moment
  have hT : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
        (Work.UBBInputs8.boxPInd V A i Φ)) x ^ 2)
      = ∑ S : Finset (Fin N), (S.card : ℝ) *
          (Real.sqrt ((S.card : ℝ) + 1) - Real.sqrt c) ^ 2 * p S := hspec
  -- the pointwise scalar bound with the `(s+1−c)²` weight, summed
  have step1 : (∑ S : Finset (Fin N), (S.card : ℝ) *
        (Real.sqrt ((S.card : ℝ) + 1) - Real.sqrt c) ^ 2 * p S)
      ≤ ∑ S : Finset (Fin N), ((S.card : ℝ) + 1 - c) ^ 2 * p S := by
    refine Finset.sum_le_sum (fun S _ => ?_)
    have hsc : (S.card : ℝ) * (Real.sqrt ((S.card : ℝ) + 1) - Real.sqrt c) ^ 2
        ≤ ((S.card : ℝ) + 1 - c) ^ 2 :=
      mulSqrtSubSqLeSqB1 (Nat.cast_nonneg S.card) (le_trans zero_le_one hc)
    exact mul_le_mul_of_nonneg_right hsc (hpnonneg S)
  -- the quadratic expansion of the `(s+1−c)²` weight
  have quad1 : (∑ S : Finset (Fin N), ((S.card : ℝ) + 1 - c) ^ 2 * p S)
      = (∑ S : Finset (Fin N), ((S.card : ℝ) ^ 2) * p S)
        + 2 * (1 - c) * (∑ S : Finset (Fin N), (S.card : ℝ) * p S)
        + (1 - c) ^ 2 * (∑ S : Finset (Fin N), p S) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun S _ => by ring)
  -- the pointwise scalar bound with the `(s−c−1)² + s` weight, summed
  have step2 : (∑ S : Finset (Fin N), (S.card : ℝ) *
        (Real.sqrt ((S.card : ℝ) + 1) - Real.sqrt c) ^ 2 * p S)
      ≤ ∑ S : Finset (Fin N), (((S.card : ℝ) - c - 1) ^ 2 + (S.card : ℝ)) * p S := by
    refine Finset.sum_le_sum (fun S _ => ?_)
    have hsc : (S.card : ℝ) * (Real.sqrt ((S.card : ℝ) + 1) - Real.sqrt c) ^ 2
        ≤ ((S.card : ℝ) - c - 1) ^ 2 + (S.card : ℝ) :=
      mul_sqrt_sub_sq_leB1 (Nat.cast_nonneg S.card) hc
    exact mul_le_mul_of_nonneg_right hsc (hpnonneg S)
  -- the two halves of the quadratic expansion of the `(s−c−1)² + s` weight
  have quad2a : (∑ S : Finset (Fin N), (((S.card : ℝ) - c - 1) ^ 2 + (S.card : ℝ)) * p S)
      = (∑ S : Finset (Fin N), ((S.card : ℝ) - c - 1) ^ 2 * p S)
        + (∑ S : Finset (Fin N), (S.card : ℝ) * p S) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun S _ => by ring)
  have quad2b : (∑ S : Finset (Fin N), ((S.card : ℝ) - c - 1) ^ 2 * p S)
      = (∑ S : Finset (Fin N), ((S.card : ℝ) ^ 2) * p S)
        - 2 * (c + 1) * (∑ S : Finset (Fin N), (S.card : ℝ) * p S)
        + (c + 1) ^ 2 * (∑ S : Finset (Fin N), p S) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun S _ => by ring)
  -- the two right-hand sides, linearised in the three moments
  have key1 : Work.BoseFixB1S.boxPairCount V ℓ A Φ
        - (Work.BoseFixB1S.boxFlatCount V ℓ A Φ ^ 2 - Work.BoseFixB1S.boxFlatCount V ℓ A Φ)
        + (Work.BoseFixB1S.boxFlatCount V ℓ A Φ + 1 - c) ^ 2
      = (Work.BoseFixB1S.boxFlatCount V ℓ A Φ + Work.BoseFixB1S.boxPairCount V ℓ A Φ)
        + 2 * (1 - c) * Work.BoseFixB1S.boxFlatCount V ℓ A Φ + (1 - c) ^ 2 * 1 := by ring
  have key2 : Work.BoseFixB1S.boxPairCount V ℓ A Φ
        - (Work.BoseFixB1S.boxFlatCount V ℓ A Φ ^ 2 - Work.BoseFixB1S.boxFlatCount V ℓ A Φ)
        + (Work.BoseFixB1S.boxFlatCount V ℓ A Φ - c - 1) ^ 2
        + Work.BoseFixB1S.boxFlatCount V ℓ A Φ
      = (Work.BoseFixB1S.boxFlatCount V ℓ A Φ + Work.BoseFixB1S.boxPairCount V ℓ A Φ)
        - 2 * (c + 1) * Work.BoseFixB1S.boxFlatCount V ℓ A Φ + (c + 1) ^ 2 * 1
        + Work.BoseFixB1S.boxFlatCount V ℓ A Φ := by ring
  constructor
  · calc (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
          (Work.UBBInputs8.boxPInd V A i Φ)) x ^ 2)
        = ∑ S : Finset (Fin N), (S.card : ℝ) *
            (Real.sqrt ((S.card : ℝ) + 1) - Real.sqrt c) ^ 2 * p S := hT
      _ ≤ ∑ S : Finset (Fin N), ((S.card : ℝ) + 1 - c) ^ 2 * p S := step1
      _ = (∑ S : Finset (Fin N), ((S.card : ℝ) ^ 2) * p S)
            + 2 * (1 - c) * (∑ S : Finset (Fin N), (S.card : ℝ) * p S)
            + (1 - c) ^ 2 * (∑ S : Finset (Fin N), p S) := quad1
      _ = (Work.BoseFixB1S.boxFlatCount V ℓ A Φ + Work.BoseFixB1S.boxPairCount V ℓ A Φ)
            + 2 * (1 - c) * Work.BoseFixB1S.boxFlatCount V ℓ A Φ + (1 - c) ^ 2 * 1 := by
          rw [hM2, hM1, hM0]
      _ = (Work.BoseFixB1S.boxPairCount V ℓ A Φ
            - (Work.BoseFixB1S.boxFlatCount V ℓ A Φ ^ 2
                - Work.BoseFixB1S.boxFlatCount V ℓ A Φ))
          + (Work.BoseFixB1S.boxFlatCount V ℓ A Φ + 1 - c) ^ 2 := key1.symm
  · calc (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
          (Work.UBBInputs8.boxPInd V A i Φ)) x ^ 2)
        = ∑ S : Finset (Fin N), (S.card : ℝ) *
            (Real.sqrt ((S.card : ℝ) + 1) - Real.sqrt c) ^ 2 * p S := hT
      _ ≤ ∑ S : Finset (Fin N), (((S.card : ℝ) - c - 1) ^ 2 + (S.card : ℝ)) * p S := step2
      _ = (∑ S : Finset (Fin N), ((S.card : ℝ) - c - 1) ^ 2 * p S)
            + (∑ S : Finset (Fin N), (S.card : ℝ) * p S) := quad2a
      _ = ((∑ S : Finset (Fin N), ((S.card : ℝ) ^ 2) * p S)
            - 2 * (c + 1) * (∑ S : Finset (Fin N), (S.card : ℝ) * p S)
            + (c + 1) ^ 2 * (∑ S : Finset (Fin N), p S))
            + (∑ S : Finset (Fin N), (S.card : ℝ) * p S) := by rw [quad2b]
      _ = ((Work.BoseFixB1S.boxFlatCount V ℓ A Φ + Work.BoseFixB1S.boxPairCount V ℓ A Φ)
            - 2 * (c + 1) * Work.BoseFixB1S.boxFlatCount V ℓ A Φ + (c + 1) ^ 2 * 1)
            + Work.BoseFixB1S.boxFlatCount V ℓ A Φ := by
          rw [hM2, hM1, hM0]
      _ = (Work.BoseFixB1S.boxPairCount V ℓ A Φ
            - (Work.BoseFixB1S.boxFlatCount V ℓ A Φ ^ 2
                - Work.BoseFixB1S.boxFlatCount V ℓ A Φ))
          + (Work.BoseFixB1S.boxFlatCount V ℓ A Φ - c - 1) ^ 2
          + Work.BoseFixB1S.boxFlatCount V ℓ A Φ := key2.symm

theorem boxMtMomentBoundsB1 {N : ℕ} {ℓ V c : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V) (hc : 1 ≤ c)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hnorm : (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) = 1) :
    (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
          (Work.UBBInputs8.boxPInd V A i Φ)) x ^ 2)
        ≤ (Work.BoseFixB1S.boxPairCount V ℓ A Φ
            - (Work.BoseFixB1S.boxFlatCount V ℓ A Φ ^ 2
                - Work.BoseFixB1S.boxFlatCount V ℓ A Φ))
          + (Work.BoseFixB1S.boxFlatCount V ℓ A Φ + 1 - c) ^ 2
    ∧ (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1S.n0FunOp V A (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c)
          (Work.UBBInputs8.boxPInd V A i Φ)) x ^ 2)
        ≤ (Work.BoseFixB1S.boxPairCount V ℓ A Φ
            - (Work.BoseFixB1S.boxFlatCount V ℓ A Φ ^ 2
                - Work.BoseFixB1S.boxFlatCount V ℓ A Φ))
          + (Work.BoseFixB1S.boxFlatCount V ℓ A Φ - c - 1) ^ 2
          + Work.BoseFixB1S.boxFlatCount V ℓ A Φ := by
  have hΦG : Work.BoseFixB1S.GoodState ℓ Φ := by
    obtain ⟨C, hC⟩ :=
      (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn hΦc.continuousOn
    exact ⟨hΦc.measurable, C, fun x hx => by simpa [Real.norm_eq_abs] using hC x hx⟩
  exact boxMtMomentArithB1 hℓ hV hc hA hVeq hAc hΦc hnorm
    (n0FunOpSumSpectralB1 hℓ hV hA hVeq hAc
      (fun r : ℝ => Real.sqrt (r + 1) - Real.sqrt c) hΦG)

end Work.BoseFixB1S
