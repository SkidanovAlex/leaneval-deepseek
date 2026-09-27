import Submission.Work.EKLComp.HPE
import Submission.Work.EKLComp.condExp_partSigmaFam

/-!
# C3 (E5) — the entropy chain rule `H(A ∨ B) = H(A) + H(B | σ(A))`
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 2000000

namespace Work.EKLComp.Core

open Work.EKLContract

variable {X : Type} [mX : MeasurableSpace X]

/-! ## 12. The sum of the indicators of a finite partition -/

theorem partIdx_sum_indicator {ι : Type*} [Fintype ι] (A : ι → Set X) (hA : IsMPart A)
    (c : ι → ℝ) (x : X) :
    (∑ j : ι, (Set.indicator (A j) (fun _ : X => c j) x : ℝ)) = c (partIdx A hA x) := by
  classical
  have h1 : ∀ j ∈ (Finset.univ : Finset ι),
      (Set.indicator (A j) (fun _ : X => c j) x : ℝ) = if partIdx A hA x = j then c j else 0 := by
    intro j _
    by_cases h : x ∈ A j
    · rw [Set.indicator_of_mem h, if_pos (partIdx_unique A hA x h).symm]
    · rw [Set.indicator_of_notMem h]
      by_cases h2 : partIdx A hA x = j
      · exfalso
        rw [← h2] at h
        exact h (partIdx_mem A hA x)
      · rw [if_neg h2]
  rw [Finset.sum_congr rfl h1,
    Finset.sum_eq_single (partIdx A hA x) (fun j _ hj => if_neg (Ne.symm hj))
      (fun h => absurd (Finset.mem_univ _) h),
    if_pos rfl]

/-! ## 13. The integral of `negMulLog` of a sum of indicators -/

theorem integral_negMulLog_indicator_sum (μ : Measure X) [IsProbabilityMeasure μ] {ι : Type*}
    [Fintype ι] (A : ι → Set X) (hA : IsMPart A) (c : ι → ℝ) :
    ∫ x, Real.negMulLog (∑ j : ι, (Set.indicator (A j) (fun _ : X => c j) x : ℝ)) ∂μ
      = ∑ i, (μ (A i)).toReal * Real.negMulLog (c i) := by
  classical
  have hpoint : ∀ x, Real.negMulLog (∑ j : ι, (Set.indicator (A j) (fun _ : X => c j) x : ℝ))
      = ∑ i : ι, (Set.indicator (A i) (fun _ : X => Real.negMulLog (c i)) x : ℝ) := by
    intro x
    rw [partIdx_sum_indicator A hA c x,
      ← partIdx_sum_indicator A hA (fun i => Real.negMulLog (c i)) x]
  calc ∫ x, Real.negMulLog (∑ j : ι, (Set.indicator (A j) (fun _ : X => c j) x : ℝ)) ∂μ
      = ∫ x, (∑ i : ι,
          (Set.indicator (A i) (fun _ : X => Real.negMulLog (c i)) x : ℝ)) ∂μ := by
        congr 1
        funext x
        exact hpoint x
    _ = ∑ i : ι, ∫ x, (Set.indicator (A i) (fun _ : X => Real.negMulLog (c i)) x : ℝ) ∂μ :=
        integral_finset_sum _ fun i _ => (integrable_const _).indicator (hA.measurable i)
    _ = ∑ i, (μ (A i)).toReal * Real.negMulLog (c i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_indicator (hA.measurable i), setIntegral_const]
        simp [Measure.real, smul_eq_mul, mul_comm]

/-! ## 14. The per-row algebra -/

theorem negMulLog_row {κ : Type*} [Fintype κ] {a : ℝ} {c : κ → ℝ}
    (ha : 0 ≤ a) (hc : ∀ j, 0 ≤ c j) (hsum : ∑ j, c j = a) :
    (∑ j, Real.negMulLog (c j)) = Real.negMulLog a + ∑ j, a * Real.negMulLog (c j / a) := by
  rcases eq_or_lt_of_le ha with h0 | hpos
  · have hz : ∀ j, c j = 0 := by
      intro j
      have h1 : c j ≤ ∑ i, c i :=
        Finset.single_le_sum (f := c) (fun i _ => hc i) (Finset.mem_univ j)
      rw [hsum, ← h0] at h1
      exact le_antisymm h1 (hc j)
    rw [← h0]
    simp [hz]
  · have h1 : ∑ j, c j / a = 1 := by
      rw [← Finset.sum_div, hsum, div_self (ne_of_gt hpos)]
    have h2 : ∀ j, c j = a * (c j / a) := by
      intro j; field_simp
    calc ∑ j, Real.negMulLog (c j) = ∑ j, Real.negMulLog (a * (c j / a)) := by
          exact Finset.sum_congr rfl fun j _ => congrArg Real.negMulLog (h2 j)
      _ = ∑ j, ((c j / a) * Real.negMulLog a + a * Real.negMulLog (c j / a)) := by
          exact Finset.sum_congr rfl fun j _ => Real.negMulLog_mul a (c j / a)
      _ = (∑ j, (c j / a)) * Real.negMulLog a + a * ∑ j, Real.negMulLog (c j / a) := by
          rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      _ = Real.negMulLog a + ∑ j, a * Real.negMulLog (c j / a) := by
          rw [h1, one_mul, Finset.mul_sum]

/-! ## 15. The chain rule -/

theorem HcondFam_join' (μ : Measure X) [IsProbabilityMeasure μ] {ι κ : Type} [Fintype ι]
    [Fintype κ] (A : ι → Set X) (B : κ → Set X) (hA : IsMPart A) (hB : IsMPart B) :
    Hfam μ (fun p : ι × κ => A p.1 ∩ B p.2) = Hfam μ A + HcondFam X μ B (partSigmaFam A) := by
  classical
  have hae : ∀ j : κ, condExp (partSigmaFam A) μ ((B j).indicator (fun _ => (1:ℝ))) =ᵐ[μ]
      fun x => ∑ i, (A i).indicator
        (fun _ => ((μ (A i)).toReal)⁻¹ * (μ (B j ∩ A i)).toReal) x :=
    fun j => Work.EKLComp.condExp_partSigmaFam μ hA (B j) (hB.measurable j)
  have hint : ∀ j : κ, Integrable (fun x => Real.negMulLog
      (condExp (partSigmaFam A) μ ((B j).indicator (fun _ => (1:ℝ))) x)) μ := by
    intro j
    have h : Integrable (fun x => ∑ i : ι, (Set.indicator (A i)
        (fun _ : X => Real.negMulLog
          (((μ (A i)).toReal)⁻¹ * (μ (B j ∩ A i)).toReal)) x : ℝ)) μ :=
      integrable_finset_sum _ fun i _ => (integrable_const _).indicator (hA.measurable i)
    refine h.congr ?_
    filter_upwards [hae j] with x hx
    rw [hx, partIdx_sum_indicator A hA
        (fun i => ((μ (A i)).toReal⁻¹ * (μ (B j ∩ A i)).toReal)) x,
      ← partIdx_sum_indicator A hA
        (fun i => Real.negMulLog (((μ (A i)).toReal)⁻¹ * (μ (B j ∩ A i)).toReal)) x]
  have hval : HcondFam X μ B (partSigmaFam A)
      = ∑ j, ∑ i, (μ (A i)).toReal *
          Real.negMulLog (((μ (A i)).toReal)⁻¹ * (μ (B j ∩ A i)).toReal) := by
    rw [HcondFam, integral_finsetSum _ (fun j _ => hint j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_congr_ae ((hae j).mono fun x hx => by rw [hx])]
    exact integral_negMulLog_indicator_sum μ A hA _
  have hfinal : (∑ i, ∑ j, Real.negMulLog ((μ (A i ∩ B j)).toReal))
      = (∑ i, Real.negMulLog ((μ (A i)).toReal))
        + ∑ j, ∑ i, (μ (A i)).toReal *
            Real.negMulLog (((μ (A i)).toReal)⁻¹ * (μ (B j ∩ A i)).toReal) := by
    rw [Finset.sum_comm (f := fun j i => (μ (A i)).toReal *
      Real.negMulLog (((μ (A i)).toReal)⁻¹ * (μ (B j ∩ A i)).toReal))]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsum : ∑ j : κ, (μ (A i ∩ B j)).toReal = (μ (A i)).toReal := by
      rw [← ENNReal.toReal_sum (fun j _ => measure_ne_top μ _),
        IsMPart.sum_measure_inter μ hB (hA.measurable i)]
    rw [negMulLog_row (ha := ENNReal.toReal_nonneg)
      (hc := fun j => ENNReal.toReal_nonneg) hsum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Set.inter_comm, div_eq_inv_mul]
  rw [hval, Hfam, Hfam, sum_prod_univ, hfinal]

end Work.EKLComp.Core