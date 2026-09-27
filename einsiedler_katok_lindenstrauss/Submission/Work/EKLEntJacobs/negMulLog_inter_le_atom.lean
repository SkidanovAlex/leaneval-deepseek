import Mathlib
import Submission.Work.EKLEntJacobs.negMulLog_matrix_le
import Submission.Work.EKLComp.Core

open MeasureTheory

namespace Work.EKLEntJacobs

/-- Entropy subadditivity on a single atom: for finite measurable partitions `A : ι → Set X`,
`C : κ → Set X` of a probability space and a measurable set `B0`, the normalised joint masses
`p i k = (μ (A i ∩ C k ∩ B0)).toReal * ((μ B0).toReal)⁻¹` form a sub-stochastic matrix (row sums
`(μ (A i ∩ B0)).toReal * ((μ B0).toReal)⁻¹`, column sums
`(μ (C k ∩ B0)).toReal * ((μ B0).toReal)⁻¹`, total `≤ 1` because `∑ i, μ (A i ∩ B0) = μ B0`), so
the matrix inequality `Work.EKLEntJacobs.negMulLog_matrix_le` gives the bound below. -/
theorem negMulLog_inter_le_atom {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] {ι κ : Type} [Fintype ι] [Fintype κ]
    {A : ι → Set X} {C : κ → Set X} (hA : Work.EKLComp.Core.IsMPart A)
    (hC : Work.EKLComp.Core.IsMPart C) {B0 : Set X} (hB0 : MeasurableSet B0) :
    (∑ i, ∑ k, Real.negMulLog ((μ (A i ∩ C k ∩ B0)).toReal * ((μ B0).toReal)⁻¹))
      ≤ (∑ i, Real.negMulLog ((μ (A i ∩ B0)).toReal * ((μ B0).toReal)⁻¹))
        + (∑ k, Real.negMulLog ((μ (C k ∩ B0)).toReal * ((μ B0).toReal)⁻¹)) := by
  classical
  -- The row marginal: `∑ k, μ (A i ∩ C k ∩ B0) = μ (A i ∩ B0)`.
  have hrow_meas : ∀ i, ∑ k, μ (A i ∩ C k ∩ B0) = μ (A i ∩ B0) := by
    intro i
    rw [← Work.EKLComp.Core.IsMPart.sum_measure_inter μ hC ((hA.measurable i).inter hB0)]
    exact Finset.sum_congr rfl (fun k _ => by
      congr 1; ext x; simp only [Set.mem_inter_iff]; tauto)
  have hrow_real : ∀ i, ∑ k, (μ (A i ∩ C k ∩ B0)).toReal = (μ (A i ∩ B0)).toReal := by
    intro i
    rw [← ENNReal.toReal_sum (fun k _ => measure_ne_top μ _), hrow_meas i]
  have hrow : ∀ i, ∑ k, (μ (A i ∩ C k ∩ B0)).toReal * ((μ B0).toReal)⁻¹
      = (μ (A i ∩ B0)).toReal * ((μ B0).toReal)⁻¹ := by
    intro i
    rw [← Finset.sum_mul, hrow_real i]
  -- The column marginal: `∑ i, μ (A i ∩ C k ∩ B0) = μ (C k ∩ B0)`.
  have hcol_meas : ∀ k, ∑ i, μ (A i ∩ C k ∩ B0) = μ (C k ∩ B0) := by
    intro k
    rw [← Work.EKLComp.Core.IsMPart.sum_measure_inter μ hA ((hC.measurable k).inter hB0)]
    exact Finset.sum_congr rfl (fun i _ => by
      congr 1; ext x; simp only [Set.mem_inter_iff]; tauto)
  have hcol_real : ∀ k, ∑ i, (μ (A i ∩ C k ∩ B0)).toReal = (μ (C k ∩ B0)).toReal := by
    intro k
    rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top μ _), hcol_meas k]
  have hcol : ∀ k, ∑ i, (μ (A i ∩ C k ∩ B0)).toReal * ((μ B0).toReal)⁻¹
      = (μ (C k ∩ B0)).toReal * ((μ B0).toReal)⁻¹ := by
    intro k
    rw [← Finset.sum_mul, hcol_real k]
  -- The total mass: `∑ i, μ (A i ∩ B0) = μ B0`.
  have htot_real : ∑ i, ∑ k, (μ (A i ∩ C k ∩ B0)).toReal = (μ B0).toReal := by
    have h1 : ∑ i, (μ (A i ∩ B0)).toReal = (μ B0).toReal := by
      rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top μ _)]
      congr 1
      rw [← Work.EKLComp.Core.IsMPart.sum_measure_inter μ hA hB0]
      exact Finset.sum_congr rfl (fun i _ => by
        congr 1; ext x; simp only [Set.mem_inter_iff]; tauto)
    rw [Finset.sum_congr rfl (fun i _ => hrow_real i), h1]
  have htot : ∑ i, ∑ k, (μ (A i ∩ C k ∩ B0)).toReal * ((μ B0).toReal)⁻¹ ≤ 1 := by
    have hEq : ∑ i, ∑ k, (μ (A i ∩ C k ∩ B0)).toReal * ((μ B0).toReal)⁻¹
        = (μ B0).toReal * ((μ B0).toReal)⁻¹ := by
      simp_rw [← Finset.sum_mul]
      rw [htot_real]
    rw [hEq]
    rcases eq_or_lt_of_le ENNReal.toReal_nonneg with h | h
    · rw [← h, inv_zero, mul_zero]; norm_num
    · rw [mul_inv_cancel₀ (ne_of_gt h)]
  -- Nonnegativity of the entries.
  have hp : ∀ i k, 0 ≤ (μ (A i ∩ C k ∩ B0)).toReal * ((μ B0).toReal)⁻¹ :=
    fun i k => mul_nonneg ENNReal.toReal_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
  -- Apply the finite matrix inequality and identify the marginals.
  refine le_trans (Work.EKLEntJacobs.negMulLog_matrix_le
    (fun i k => (μ (A i ∩ C k ∩ B0)).toReal * ((μ B0).toReal)⁻¹) hp htot) ?_
  have e1 : (∑ i, Real.negMulLog (∑ k, (μ (A i ∩ C k ∩ B0)).toReal * ((μ B0).toReal)⁻¹))
      = ∑ i, Real.negMulLog ((μ (A i ∩ B0)).toReal * ((μ B0).toReal)⁻¹) :=
    Finset.sum_congr rfl (fun i _ => by rw [hrow i])
  have e2 : (∑ k, Real.negMulLog (∑ i, (μ (A i ∩ C k ∩ B0)).toReal * ((μ B0).toReal)⁻¹))
      = ∑ k, Real.negMulLog ((μ (C k ∩ B0)).toReal * ((μ B0).toReal)⁻¹) :=
    Finset.sum_congr rfl (fun k _ => by rw [hcol k])
  rw [e1, e2]

end Work.EKLEntJacobs
