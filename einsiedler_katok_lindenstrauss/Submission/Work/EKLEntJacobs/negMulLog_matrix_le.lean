import Mathlib
import Submission.Work.Misiurewicz.Hfam_sum_le

namespace Work.EKLEntJacobs

/-- Chain rule for `x ↦ -x log x` (universe-polymorphic form of
`Work.EKLComp.Hpart.sum_negMulLog_chain`): the total entropy of the vector `c` is the entropy
of its total mass plus the mass-weighted entropy of the normalized vector. -/
private theorem sum_negMulLog_chain' {κ : Type*} [Fintype κ] (c : κ → ℝ) (hc : ∀ j, 0 ≤ c j) :
    ∑ j, Real.negMulLog (c j) =
      Real.negMulLog (∑ j, c j)
        + ∑ j, (∑ j, c j) * Real.negMulLog (c j / (∑ j, c j)) := by
  set S := ∑ j, c j with hSdef
  have hSnonneg : 0 ≤ S := Finset.sum_nonneg (fun j _ => hc j)
  rcases eq_or_lt_of_le hSnonneg with h0 | hpos
  · have hz : ∀ j, c j = 0 := by
      intro j
      have h1 : c j ≤ ∑ j, c j :=
        Finset.single_le_sum (f := c) (fun j _ => hc j) (Finset.mem_univ j)
      rw [← hSdef, ← h0] at h1
      exact le_antisymm h1 (hc j)
    rw [← h0, Real.negMulLog_zero]
    simp [hz]
  · have hci : ∀ j, S * (c j / S) = c j := fun j => mul_div_cancel₀ (c j) (ne_of_gt hpos)
    have hsum : (∑ j, Real.negMulLog (c j)) = ∑ j, Real.negMulLog (S * (c j / S)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hci j]
    rw [hsum]
    simp only [Real.negMulLog_mul]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    rw [← Finset.sum_div, ← hSdef, div_self (ne_of_gt hpos), one_mul]

/-- Finite entropy inequality for a sub-stochastic matrix: for nonnegative reals `p i j` with
total mass at most `1`, `∑ i ∑ j negMulLog (p i j) ≤ ∑ i negMulLog (∑ j, p i j) + ∑ j negMulLog (∑ i, p i j)`.
Suggested route: the row chain rule `Work.EKLComp.Hpart.sum_negMulLog_chain` (or
`Work.EKLComp.negMulLog_row` in `Submission/Work/EKLComp/HPE3.lean`) together with concavity of
`Real.negMulLog` on `Set.Ici 0` (`Real.concaveOn_negMulLog`) applied with sub-probability weights:
if `r i ≥ 0`, `∑ i, r i ≤ 1` and `0 ≤ x i ≤ 1` then `Real.negMulLog (∑ i, r i * x i) ≥ ∑ i, r i * Real.negMulLog (x i)`. -/
theorem negMulLog_matrix_le {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι → κ → ℝ)
    (hp : ∀ i j, 0 ≤ p i j) (htot : ∑ i, ∑ j, p i j ≤ 1) :
    ∑ i, ∑ j, Real.negMulLog (p i j) ≤
      (∑ i, Real.negMulLog (∑ j, p i j)) + ∑ j, Real.negMulLog (∑ i, p i j) := by
  classical
  have hr : ∀ i, 0 ≤ ∑ j, p i j := fun i => Finset.sum_nonneg (fun j _ => hp i j)
  -- Row chain rule: split off the row mass of each row.
  have hchain : ∀ i, ∑ j, Real.negMulLog (p i j)
      = Real.negMulLog (∑ j, p i j)
        + ∑ j, (∑ j, p i j) * Real.negMulLog (p i j / (∑ j, p i j)) :=
    fun i => sum_negMulLog_chain' (fun j => p i j) (fun j => hp i j)
  -- Recombining the normalized row with the row mass recovers `p i j`.
  have hcancel : ∀ i j, (∑ j, p i j) * (p i j / (∑ j, p i j)) = p i j := by
    intro i j
    rcases eq_or_lt_of_le (hr i) with h0 | hpos
    · have hpz : p i j = 0 := by
        have hle : p i j ≤ ∑ j, p i j :=
          Finset.single_le_sum (f := fun j => p i j) (fun j _ => hp i j) (Finset.mem_univ j)
        rw [← h0] at hle
        linarith [hp i j]
      rw [← h0, hpz]
      simp
    · rw [mul_div_cancel₀ _ (ne_of_gt hpos)]
  have hLHS : ∑ i, ∑ j, Real.negMulLog (p i j)
      = (∑ i, Real.negMulLog (∑ j, p i j))
        + ∑ i, ∑ j, (∑ j, p i j) * Real.negMulLog (p i j / (∑ j, p i j)) := by
    simp_rw [hchain]
    rw [Finset.sum_add_distrib]
  -- Jensen step: the weighted entropy of the columns is at most the entropy of the column sums.
  have hdouble : ∑ i, ∑ j, (∑ j, p i j) * Real.negMulLog (p i j / (∑ j, p i j))
      ≤ ∑ j, Real.negMulLog (∑ i, p i j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro j _
    have hle := Work.Misiurewicz.sum_mul_negMulLog_le (κ := ι)
      (c := fun i => ∑ j, p i j) (x := fun i => p i j / (∑ j, p i j))
      (fun i => hr i) (fun i => div_nonneg (hp i j) (hr i)) htot
    calc ∑ i, (∑ j, p i j) * Real.negMulLog (p i j / (∑ j, p i j))
        ≤ Real.negMulLog (∑ i, (∑ j, p i j) * (p i j / (∑ j, p i j))) := hle
      _ = Real.negMulLog (∑ i, p i j) := by
          congr 1
          exact Finset.sum_congr rfl (fun i _ => hcancel i j)
  calc ∑ i, ∑ j, Real.negMulLog (p i j)
      = (∑ i, Real.negMulLog (∑ j, p i j))
        + ∑ i, ∑ j, (∑ j, p i j) * Real.negMulLog (p i j / (∑ j, p i j)) := hLHS
    _ ≤ (∑ i, Real.negMulLog (∑ j, p i j)) + ∑ j, Real.negMulLog (∑ i, p i j) :=
        by linarith [hdouble]

end Work.EKLEntJacobs
