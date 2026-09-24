import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiDelay

namespace Work.NumberTheory.Chen.APSwitchUpper

open Finset
open scoped BigOperators

noncomputable section

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Reindexing the tail sum: the `range`-indexed sum equals the `Icc`-indexed sum
after the substitution `i ↦ i + 1`. -/
private theorem sum_range_eq_sum_Icc (j : ℕ) (X : ℝ) :
    (∑ i ∈ Finset.range (j + 1), profTail (2 * i + 1) X)
      = ∑ i ∈ Finset.Icc 1 (j + 1), profTail (2 * i - 1) X := by
  refine Finset.sum_bij' (fun i _ => i + 1) (fun i _ => i - 1) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_range] at ha
    rw [Finset.mem_Icc]
    omega
  · intro a ha
    rw [Finset.mem_Icc] at ha
    rw [Finset.mem_range]
    omega
  · intro a ha
    rw [Finset.mem_range] at ha
    omega
  · intro a ha
    rw [Finset.mem_Icc] at ha
    omega
  · intro a ha
    rw [Finset.mem_range] at ha
    have h : 2 * (a + 1) - 1 = 2 * a + 1 := by omega
    rw [h]

/-- The base term: `s · profC 0 s = (3 − s)·1_{s ≤ 3}` for `s ≥ 1`. -/
private theorem mul_profC_zero (s : ℝ) (hs : 1 ≤ s) :
    s * profC 0 s = if s ≤ 3 then (3 - s) else 0 := by
  rw [profC_zero]
  by_cases h3 : s ≤ 3
  · rw [if_pos ⟨hs, h3⟩, if_pos h3]
    exact mul_div_cancel₀ (3 - s) (by linarith)
  · rw [if_neg (fun h => h3 h.2), if_neg h3, mul_zero]

theorem profC_summed_delay :
    (∀ (j : ℕ) (s : ℝ), 1 ≤ s → s * Work.NumberTheory.Chen.APSwitchUpper.evenSum (j + 1) s
        = (if s ≤ 3 then (3 - s) else 0)
          + ∑ i ∈ Finset.Icc 1 (j + 1),
              Work.NumberTheory.Chen.APSwitchUpper.profTail (2 * i - 1) (max (s - 1) 2))
    ∧ (∀ (j : ℕ) (s : ℝ), 2 ≤ s → s * Work.NumberTheory.Chen.APSwitchUpper.oddSum j s
        = ∑ i ∈ Finset.range (j + 1),
            Work.NumberTheory.Chen.APSwitchUpper.profTail (2 * i) (s - 1)) := by
  constructor
  · intro j s hs
    have h0 : s * profC 0 s = if s ≤ 3 then (3 - s) else 0 := mul_profC_zero s hs
    have hsplit : evenSum (j + 1) s
        = profC 0 s + ∑ i ∈ Finset.range (j + 1), profC (2 * (i + 1)) s := by
      rw [evenSum, Finset.sum_range_succ']
      simp [add_comm]
    have hsum : (∑ i ∈ Finset.range (j + 1), s * profC (2 * (i + 1)) s)
        = ∑ i ∈ Finset.Icc 1 (j + 1), profTail (2 * i - 1) (max (s - 1) 2) := by
      refine (Finset.sum_congr rfl ?_).trans (sum_range_eq_sum_Icc j (max (s - 1) 2))
      intro i _
      exact profC_even_mul i s hs
    rw [hsplit, mul_add, Finset.mul_sum, h0, hsum]
  · intro j s hs
    rw [oddSum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => profC_odd_mul i s hs)

end

end Work.NumberTheory.Chen.APSwitchUpper
