import Mathlib
import Submission.Commons.Analysis.Series.tail_inv_sq_le
import Submission.Commons.Analysis.Series.tail_inv_sq_summable

namespace Work.FIArea7

/-- For any finite set `S` of naturals all exceeding a positive real `c`, the sum of
`1/b²` over `S` is at most `2/c`: taking `N = min S`, the whole set is dominated by the
tail `∑_{n ≥ N} 1/n² ≤ 2/(2N-1)`, while `c < N ≤ 2N - 1`. -/
private lemma sum_inv_sq_le_of_gt {c : ℝ} (hc : 0 < c) (S : Finset ℕ)
    (hS : ∀ b ∈ S, c < (b : ℝ)) :
    ∑ b ∈ S, (1:ℝ) / (b : ℝ) ^ 2 ≤ 2 / c := by
  rcases S.eq_empty_or_nonempty with hEmpty | hne
  · rw [hEmpty]; simp only [Finset.sum_empty]; positivity
  · set N : ℕ := S.min' hne with hN
    have hNmem : N ∈ S := Finset.min'_mem S hne
    have hNmin : ∀ b ∈ S, N ≤ b := fun b hb => Finset.min'_le S b hb
    have hcN : c < (N : ℝ) := hS N hNmem
    have hNpos : 0 < N := by exact_mod_cast (lt_trans hc hcN)
    have hN1 : 1 ≤ N := hNpos
    have hNposR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hc2N : c < 2 * (N : ℝ) - 1 := by nlinarith
    have hbound0 : ∑ b ∈ S, (1:ℝ)/(b:ℝ)^2
        = ∑ b ∈ S, (if N ≤ b then (1:ℝ)/(b:ℝ)^2 else 0) := by
      refine Finset.sum_congr rfl (fun b hb => ?_)
      rw [if_pos (hNmin b hb)]
    have hbound : ∑ b ∈ S, (1:ℝ)/(b:ℝ)^2
        ≤ ∑' n : ℕ, (if N ≤ n then (1:ℝ)/(n:ℝ)^2 else 0) := by
      rw [hbound0]
      exact Summable.sum_le_tsum S (fun n _ => by split <;> positivity)
        (Commons.Analysis.Series.tail_inv_sq_summable N)
    have htail := Commons.Analysis.Series.tail_inv_sq_le N hN1
    have hmain : ∑ b ∈ S, (1:ℝ)/(b:ℝ)^2 ≤ 2/(2*(N:ℝ)-1) := le_trans hbound htail
    exact le_trans hmain (le_of_lt (div_lt_div_of_pos_left (by norm_num) hc hc2N))

/-- The sub-sum of `1/b²` over the integers `b ≤ B` exceeding `c` is at most `2/c`. -/
theorem sum_inv_sq_filter_le (B : ℕ) (c : ℝ) (hc : 0 < c) :
    (∑ b ∈ (Finset.Icc 1 B).filter (fun b : ℕ => c < (b : ℝ)), (1:ℝ) / (b : ℝ) ^ 2)
      ≤ 2 / c := by
  refine sum_inv_sq_le_of_gt hc _ (fun b hb => ?_)
  exact (Finset.mem_filter.mp hb).2

end Work.FIArea7
