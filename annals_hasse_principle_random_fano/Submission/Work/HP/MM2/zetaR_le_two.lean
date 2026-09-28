import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.MDEstimates.sumIccInvSq

namespace Work.HP.MM2

/-- Summability of `k ↦ 1/((k:ℝ)+1)^2`, obtained by shifting the standard
`p`-series `∑ 1/n^s` (`s = 2 > 1`). -/
private lemma summable_inv_sq_succ : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ 2) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num : (1 : ℕ) < 2)
  have h2 : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 1).mpr h
  simpa [Nat.cast_add, Nat.cast_one] using h2

/-- Summability of `k ↦ 1/((k:ℝ)+1)^m` for `m ≥ 2`, dominating the series by the
square case. -/
private lemma summable_inv_pow_succ (m : ℕ) (hm : 2 ≤ m) :
    Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ m) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) summable_inv_sq_succ
  have hx : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have := Nat.cast_nonneg k (α := ℝ); linarith
  have h : ((k : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 1) ^ m := pow_le_pow_right₀ hx hm
  have hpos : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
  exact one_div_le_one_div_of_le hpos h

/-- Reindexing identity: `∑' k, 1/((k+1)^2) = ∑' l, 1/l^2` (the `l = 0` term of the
right-hand series vanishes). -/
private lemma tsum_inv_sq_succ_eq :
    (∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + 1) ^ 2) = ∑' l : ℕ, (1 : ℝ) / (l : ℝ) ^ 2 := by
  have h : Summable (fun l : ℕ => (1 : ℝ) / (l : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num : (1 : ℕ) < 2)
  have hz := h.tsum_eq_zero_add
  rw [hz]
  simp only [Nat.cast_zero]
  have hz0 : (1 : ℝ) / (0 : ℝ) ^ 2 = 0 := by norm_num
  rw [hz0, zero_add]
  apply tsum_congr
  intro n
  push_cast
  ring_nf

/-- The `p`-series at `p = 2` is bounded by `2`: every finite partial sum is at most
`2` (via `MDEstimates.sumIccInvSq`), so the same holds for the full sum. -/
private lemma tsum_inv_sq_le_two : (∑' l : ℕ, (1 : ℝ) / (l : ℝ) ^ 2) ≤ 2 := by
  have hsq : Summable (fun l : ℕ => (1 : ℝ) / (l : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num : (1 : ℕ) < 2)
  refine Summable.tsum_le_of_sum_le hsq (fun s => ?_)
  set N := s.sup id with hN
  have hsub : s ⊆ Finset.Icc 0 N := by
    intro l hl
    simp only [Finset.mem_Icc]
    exact ⟨Nat.zero_le l, Finset.le_sup (f := id) hl⟩
  have h1 : ∑ l ∈ s, (1 : ℝ) / (l : ℝ) ^ 2 ≤ ∑ l ∈ Finset.Icc 0 N, (1 : ℝ) / (l : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
  refine le_trans h1 ?_
  have hI := Finset.insert_Icc_add_one_left_eq_Icc (show (0 : ℕ) ≤ N from Nat.zero_le N)
  rw [← hI, Finset.sum_insert (by simp [Finset.mem_Icc])]
  have hz : (1 : ℝ) / (((0 : ℕ)) : ℝ) ^ 2 = 0 := by norm_num
  rw [hz, zero_add]
  exact Work.HP.MDEstimates.sumIccInvSq N

/-- `zetaR m = Σ'_{k≥0} 1/(k+1)^m` is at most `2` for `m ≥ 2`. Termwise `1/(k+1)^m ≤ 1/(k+1)^2`,
and the `k = 0` term is `1` while the tail `k ≥ 1` telescopes: `1/(k+1)^2 ≤ 1/(k+1) - 1/(k+2)`,
so the total is at most `1 + 1 = 2`. Equivalently: bound every finite partial sum with
`MDEstimates.sumIccInvSq` and use `Summable.tsum_le_of_sum_le`. -/
theorem zetaR_le_two (m : ℕ) (hm : 2 ≤ m) : zetaR m ≤ 2 := by
  rw [zetaR]
  calc ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + 1) ^ m
      ≤ ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + 1) ^ 2 := by
        refine Summable.tsum_le_tsum (fun k => ?_) (summable_inv_pow_succ m hm) summable_inv_sq_succ
        have hx : (1 : ℝ) ≤ (k : ℝ) + 1 := by
          have := Nat.cast_nonneg k (α := ℝ); linarith
        have h : ((k : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 1) ^ m := pow_le_pow_right₀ hx hm
        have hpos : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
        exact one_div_le_one_div_of_le hpos h
    _ = ∑' l : ℕ, (1 : ℝ) / (l : ℝ) ^ 2 := tsum_inv_sq_succ_eq
    _ ≤ 2 := tsum_inv_sq_le_two

end Work.HP.MM2
