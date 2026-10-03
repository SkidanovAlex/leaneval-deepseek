import Mathlib
import Submission.Commons.Analysis.Series.summable_log_div_rpow_three_halves

namespace Commons.NumberTheory.Sieve

/-- Termwise comparison: for a prime `p` (indeed any `p` with `z < p` and `z ≥ 1`),
`log p / p ^ 2` is bounded by `z ^ (-1/2)` times `log p / p ^ (3/2)`. -/
private lemma log_div_sq_le_inv_sqrt_mul_log_div_rpow (z : ℝ) (hz : 1 ≤ z)
    (p : ℕ) (hzp : z < (p : ℝ)) :
    Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤
      (Real.sqrt z)⁻¹ * (Real.log (p : ℝ) / (p : ℝ) ^ ((3 : ℝ) / 2)) := by
  have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
  have hxp : (0 : ℝ) < (p : ℝ) := lt_trans hz0 hzp
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    have : (1 : ℝ) < (p : ℝ) := lt_of_le_of_lt hz hzp
    exact le_of_lt this
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
  have hsz : 0 < Real.sqrt z := Real.sqrt_pos_of_pos hz0
  have hsle : Real.sqrt z ≤ Real.sqrt (p : ℝ) := Real.sqrt_le_sqrt (le_of_lt hzp)
  have h32 : (p : ℝ) ^ ((3 : ℝ) / 2) = (p : ℝ) * Real.sqrt (p : ℝ) := by
    have hsp : ((3 : ℝ) / 2) = 1 + 1 / 2 := by norm_num
    rw [hsp, Real.rpow_add hxp, Real.rpow_one, Real.sqrt_eq_rpow]
  have hsqp : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) := by
    have h := Real.sq_sqrt hxp.le
    rwa [pow_two] at h
  have hkey : (p : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt z ≤ (p : ℝ) ^ 2 := by
    calc (p : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt z
        ≤ (p : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt (p : ℝ) :=
          mul_le_mul_of_nonneg_left hsle (Real.rpow_nonneg hxp.le _)
      _ = (p : ℝ) * Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) := by rw [h32]
      _ = (p : ℝ) * (Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ)) := by ring
      _ = (p : ℝ) * (p : ℝ) := by rw [hsqp]
      _ = (p : ℝ) ^ 2 := by ring
  have hRHS : Real.log (p : ℝ) / (Real.sqrt z * (p : ℝ) ^ ((3 : ℝ) / 2)) =
      (Real.sqrt z)⁻¹ * (Real.log (p : ℝ) / (p : ℝ) ^ ((3 : ℝ) / 2)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [← hRHS]
  exact div_le_div_of_nonneg_left hlog
    (mul_pos hsz (Real.rpow_pos_of_pos hxp _)) (by rw [mul_comm]; exact hkey)

/-- The summand `log n / n ^ (3/2)` is nonnegative. -/
private lemma log_div_rpow_three_halves_nonneg (n : ℕ) :
    0 ≤ Real.log (n : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 2) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact div_nonneg (Real.log_nonneg hn1) (Real.rpow_nonneg hnpos.le _)

theorem sum_primes_log_div_sq_tail_le :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 1 ≤ z → ∀ N : ℕ,
      (∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ z < (p : ℝ)),
        Real.log (p : ℝ) / (p : ℝ) ^ 2) ≤ C / Real.sqrt z := by
  classical
  refine ⟨20, by norm_num, ?_⟩
  intro z hz N
  set S := (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ z < (p : ℝ)) with hS
  have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
  have hsz : 0 < Real.sqrt z := Real.sqrt_pos_of_pos hz0
  -- step 1: factor out `z ^ (-1/2)`
  have step1 : ∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ) ^ 2
      ≤ (Real.sqrt z)⁻¹ * ∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hzp : z < (p : ℝ) := (Finset.mem_filter.mp hp).2.2
    exact log_div_sq_le_inv_sqrt_mul_log_div_rpow z hz p hzp
  -- step 2: bound the inner sum by 20
  have hsub : S ⊆ Finset.Icc 1 N := by
    intro x hx; exact (Finset.mem_filter.mp hx).1
  have step2a : ∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ) ^ ((3 : ℝ) / 2)
      ≤ ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => log_div_rpow_three_halves_nonneg i)
  have hsumm := (Commons.Analysis.Series.summable_log_div_rpow_three_halves).1
  have hbnd := (Commons.Analysis.Series.summable_log_div_rpow_three_halves).2
  have step2b : ∑ n ∈ Finset.Icc 1 N, Real.log (n : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 2)
      ≤ ∑' n : ℕ, Real.log (n : ℝ) / (n : ℝ) ^ ((3 : ℝ) / 2) :=
    hsumm.sum_le_tsum (Finset.Icc 1 N) (fun i _ => log_div_rpow_three_halves_nonneg i)
  have step2 : ∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ) ^ ((3 : ℝ) / 2) ≤ 20 :=
    le_trans (le_trans step2a step2b) hbnd
  calc ∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ) ^ 2
      ≤ (Real.sqrt z)⁻¹ * ∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ) ^ ((3 : ℝ) / 2) := step1
    _ ≤ (Real.sqrt z)⁻¹ * 20 :=
        mul_le_mul_of_nonneg_left step2 (inv_nonneg.mpr hsz.le)
    _ = 20 / Real.sqrt z := by rw [div_eq_mul_inv]; ring

end Commons.NumberTheory.Sieve
