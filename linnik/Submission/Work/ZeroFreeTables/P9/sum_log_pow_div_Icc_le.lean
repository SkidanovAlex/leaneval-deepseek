import Mathlib

namespace Work.ZeroFreeTables.P9

open Finset

/-- Elementary lower bound for `log`: for `0 < x` we have
`1 / (x + 1) ≤ log (x + 1) - log x`. -/
private lemma inv_add_one_le_log_sub_local (x : ℝ) (hx : 0 < x) :
    (x + 1)⁻¹ ≤ Real.log (x + 1) - Real.log x := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have hlog : Real.log (x + 1) - Real.log x = Real.log ((x + 1) / x) :=
    (Real.log_div (ne_of_gt hx1) (ne_of_gt hx)).symm
  rw [hlog]
  have h2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < (x + 1) / x by positivity)
  have hinv : ((x + 1) / x)⁻¹ = x / (x + 1) := inv_div (x + 1) x
  rw [hinv] at h2
  have h4 : 1 - x / (x + 1) = (x + 1)⁻¹ := by
    field_simp
    ring
  rw [h4] at h2
  exact h2

/-- The reciprocal sum over `{2, ..., N}` is bounded by `3 log N` for `N ≥ 2`. -/
private lemma sum_inv_Icc_le (N : ℕ) (hN : 2 ≤ N) :
    ∑ n ∈ Finset.Icc 2 N, (n : ℝ)⁻¹ ≤ 3 * Real.log (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base =>
      norm_num
      linarith [Real.log_two_gt_d9]
  | succ n hn ih =>
      have hsplit := Finset.sum_Icc_succ_top (a := 2) (b := n) (by omega)
        (fun k : ℕ => ((k : ℝ))⁻¹)
      rw [hsplit]
      push_cast
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        have : (1 : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hn)
        linarith
      have hkey : ((n : ℝ) + 1)⁻¹ ≤ 3 * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) := by
        have h := inv_add_one_le_log_sub_local (n : ℝ) hnpos
        have hL : 0 ≤ Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) :=
          le_trans (by positivity) h
        linarith
      linarith [ih, hkey]

theorem sum_log_pow_div_Icc_le (j N : ℕ) (hN : 2 ≤ N) :
    ∑ n ∈ Finset.Icc 2 N, (Real.log (n : ℝ)) ^ j / (n : ℝ)
      ≤ 3 * (Real.log (N : ℝ)) ^ (j + 1) := by
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hN)
  calc
    ∑ n ∈ Finset.Icc 2 N, (Real.log (n : ℝ)) ^ j / (n : ℝ)
        ≤ ∑ n ∈ Finset.Icc 2 N, (Real.log (N : ℝ)) ^ j * (n : ℝ)⁻¹ := by
          apply Finset.sum_le_sum
          intro n hn
          obtain ⟨hn2, hnN⟩ := Finset.mem_Icc.mp hn
          have hnpos : (0 : ℝ) < (n : ℝ) := by
            have : (1 : ℝ) ≤ (n : ℝ) := by
              exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hn2)
            linarith
          have hnlogn_nonneg : 0 ≤ Real.log (n : ℝ) :=
            Real.log_nonneg (by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hn2))
          have hlog_le : Real.log (n : ℝ) ≤ Real.log (N : ℝ) :=
            Real.log_le_log (by positivity) (by exact_mod_cast hnN)
          have hp := pow_le_pow_left₀ hnlogn_nonneg hlog_le j
          calc (Real.log (n : ℝ)) ^ j / (n : ℝ)
              ≤ (Real.log (N : ℝ)) ^ j / (n : ℝ) :=
                div_le_div_of_nonneg_right hp (le_of_lt hnpos)
            _ = (Real.log (N : ℝ)) ^ j * (n : ℝ)⁻¹ := by rw [div_eq_mul_inv]
    _ = (Real.log (N : ℝ)) ^ j * ∑ n ∈ Finset.Icc 2 N, (n : ℝ)⁻¹ :=
          (Finset.mul_sum (Finset.Icc 2 N) (fun n : ℕ => ((n : ℝ))⁻¹)
            ((Real.log (N : ℝ)) ^ j)).symm
    _ ≤ (Real.log (N : ℝ)) ^ j * (3 * Real.log (N : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_inv_Icc_le N hN) (pow_nonneg hlogN_nonneg j)
    _ = 3 * (Real.log (N : ℝ)) ^ (j + 1) := by
          rw [pow_succ]
          ring

end Work.ZeroFreeTables.P9
