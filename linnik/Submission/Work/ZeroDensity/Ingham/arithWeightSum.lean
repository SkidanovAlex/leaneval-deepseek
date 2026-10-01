import Mathlib
import Submission.Work.ZeroDensity.Ingham.sum_Icc_Icc_swap
import Submission.Work.ZeroDensity.Ingham.sum_inv_mul_log_le_logLog
import Submission.Work.ZeroDensity.Ingham.logLog_diff_le

namespace Work.ZeroDensity.Ingham

open scoped BigOperators

/-!
# The arithmetic weight sum for Ingham's zero-density bound

For `N ≥ 2` and any `b : ℕ → ℂ`,

`∑_{2 ≤ k ≤ N-1} (∑_{1 ≤ n ≤ k} ‖b n‖²) / (k log k)`
  `≤ C · ∑_{1 ≤ n ≤ N} ‖b n‖² (1 + log(2N)/log(2n))`.

Swapping the two sums, the left side is `∑_{1 ≤ n ≤ N-1} ‖b n‖² · S n`, where

`S n = ∑_{max 2 n ≤ k ≤ N-1} 1/(k log k)`,

and the content is the pointwise estimate `S n ≤ 4 (1 + log(2N)/log(2n))`.  This is the
logarithmic weight that turns the `log log` growth of `∑ 1/(k log k)` into the weights
appearing in the mean-square estimates.

The pointwise estimate is proved by the integral (telescoping) comparison, valid for `n ≥ 3`,

`∑_{n ≤ k ≤ M} 1/(k log k) ≤ log log M - log log(n-1)`
  (`sum_inv_mul_log_le_logLog`), together with the elementary comparison
`log log(N-1) - log log(n-1) ≤ 2 (1 + log(2N)/log(2n))` (`logLog_diff_le`); the
cases `n ≤ 2` are handled directly from the `k = 2` term and the same telescoping bound.
-/

/-- Pointwise bound for the logarithmic weight: for `1 ≤ n ≤ N-1`,
`∑_{max 2 n ≤ k ≤ N-1} 1/(k log k) ≤ 4 (1 + log(2N)/log(2n))`. -/
private lemma weight_pointwise (N n : ℕ) (hN : 2 ≤ N) (hn1 : 1 ≤ n) (hnN : n ≤ N - 1) :
    (∑ k ∈ Finset.Icc (max 2 n) (N - 1), (1:ℝ)/((k:ℝ)*Real.log (k:ℝ)))
      ≤ 4 * (1 + Real.log (2*(N:ℝ))/Real.log (2*(n:ℝ))) := by
  have hlog2n_pos : 0 < Real.log (2*(n:ℝ)) := by
    apply Real.log_pos
    have hn1' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
    linarith
  have hlog2N_nn : 0 ≤ Real.log (2*(N:ℝ)) := by
    apply Real.log_nonneg
    have hN' : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    linarith
  have hq_nn : 0 ≤ Real.log (2*(N:ℝ)) / Real.log (2*(n:ℝ)) :=
    div_nonneg hlog2N_nn (le_of_lt hlog2n_pos)
  rcases lt_or_ge n 3 with hn3 | hn3
  · -- case `n ≤ 2`
    have hn2 : n ≤ 2 := by omega
    have hmax : max 2 n = 2 := by omega
    rw [hmax]
    have hlog2_ge_half : (1:ℝ)/2 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hg2 : (1:ℝ)/((2:ℝ)*Real.log 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have hlog2le1 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
    have hlog4le2 : Real.log 4 ≤ 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; linarith
    have hnegloglog2 : -Real.log (Real.log 2) ≤ 1 := by
      have hpos : (0:ℝ) < Real.log 2 := by linarith
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (Real.log 2)⁻¹ by positivity)
      rw [Real.log_inv] at h
      have h2 : (Real.log 2)⁻¹ ≤ 2 := by
        rw [inv_le_iff_one_le_mul₀ hpos]; linarith
      linarith
    have hS : (∑ k ∈ Finset.Icc 2 (N - 1), (1:ℝ)/((k:ℝ)*Real.log (k:ℝ)))
        ≤ 2 + Real.log (2*(N:ℝ)) := by
      rcases lt_or_ge (N-1) 3 with hN3 | hN3
      · -- `N - 1 ≤ 2`
        have h2 : (∑ k ∈ Finset.Icc 2 (N-1), (1:ℝ)/((k:ℝ)*Real.log (k:ℝ)))
            ≤ ∑ k ∈ Finset.Icc (2:ℕ) 2, (1:ℝ)/((k:ℝ)*Real.log (k:ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.Icc_subset_Icc_right (by omega : N-1 ≤ 2))
          intro i hi _
          have hi2 : i = 2 := by
            rw [Finset.Icc_self, Finset.mem_singleton] at hi; exact hi
          rw [hi2]; positivity
        rw [Finset.Icc_self, Finset.sum_singleton] at h2
        have hb : (1:ℝ)/((↑(2:ℕ):ℝ)*Real.log (↑(2:ℕ):ℝ)) ≤ 1 := by
          rw [div_le_one (by positivity)]
          push_cast
          have := Real.log_two_gt_d9; linarith
        linarith [h2, hb, hlog2N_nn]
      · -- `3 ≤ N - 1`
        have hsplit : (∑ k ∈ Finset.Icc 2 (N-1), (1:ℝ)/((k:ℝ)*Real.log (k:ℝ)))
            = (1:ℝ)/((2:ℝ)*Real.log 2)
              + ∑ k ∈ Finset.Icc 3 (N-1), (1:ℝ)/((k:ℝ)*Real.log (k:ℝ)) := by
          have hs : Finset.Icc 2 (N-1) = insert 2 (Finset.Icc 3 (N-1)) := by
            ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hs, Finset.sum_insert (by simp)]
          norm_num
        rw [hsplit]
        have ht := sum_inv_mul_log_le_logLog (N-1) 3 (by norm_num) (by omega)
        have hll : Real.log (Real.log (((N-1:ℕ):ℝ))) ≤ Real.log (2*(N:ℝ)) := by
          have hN1pos : (0:ℝ) < ((N-1:ℕ):ℝ) := by
            have : (0:ℕ) < N-1 := by omega
            exact_mod_cast this
          have hlogN1pos : 0 < Real.log (((N-1:ℕ):ℝ)) :=
            Real.log_pos (by exact_mod_cast (by omega : 1 < N-1))
          apply Real.log_le_log hlogN1pos
          have hN1le : ((N-1:ℕ):ℝ) ≤ 2*(N:ℝ) := by
            have h1 : ((N-1:ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.sub_le N 1
            have h2 : (0:ℝ) ≤ (N:ℝ) := by positivity
            linarith
          have h3 := Real.log_le_sub_one_of_pos hN1pos
          linarith
        linarith [ht, hll, hg2, hnegloglog2]
    have hlog2n_le2 : Real.log (2*(n:ℝ)) ≤ 2 := by
      have hle : (2:ℝ)*(n:ℝ) ≤ 4 := by
        have : (n:ℝ) ≤ 2 := by exact_mod_cast hn2
        linarith
      exact le_trans (Real.log_le_log (by positivity) hle) hlog4le2
    have hq_ge : Real.log (2*(N:ℝ))/2 ≤ Real.log (2*(N:ℝ))/Real.log (2*(n:ℝ)) :=
      div_le_div_of_nonneg_left hlog2N_nn hlog2n_pos hlog2n_le2
    linarith [hS, hq_ge]
  · -- case `n ≥ 3`
    have hmax : max 2 n = n := by omega
    rw [hmax]
    have ht := sum_inv_mul_log_le_logLog (N-1) n hn3 hnN
    have hc := logLog_diff_le N n hN hn3 hnN
    linarith [ht, hc, hq_nn]

theorem arithWeightSum :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 2 ≤ N → ∀ (b : ℕ → ℂ),
      (∑ k ∈ Finset.Icc 2 (N - 1),
          (∑ n ∈ Finset.Icc 1 k, ‖b n‖ ^ 2) / ((k : ℝ) * Real.log (k : ℝ)))
        ≤ C * ∑ n ∈ Finset.Icc 1 N,
            ‖b n‖ ^ 2 * (1 + Real.log (2 * (N : ℝ)) / Real.log (2 * (n : ℝ))) := by
  refine ⟨4, by norm_num, ?_⟩
  intro N hN b
  have step1 : (∑ k ∈ Finset.Icc 2 (N-1),
        (∑ n ∈ Finset.Icc 1 k, ‖b n‖^2)/((k:ℝ)*Real.log (k:ℝ)))
      = ∑ k ∈ Finset.Icc 2 (N-1),
          ∑ n ∈ Finset.Icc 1 k, ‖b n‖^2 * (1/((k:ℝ)*Real.log (k:ℝ))) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [div_eq_mul_one_div, Finset.sum_mul]
  have step2 : (∑ k ∈ Finset.Icc 2 (N-1),
        ∑ n ∈ Finset.Icc 1 k, ‖b n‖^2 * (1/((k:ℝ)*Real.log (k:ℝ))))
      = ∑ n ∈ Finset.Icc 1 (N-1),
          ∑ k ∈ Finset.Icc (max 2 n) (N-1), ‖b n‖^2 * (1/((k:ℝ)*Real.log (k:ℝ))) :=
    sum_Icc_Icc_swap (N-1) (fun n k => ‖b n‖^2 * (1/((k:ℝ)*Real.log (k:ℝ))))
  have step3 : (∑ n ∈ Finset.Icc 1 (N-1),
        ∑ k ∈ Finset.Icc (max 2 n) (N-1), ‖b n‖^2 * (1/((k:ℝ)*Real.log (k:ℝ))))
      = ∑ n ∈ Finset.Icc 1 (N-1),
          ‖b n‖^2 * (∑ k ∈ Finset.Icc (max 2 n) (N-1), (1/((k:ℝ)*Real.log (k:ℝ)))) := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [Finset.mul_sum]
  have hE : (∑ k ∈ Finset.Icc 2 (N-1),
        (∑ n ∈ Finset.Icc 1 k, ‖b n‖^2)/((k:ℝ)*Real.log (k:ℝ)))
      = ∑ n ∈ Finset.Icc 1 (N-1),
          ‖b n‖^2 * (∑ k ∈ Finset.Icc (max 2 n) (N-1), (1/((k:ℝ)*Real.log (k:ℝ)))) := by
    rw [step1, step2, step3]
  have hstep : ∀ n ∈ Finset.Icc 1 (N-1),
      ‖b n‖^2 * (∑ k ∈ Finset.Icc (max 2 n) (N-1), (1/((k:ℝ)*Real.log (k:ℝ))))
        ≤ ‖b n‖^2 * (4*(1 + Real.log (2*(N:ℝ))/Real.log (2*(n:ℝ)))) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnN : n ≤ N-1 := (Finset.mem_Icc.mp hn).2
    exact mul_le_mul_of_nonneg_left (weight_pointwise N n hN hn1 hnN) (sq_nonneg _)
  calc (∑ k ∈ Finset.Icc 2 (N-1),
        (∑ n ∈ Finset.Icc 1 k, ‖b n‖^2)/((k:ℝ)*Real.log (k:ℝ)))
      = ∑ n ∈ Finset.Icc 1 (N-1),
          ‖b n‖^2 * (∑ k ∈ Finset.Icc (max 2 n) (N-1), (1/((k:ℝ)*Real.log (k:ℝ)))) := hE
    _ ≤ ∑ n ∈ Finset.Icc 1 (N-1),
          ‖b n‖^2 * (4*(1 + Real.log (2*(N:ℝ))/Real.log (2*(n:ℝ)))) := Finset.sum_le_sum hstep
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
          ‖b n‖^2 * (4*(1 + Real.log (2*(N:ℝ))/Real.log (2*(n:ℝ)))) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.Icc_subset_Icc_right (by omega)
        · intro i hi _
          have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
          have hlog_pos : 0 < Real.log (2*(i:ℝ)) := by
            apply Real.log_pos
            have : (1:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi1
            linarith
          have hlogN_nn : 0 ≤ Real.log (2*(N:ℝ)) := by
            apply Real.log_nonneg
            have : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
            linarith
          have hW : 0 ≤ 1 + Real.log (2*(N:ℝ))/Real.log (2*(i:ℝ)) := by
            have : 0 ≤ Real.log (2*(N:ℝ))/Real.log (2*(i:ℝ)) :=
              div_nonneg hlogN_nn (le_of_lt hlog_pos)
            linarith
          exact mul_nonneg (sq_nonneg _) (by linarith)
    _ = 4 * ∑ n ∈ Finset.Icc 1 N,
          ‖b n‖^2 * (1 + Real.log (2*(N:ℝ))/Real.log (2*(n:ℝ))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun n hn => ?_)
        ring

end Work.ZeroDensity.Ingham
