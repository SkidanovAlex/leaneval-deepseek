import Mathlib
import Submission.Commons.NumberTheory.Moebius.moebius_recip_sum_exp_decay
import Submission.Commons.Analysis.Asymptotics.sum_exp_neg_sqrt_log_div_le

namespace Commons.NumberTheory.Moebius

open Finset

/-- Partial sums of `μ n / n`. -/
noncomputable def muRecipSum (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)

/-- The log-weighted Möbius reciprocal sum. -/
noncomputable def logWeightedMuSum (x : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 x,
    (ArithmeticFunction.moebius m : ℝ) * (Real.log (x : ℝ) - Real.log (m : ℝ)) / (m : ℝ)

lemma logWeightedMuSum_one : logWeightedMuSum 1 = 0 := by
  simp [logWeightedMuSum]

lemma logWeightedMuSum_succ {x : ℕ} (hx : 1 ≤ x) :
    logWeightedMuSum (x + 1) =
      logWeightedMuSum x + muRecipSum x * (Real.log ((x : ℝ) + 1) - Real.log (x : ℝ)) := by
  have key : ∀ m : ℕ,
      (ArithmeticFunction.moebius m : ℝ) * (Real.log ((x:ℝ)+1) - Real.log (m:ℝ)) / (m:ℝ)
      = (ArithmeticFunction.moebius m : ℝ) * (Real.log (x:ℝ) - Real.log (m:ℝ)) / (m:ℝ)
        + (ArithmeticFunction.moebius m : ℝ)/(m:ℝ)
            * (Real.log ((x:ℝ)+1) - Real.log (x:ℝ)) := by
    intro m; ring
  unfold logWeightedMuSum muRecipSum
  rw [Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ x + 1)]
  rw [show (ArithmeticFunction.moebius (x + 1) : ℝ) *
        (Real.log ((x + 1 : ℕ) : ℝ) - Real.log ((x + 1 : ℕ) : ℝ)) / ((x + 1 : ℕ) : ℝ) = 0 by
      simp, add_zero]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [Finset.sum_congr rfl (fun m _ => key m)]
  rw [Finset.sum_add_distrib, Finset.sum_mul]

/-- Abel-style summation by parts: the log-weighted Möbius reciprocal sum is the
log-telescoped sum of the partial sums `muRecipSum`. -/
lemma logWeightedMuSum_eq (x : ℕ) :
    logWeightedMuSum (x + 1) =
      ∑ n ∈ Finset.Icc 1 x, muRecipSum n * (Real.log ((n:ℝ) + 1) - Real.log (n:ℝ)) := by
  induction x with
  | zero => simp [logWeightedMuSum_one]
  | succ x ih =>
    rw [show x + 1 + 1 = (x + 1) + 1 by ring, logWeightedMuSum_succ (by omega : 1 ≤ x + 1), ih]
    rw [Finset.sum_Icc_succ_top (by omega : (1:ℕ) ≤ x + 1)]

/-- `log (n+1) - log n ≤ 1/n` for `n ≥ 1`. -/
lemma log_succ_sub_log_le_inv {n : ℕ} (hn : 1 ≤ n) :
    Real.log ((n:ℝ) + 1) - Real.log (n:ℝ) ≤ 1/(n:ℝ) := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log ((n:ℝ)+1) - Real.log (n:ℝ) = Real.log (((n:ℝ)+1)/(n:ℝ)) := by
    rw [Real.log_div (by positivity) (by positivity)]
  rw [hlog]
  have := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < ((n:ℝ)+1)/(n:ℝ))
  calc Real.log (((n:ℝ)+1)/(n:ℝ)) ≤ ((n:ℝ)+1)/(n:ℝ) - 1 := this
    _ = 1/(n:ℝ) := by field_simp; ring

/-- `|log (n+1) - log n| ≤ 1/n` for `n ≥ 1`. -/
lemma abs_log_succ_sub_log_le_inv {n : ℕ} (hn : 1 ≤ n) :
    |Real.log ((n:ℝ) + 1) - Real.log (n:ℝ)| ≤ 1/(n:ℝ) := by
  rw [abs_of_nonneg (sub_nonneg.mpr ?_)]
  · exact log_succ_sub_log_le_inv hn
  · have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    exact Real.log_le_log hnpos (by linarith)

/-- Uniform exponential-decay bound for the partial sums `muRecipSum n` (valid also at `n = 1`). -/
lemma muRecipSum_decay {c C0 : ℝ} (_hc : 0 < c) (_hC0 : 0 < C0)
    (hdecay : ∀ x : ℝ, 2 ≤ x →
      |∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)|
        ≤ C0 * Real.exp (-(c * Real.sqrt (Real.log x)))) :
    ∀ n : ℕ, 1 ≤ n →
      |muRecipSum n| ≤ max C0 1 * Real.exp (-(c * Real.sqrt (Real.log (n:ℝ)))) := by
  intro n hn
  rcases eq_or_lt_of_le hn with h1 | h2
  · subst h1
    rw [show muRecipSum 1 = 1 by simp [muRecipSum]]
    simp only [Nat.cast_one, Real.log_one, Real.sqrt_zero, mul_zero, neg_zero, Real.exp_zero,
      mul_one, abs_one]
    exact le_max_right _ _
  · have h2' : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast h2
    have hb := hdecay (n:ℝ) h2'
    rw [Nat.floor_natCast] at hb
    exact le_trans hb (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)

theorem log_weighted_moebius_recip_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 1 ≤ x →
      |∑ m ∈ Finset.Icc 1 x,
          (ArithmeticFunction.moebius m : ℝ) * (Real.log (x : ℝ) - Real.log (m : ℝ)) / (m : ℝ)| ≤ C := by
  obtain ⟨c, C0, hc, hC0, hdecay⟩ := moebius_recip_sum_exp_decay
  obtain ⟨K, hK, htail⟩ := Commons.Analysis.Asymptotics.sum_exp_neg_sqrt_log_div_le c hc
  have hCd := muRecipSum_decay hc hC0 hdecay
  refine ⟨max C0 1 * K, mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right C0 1)) hK, ?_⟩
  intro x hx
  show |logWeightedMuSum x| ≤ max C0 1 * K
  have heq : logWeightedMuSum x
      = ∑ n ∈ Finset.Icc 1 (x-1), muRecipSum n * (Real.log ((n:ℝ)+1) - Real.log (n:ℝ)) := by
    conv_lhs => rw [← Nat.sub_add_cancel hx]
    exact logWeightedMuSum_eq (x-1)
  rw [heq]
  calc
    |∑ n ∈ Finset.Icc 1 (x-1), muRecipSum n * (Real.log ((n:ℝ)+1) - Real.log (n:ℝ))|
        ≤ ∑ n ∈ Finset.Icc 1 (x-1),
            |muRecipSum n * (Real.log ((n:ℝ)+1) - Real.log (n:ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ n ∈ Finset.Icc 1 (x-1),
            |muRecipSum n| * (Real.log ((n:ℝ)+1) - Real.log (n:ℝ)) := by
          apply Finset.sum_congr rfl; intro n hn
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
          have hdnn : 0 ≤ Real.log ((n:ℝ)+1) - Real.log (n:ℝ) :=
            sub_nonneg.mpr (Real.log_le_log hnpos (by linarith))
          rw [abs_mul, abs_of_nonneg hdnn]
    _ ≤ ∑ n ∈ Finset.Icc 1 (x-1), |muRecipSum n| / (n:ℝ) := by
          apply Finset.sum_le_sum; intro n hn
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          have hle := log_succ_sub_log_le_inv hn1
          have h1 : |muRecipSum n| * (Real.log ((n:ℝ)+1) - Real.log (n:ℝ))
              ≤ |muRecipSum n| * (1/(n:ℝ)) :=
            mul_le_mul_of_nonneg_left hle (abs_nonneg _)
          have h2 : |muRecipSum n| * (1/(n:ℝ)) = |muRecipSum n| / (n:ℝ) := by ring
          linarith [h1, h2]
    _ ≤ ∑ n ∈ Finset.Icc 1 (x-1),
            max C0 1 * Real.exp (-(c * Real.sqrt (Real.log (n:ℝ)))) / (n:ℝ) := by
          apply Finset.sum_le_sum; intro n hn
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
          exact div_le_div_of_nonneg_right (hCd n hn1) hnpos.le
    _ = max C0 1 * ∑ n ∈ Finset.Icc 1 (x-1),
            Real.exp (-(c * Real.sqrt (Real.log (n:ℝ)))) / (n:ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro n _; ring
    _ ≤ max C0 1 * K :=
          mul_le_mul_of_nonneg_left (htail (x-1))
            (le_trans zero_le_one (le_max_right C0 1))

end Commons.NumberTheory.Moebius
