/-
# `Submission.Work.FIArea7CF.deltaQ_mass_le` — clash-free copy of `Submission.Work.FIArea7.deltaQ_mass_le`

Imports redirected to the `FIArea7CF` copies; renamed: mem_gBox_iff→r2c_mem_gBox_iff.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7.Bridge17Defs
import Submission.Work.FIArea7.angTrunc_le
import Submission.Work.FIArea7.angFourierCoeff_le
import Submission.Work.FIArea7.sum_Icc_divisors_swap_left
import Submission.Work.FIArea7.sum_tau_Icc_le_two_mul_log
import Submission.Work.FIArea7CF.r2count_upper
import Submission.Work.FIArea7.params_theta_le_quarter

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea7

/-! ### Helpers for `deltaQ_mass_le` (A4 of `AREA7_ROUTE_LEAD.md`)

Everything below is proved from *FI* (16.26)–(16.27) (`angTrunc_le`), the divisor-moment
inequalities `Σ_{n≤y} τ(n)^k ≪ y log^{2^k−1} y` (`k = 1,2,3`), the classical bound
`r₂(n) ≤ 4τ(n)` (`r2count_upper`) and the parameter fact `θ ≤ 1/4` of `Params`. -/

namespace DeltaQ

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Part A: divisor moments -/

def tauR (n : ℕ) : ℝ := (n.divisors.card : ℝ)

lemma tauR_nonneg (n : ℕ) : 0 ≤ tauR n := by
  unfold tauR
  positivity

lemma tauR_relaxed_mul (m n : ℕ) : tauR (m * n) ≤ tauR m * tauR n := by
  have h : (m * n).divisors.card ≤ m.divisors.card * n.divisors.card := by
    rw [Nat.divisors_mul]
    exact Finset.card_mul_le
  have h2 : ((m * n).divisors.card : ℝ) ≤ ((m.divisors.card * n.divisors.card : ℕ) : ℝ) := by
    exact_mod_cast h
  simpa [tauR, Nat.cast_mul] using h2

lemma tauR_eq_sum_ones (n : ℕ) : tauR n = ∑ d ∈ n.divisors, (1 : ℝ) := by
  unfold tauR
  rw [Finset.card_eq_sum_ones]
  push_cast
  rfl

lemma tauR_sq_le (n : ℕ) : tauR n ^ 2 ≤ ∑ d ∈ n.divisors, tauR d * tauR (n / d) := by
  have hn : tauR n = ∑ d ∈ n.divisors, (1 : ℝ) := tauR_eq_sum_ones n
  calc tauR n ^ 2 = tauR n * tauR n := by rw [sq]
    _ = tauR n * (∑ d ∈ n.divisors, (1 : ℝ)) := by rw [hn]
    _ = ∑ d ∈ n.divisors, tauR n := by rw [Finset.mul_sum]; simp
    _ ≤ ∑ d ∈ n.divisors, tauR d * tauR (n / d) := by
        apply Finset.sum_le_sum
        intro d hd
        have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
        have hdn : n = d * (n / d) := (Nat.mul_div_cancel' hdvd).symm
        have h2 := tauR_relaxed_mul d (n / d)
        rw [← hdn] at h2
        exact h2

lemma tauR_cube_le (n : ℕ) : tauR n ^ 3 ≤ ∑ d ∈ n.divisors, tauR d ^ 2 * tauR (n / d) ^ 2 := by
  have hn : tauR n = ∑ d ∈ n.divisors, (1 : ℝ) := tauR_eq_sum_ones n
  calc tauR n ^ 3 = tauR n ^ 2 * tauR n := by ring
    _ = tauR n ^ 2 * (∑ d ∈ n.divisors, (1 : ℝ)) := by rw [hn]
    _ = ∑ d ∈ n.divisors, tauR n ^ 2 := by rw [Finset.mul_sum]; simp
    _ ≤ ∑ d ∈ n.divisors, tauR d ^ 2 * tauR (n / d) ^ 2 := by
        apply Finset.sum_le_sum
        intro d hd
        have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
        have hdn : n = d * (n / d) := (Nat.mul_div_cancel' hdvd).symm
        have h : tauR n ≤ tauR d * tauR (n / d) := by
          have h2 := tauR_relaxed_mul d (n / d)
          rwa [← hdn] at h2
        calc tauR n ^ 2 ≤ (tauR d * tauR (n / d)) ^ 2 :=
              pow_le_pow_left₀ (tauR_nonneg n) h 2
          _ = tauR d ^ 2 * tauR (n / d) ^ 2 := by ring

/-- Reindexing a double divisor sum. -/
lemma sum_divisors_swap {M : Type*} [AddCommMonoid M] (N : ℕ) (G : ℕ → ℕ → M) :
    (∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, G d (n / d))
      = ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d), G d m := by
  have hflt : ∀ n ∈ Icc 1 N, n.divisors.filter (fun d => d ≤ N) = n.divisors := by
    intro n hn
    refine Finset.filter_true_of_mem (fun d hd => ?_)
    rw [Finset.mem_Icc] at hn
    have hdn : d ≤ n := Nat.le_of_dvd (by omega : 0 < n) (Nat.mem_divisors.mp hd).1
    omega
  have hmvd : ∀ d m : ℕ, 0 < d → (d * m) / d = m := by
    intro d m hd
    have h1 : d * ((d * m) / d) = d * m := Nat.mul_div_cancel' (dvd_mul_right d m)
    exact Nat.mul_left_cancel hd h1
  calc (∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, G d (n / d))
      = ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors.filter (fun d => d ≤ N), G d (n / d) := by
        refine Finset.sum_congr rfl (fun n hn => ?_)
        rw [hflt n hn]
    _ = ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d), G d ((d * m) / d) :=
        sum_Icc_divisors_swap_left N N (fun d n => G d (n / d))
    _ = ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d), G d m := by
        refine Finset.sum_congr rfl (fun d hd => ?_)
        refine Finset.sum_congr rfl (fun m hm => ?_)
        rw [Finset.mem_Icc] at hd
        rw [hmvd d m (by omega)]

lemma sum_div_helper {ι : Type*} (s : Finset ι) (f : ι → ℝ) (c : ℝ) :
    (∑ i ∈ s, f i) / c = ∑ i ∈ s, f i / c := by
  rw [div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => by rw [div_eq_mul_inv])

/-- `Σ_{n ≤ N} τ(n)/n ≤ (Σ_{d ≤ N} 1/d)²`. -/
lemma sum_tau_div_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, tauR n / (n : ℝ) ≤ (∑ d ∈ Icc 1 N, (1 : ℝ) / (d : ℝ)) ^ 2 := by
  have hpt : ∀ n ∈ Icc 1 N, tauR n / (n : ℝ)
      = ∑ d ∈ n.divisors, (1 : ℝ) / (d : ℝ) * (1 / ((n / d : ℕ) : ℝ)) := by
    intro n hn
    have hcd : tauR n = ∑ d ∈ n.divisors, (1 : ℝ) := tauR_eq_sum_ones n
    rw [hcd, sum_div_helper]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
    have hmul : (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
    rw [div_mul_div_comm, one_mul, hmul]
  calc ∑ n ∈ Icc 1 N, tauR n / (n : ℝ)
      = ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors,
          (1 : ℝ) / (d : ℝ) * (1 / ((n / d : ℕ) : ℝ)) := Finset.sum_congr rfl hpt
    _ = ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d),
          (1 : ℝ) / (d : ℝ) * (1 / (m : ℝ)) :=
        sum_divisors_swap N (fun d m => (1 : ℝ) / (d : ℝ) * (1 / (m : ℝ)))
    _ = ∑ d ∈ Icc 1 N, (1 : ℝ) / (d : ℝ) * (∑ m ∈ Icc 1 (N / d), (1 / (m : ℝ))) := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [Finset.mul_sum]
    _ ≤ ∑ d ∈ Icc 1 N, (1 : ℝ) / (d : ℝ) * (∑ m ∈ Icc 1 N, (1 / (m : ℝ))) := by
        apply Finset.sum_le_sum
        intro d hd
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.Icc_subset_Icc_right (Nat.div_le_self N d)
        · intro x hx hxn
          positivity
    _ = (∑ d ∈ Icc 1 N, (1 : ℝ) / (d : ℝ)) * (∑ m ∈ Icc 1 N, (1 / (m : ℝ))) := by
        rw [Finset.sum_mul]
    _ = (∑ d ∈ Icc 1 N, (1 : ℝ) / (d : ℝ)) ^ 2 := by rw [sq]

lemma log_two_base_nonneg (N : ℕ) : 0 ≤ Real.log ((N : ℝ) + 2) := by
  apply Real.log_nonneg
  have h : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  linarith

lemma log_succ_two_le (N M : ℕ) (hM : M ≤ N) :
    Real.log ((M : ℝ) + 2) ≤ 1 + Real.log ((N : ℝ) + 2) := by
  have hle : ((M : ℝ) + 2) ≤ ((N : ℝ) + 2) := by
    have : (M : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hM
    linarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (M : ℝ) + 2) hle
  have h0 := log_two_base_nonneg N
  linarith

lemma log_two_mono (N M : ℕ) (hM : M ≤ N) :
    Real.log ((M : ℝ) + 2) ≤ Real.log ((N : ℝ) + 2) := by
  apply Real.log_le_log (by positivity)
  have : (M : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hM
  linarith

lemma one_le_one_add_log (N : ℕ) : (1 : ℝ) ≤ 1 + Real.log ((N : ℝ) + 2) := by
  have := log_two_base_nonneg N
  linarith

/-- `Σ_{n ≤ N} τ(n)² ≤ 8 N (1 + log(N+2))³`. -/
lemma sum_tau_sq_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, tauR n ^ 2 ≤ 8 * (N : ℝ) * (1 + Real.log ((N : ℝ) + 2)) ^ 3 := by
  have hL1 := one_le_one_add_log N
  have hLnn : (0 : ℝ) ≤ 1 + Real.log ((N : ℝ) + 2) := le_trans zero_le_one hL1
  have hharm : (0 : ℝ) ≤ ∑ d ∈ Icc 1 N, (1 : ℝ) / (d : ℝ) := by
    apply Finset.sum_nonneg
    intro d _
    exact div_nonneg zero_le_one (Nat.cast_nonneg d)
  have hlog2 : (0 : ℝ) ≤ 2 * Real.log ((N : ℝ) + 2) := by
    have := log_two_base_nonneg N; linarith
  calc ∑ n ∈ Icc 1 N, tauR n ^ 2
      ≤ ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, tauR d * tauR (n / d) :=
        Finset.sum_le_sum (fun n _ => tauR_sq_le n)
    _ = ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d), tauR d * tauR m :=
        sum_divisors_swap N (fun d m => tauR d * tauR m)
    _ = ∑ d ∈ Icc 1 N, tauR d * (∑ m ∈ Icc 1 (N / d), tauR m) := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [Finset.mul_sum]
    _ ≤ ∑ d ∈ Icc 1 N,
          tauR d * (2 * ((N / d : ℕ) : ℝ) * Real.log (((N / d : ℕ) : ℝ) + 2)) := by
        apply Finset.sum_le_sum
        intro d _
        exact mul_le_mul_of_nonneg_left (sum_tau_Icc_le_two_mul_log (N / d)) (tauR_nonneg d)
    _ ≤ ∑ d ∈ Icc 1 N,
          (2 * (N : ℝ) * (1 + Real.log ((N : ℝ) + 2))) * (tauR d / (d : ℝ)) := by
        apply Finset.sum_le_sum
        intro d hd
        rw [Finset.mem_Icc] at hd
        have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
        have hc : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
        have hlog : Real.log (((N / d : ℕ) : ℝ) + 2) ≤ 1 + Real.log ((N : ℝ) + 2) :=
          log_succ_two_le N (N / d) (Nat.div_le_self N d)
        have hmain : 2 * ((N / d : ℕ) : ℝ) * Real.log (((N / d : ℕ) : ℝ) + 2)
            ≤ (2 * (N : ℝ) * (1 + Real.log ((N : ℝ) + 2))) / (d : ℝ) := by
          calc 2 * ((N / d : ℕ) : ℝ) * Real.log (((N / d : ℕ) : ℝ) + 2)
              ≤ 2 * ((N / d : ℕ) : ℝ) * (1 + Real.log ((N : ℝ) + 2)) := by
                apply mul_le_mul_of_nonneg_left hlog
                positivity
            _ ≤ 2 * ((N : ℝ) / (d : ℝ)) * (1 + Real.log ((N : ℝ) + 2)) := by
                apply mul_le_mul_of_nonneg_right _ hLnn
                exact mul_le_mul_of_nonneg_left hc (by norm_num)
            _ = (2 * (N : ℝ) * (1 + Real.log ((N : ℝ) + 2))) / (d : ℝ) := by
                field_simp
        calc tauR d * (2 * ((N / d : ℕ) : ℝ) * Real.log (((N / d : ℕ) : ℝ) + 2))
            ≤ tauR d * ((2 * (N : ℝ) * (1 + Real.log ((N : ℝ) + 2))) / (d : ℝ)) :=
              mul_le_mul_of_nonneg_left hmain (tauR_nonneg d)
          _ = (2 * (N : ℝ) * (1 + Real.log ((N : ℝ) + 2))) * (tauR d / (d : ℝ)) := by ring
    _ = 2 * (N : ℝ) * (1 + Real.log ((N : ℝ) + 2))
          * (∑ d ∈ Icc 1 N, tauR d / (d : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ 2 * (N : ℝ) * (1 + Real.log ((N : ℝ) + 2))
          * (4 * (1 + Real.log ((N : ℝ) + 2)) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ∑ d ∈ Icc 1 N, tauR d / (d : ℝ)
            ≤ (∑ d ∈ Icc 1 N, (1 : ℝ) / (d : ℝ)) ^ 2 := sum_tau_div_le N
          _ ≤ (2 * Real.log ((N : ℝ) + 2)) ^ 2 :=
              pow_le_pow_left₀ hharm (sum_inv_Icc_le_two_log N) 2
          _ ≤ (2 * (1 + Real.log ((N : ℝ) + 2))) ^ 2 := by
              apply pow_le_pow_left₀ hlog2
              linarith
          _ = 4 * (1 + Real.log ((N : ℝ) + 2)) ^ 2 := by ring
    _ = 8 * (N : ℝ) * (1 + Real.log ((N : ℝ) + 2)) ^ 3 := by ring

/-- `Σ_{n ≤ N} τ(n)²/n ≤ 16 (1 + log(N+2))⁴`. -/
lemma sum_tau_sq_div_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, tauR n ^ 2 / (n : ℝ) ≤ 16 * (1 + Real.log ((N : ℝ) + 2)) ^ 4 := by
  have hL1 := one_le_one_add_log N
  have hLnn : (0 : ℝ) ≤ 1 + Real.log ((N : ℝ) + 2) := le_trans zero_le_one hL1
  have hharm : (0 : ℝ) ≤ ∑ d ∈ Icc 1 N, (1 : ℝ) / (d : ℝ) := by
    apply Finset.sum_nonneg
    intro d _
    exact div_nonneg zero_le_one (Nat.cast_nonneg d)
  have hlog2 : (0 : ℝ) ≤ 2 * Real.log ((N : ℝ) + 2) := by
    have := log_two_base_nonneg N; linarith
  have hpt : ∀ n ∈ Icc 1 N, tauR n ^ 2 / (n : ℝ)
      ≤ ∑ d ∈ n.divisors, (tauR d / (d : ℝ)) * (tauR (n / d) / ((n / d : ℕ) : ℝ)) := by
    intro n _
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    calc tauR n ^ 2 / (n : ℝ)
        ≤ (∑ d ∈ n.divisors, tauR d * tauR (n / d)) / (n : ℝ) :=
          div_le_div_of_nonneg_right (tauR_sq_le n) hn0
      _ = ∑ d ∈ n.divisors, (tauR d * tauR (n / d)) / (n : ℝ) :=
          sum_div_helper _ _ _
      _ = ∑ d ∈ n.divisors, (tauR d / (d : ℝ)) * (tauR (n / d) / ((n / d : ℕ) : ℝ)) := by
          refine Finset.sum_congr rfl (fun d hd => ?_)
          have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
          have hmul : (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
            rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
          rw [← hmul, div_mul_div_comm]
  calc ∑ n ∈ Icc 1 N, tauR n ^ 2 / (n : ℝ)
      ≤ ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors,
          (tauR d / (d : ℝ)) * (tauR (n / d) / ((n / d : ℕ) : ℝ)) :=
        Finset.sum_le_sum hpt
    _ = ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d),
          (tauR d / (d : ℝ)) * (tauR m / (m : ℝ)) :=
        sum_divisors_swap N (fun d m => (tauR d / (d : ℝ)) * (tauR m / (m : ℝ)))
    _ ≤ (∑ d ∈ Icc 1 N, tauR d / (d : ℝ)) * (∑ m ∈ Icc 1 N, tauR m / (m : ℝ)) := by
        have hinner : ∀ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d),
              (tauR d / (d : ℝ)) * (tauR m / (m : ℝ))
            ≤ (tauR d / (d : ℝ)) * (∑ m ∈ Icc 1 N, tauR m / (m : ℝ)) := by
          intro d _
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.Icc_subset_Icc_right (Nat.div_le_self N d)
          · intro x _ _
            exact mul_nonneg (div_nonneg (tauR_nonneg d) (Nat.cast_nonneg d))
              (div_nonneg (tauR_nonneg x) (Nat.cast_nonneg x))
        calc ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d),
                (tauR d / (d : ℝ)) * (tauR m / (m : ℝ))
            ≤ ∑ d ∈ Icc 1 N,
                (tauR d / (d : ℝ)) * (∑ m ∈ Icc 1 N, tauR m / (m : ℝ)) :=
              Finset.sum_le_sum hinner
          _ = (∑ d ∈ Icc 1 N, tauR d / (d : ℝ))
                * (∑ m ∈ Icc 1 N, tauR m / (m : ℝ)) := by
              rw [Finset.sum_mul]
    _ = (∑ d ∈ Icc 1 N, tauR d / (d : ℝ)) ^ 2 := by rw [sq]
    _ ≤ (4 * (1 + Real.log ((N : ℝ) + 2)) ^ 2) ^ 2 := by
        apply pow_le_pow_left₀ (Finset.sum_nonneg
          (fun d _ => div_nonneg (tauR_nonneg d) (Nat.cast_nonneg d)))
        calc ∑ d ∈ Icc 1 N, tauR d / (d : ℝ)
            ≤ (∑ d ∈ Icc 1 N, (1 : ℝ) / (d : ℝ)) ^ 2 := sum_tau_div_le N
          _ ≤ (2 * Real.log ((N : ℝ) + 2)) ^ 2 :=
              pow_le_pow_left₀ hharm (sum_inv_Icc_le_two_log N) 2
          _ ≤ (2 * (1 + Real.log ((N : ℝ) + 2))) ^ 2 := by
              apply pow_le_pow_left₀ hlog2
              linarith
          _ = 4 * (1 + Real.log ((N : ℝ) + 2)) ^ 2 := by ring
    _ = 16 * (1 + Real.log ((N : ℝ) + 2)) ^ 4 := by ring

/-- `Σ_{n ≤ N} τ(n)³ ≤ 128 N (1 + log(N+2))⁷`. -/
lemma sum_tau_cube_le_aux (N : ℕ) :
    ∑ n ∈ Icc 1 N, tauR n ^ 3 ≤ 128 * (N : ℝ) * (1 + Real.log ((N : ℝ) + 2)) ^ 7 := by
  have hL1 := one_le_one_add_log N
  have hLnn : (0 : ℝ) ≤ 1 + Real.log ((N : ℝ) + 2) := le_trans zero_le_one hL1
  have hL3nn : (0 : ℝ) ≤ (1 + Real.log ((N : ℝ) + 2)) ^ 3 := pow_nonneg hLnn 3
  calc ∑ n ∈ Icc 1 N, tauR n ^ 3
      ≤ ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, tauR d ^ 2 * tauR (n / d) ^ 2 :=
        Finset.sum_le_sum (fun n _ => tauR_cube_le n)
    _ = ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d), tauR d ^ 2 * tauR m ^ 2 :=
        sum_divisors_swap N (fun d m => tauR d ^ 2 * tauR m ^ 2)
    _ = ∑ d ∈ Icc 1 N, tauR d ^ 2 * (∑ m ∈ Icc 1 (N / d), tauR m ^ 2) := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [Finset.mul_sum]
    _ ≤ ∑ d ∈ Icc 1 N,
          tauR d ^ 2 * (8 * ((N / d : ℕ) : ℝ) * (1 + Real.log ((N : ℝ) + 2)) ^ 3) := by
        apply Finset.sum_le_sum
        intro d _
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (tauR_nonneg d) 2)
        have h := sum_tau_sq_le (N / d)
        have hlog : 1 + Real.log (((N / d : ℕ) : ℝ) + 2)
            ≤ 1 + Real.log ((N : ℝ) + 2) := by
          have := log_two_mono N (N / d) (Nat.div_le_self N d)
          linarith
        calc ∑ m ∈ Icc 1 (N / d), tauR m ^ 2
            ≤ 8 * ((N / d : ℕ) : ℝ) * (1 + Real.log (((N / d : ℕ) : ℝ) + 2)) ^ 3 := h
          _ ≤ 8 * ((N / d : ℕ) : ℝ) * (1 + Real.log ((N : ℝ) + 2)) ^ 3 := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact pow_le_pow_left₀ (by have h := log_two_base_nonneg (N / d); linarith) hlog 3
    _ ≤ ∑ d ∈ Icc 1 N,
          (8 * (N : ℝ) * (1 + Real.log ((N : ℝ) + 2)) ^ 3) * (tauR d ^ 2 / (d : ℝ)) := by
        apply Finset.sum_le_sum
        intro d hd
        rw [Finset.mem_Icc] at hd
        have hc : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
        have hstep : 8 * ((N / d : ℕ) : ℝ) * (1 + Real.log ((N : ℝ) + 2)) ^ 3
            ≤ (8 * (N : ℝ) * (1 + Real.log ((N : ℝ) + 2)) ^ 3) / (d : ℝ) := by
          have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
          calc 8 * ((N / d : ℕ) : ℝ) * (1 + Real.log ((N : ℝ) + 2)) ^ 3
              ≤ 8 * ((N : ℝ) / (d : ℝ)) * (1 + Real.log ((N : ℝ) + 2)) ^ 3 := by
                apply mul_le_mul_of_nonneg_right _ hL3nn
                exact mul_le_mul_of_nonneg_left hc (by norm_num)
            _ = (8 * (N : ℝ) * (1 + Real.log ((N : ℝ) + 2)) ^ 3) / (d : ℝ) := by
                field_simp
        calc tauR d ^ 2 * (8 * ((N / d : ℕ) : ℝ) * (1 + Real.log ((N : ℝ) + 2)) ^ 3)
            ≤ tauR d ^ 2 * ((8 * (N : ℝ) * (1 + Real.log ((N : ℝ) + 2)) ^ 3) / (d : ℝ)) :=
              mul_le_mul_of_nonneg_left hstep (pow_nonneg (tauR_nonneg d) 2)
          _ = (8 * (N : ℝ) * (1 + Real.log ((N : ℝ) + 2)) ^ 3) * (tauR d ^ 2 / (d : ℝ)) := by
              ring
    _ = 8 * (N : ℝ) * (1 + Real.log ((N : ℝ) + 2)) ^ 3
          * (∑ d ∈ Icc 1 N, tauR d ^ 2 / (d : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ 8 * (N : ℝ) * (1 + Real.log ((N : ℝ) + 2)) ^ 3
          * (16 * (1 + Real.log ((N : ℝ) + 2)) ^ 4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact sum_tau_sq_div_le N
    _ = 128 * (N : ℝ) * (1 + Real.log ((N : ℝ) + 2)) ^ 7 := by ring

/-- **A3 with `j = 3`**: `Σ_{n ≤ y} τ(n)³ ≤ C y (1 + log(y+2))⁷`. -/
theorem sum_tau_cube_le : ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ,
    ∑ n ∈ Icc 1 y, tauR n ^ 3
      ≤ C * (y : ℝ) * (1 + Real.log ((y : ℝ) + 2)) ^ 7 := by
  exact ⟨128, by norm_num, fun y => sum_tau_cube_le_aux y⟩

/-! ### Part B: the `τ²`-moment of `|z|²` over a box -/

/-- Every point of the box `gBox R` has `|z|² ≤ 2 R²`. -/
lemma gBox_gnorm_le (R : ℤ) {z : GaussianInt} (hz : z ∈ Work.FIPlan.gBox R) :
    Work.FIPlan.gnorm z ≤ 2 * R.natAbs ^ 2 := by
  rw [Work.FIPlan.gnorm, GaussianInt.natAbs_norm_eq]
  rw [Work.FIArea7.r2c_mem_gBox_iff] at hz
  obtain ⟨hre, him⟩ := hz
  rw [Finset.mem_Icc] at hre him
  have h1 : z.re.natAbs ≤ R.natAbs := by
    rw [Int.natAbs_le_iff_sq_le]
    nlinarith [hre.1, hre.2]
  have h2 : z.im.natAbs ≤ R.natAbs := by
    rw [Int.natAbs_le_iff_sq_le]
    nlinarith [him.1, him.2]
  have hm1 := Nat.mul_le_mul h1 h1
  have hm2 := Nat.mul_le_mul h2 h2
  calc z.re.natAbs * z.re.natAbs + z.im.natAbs * z.im.natAbs
      ≤ R.natAbs * R.natAbs + R.natAbs * R.natAbs := by omega
    _ = 2 * R.natAbs ^ 2 := by ring

/-- **Disc bound for the `τ²`-moment of `|z|²` over a box.**
`Σ_{z ∈ gBox R} τ(|z|²)² ≤ 4 Σ_{n ≤ 2R²} τ(n)³`. -/
lemma gBox_gnorm_tau_sq_le (R : ℤ) :
    ∑ z ∈ Work.FIPlan.gBox R, tauR (Work.FIPlan.gnorm z) ^ 2
      ≤ 4 * ∑ n ∈ Finset.Icc 1 (2 * R.natAbs ^ 2), tauR n ^ 3 := by
  set s : Finset GaussianInt := Work.FIPlan.gBox R with hs
  set t : Finset ℕ := s.image Work.FIPlan.gnorm with ht
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := s) (t := t) (g := Work.FIPlan.gnorm)
    (fun z hz => Finset.mem_image_of_mem Work.FIPlan.gnorm hz)
    (fun z => tauR (Work.FIPlan.gnorm z) ^ 2)
  rw [← hfiber]
  have hinner : ∀ m ∈ t,
      ∑ z ∈ s.filter (fun z => Work.FIPlan.gnorm z = m), tauR (Work.FIPlan.gnorm z) ^ 2
        ≤ 4 * tauR m ^ 3 := by
    intro m hm
    have hconst : ∀ z ∈ s.filter (fun z => Work.FIPlan.gnorm z = m),
        tauR (Work.FIPlan.gnorm z) ^ 2 = tauR m ^ 2 := by
      intro z hz
      rw [Finset.mem_filter] at hz
      rw [hz.2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      simp [tauR]
    · have hcard : (((s.filter (fun z => Work.FIPlan.gnorm z = m)).card : ℕ) : ℝ)
          ≤ 4 * tauR m := by
        have hsub : s.filter (fun z => Work.FIPlan.gnorm z = m) ⊆ Sz m := by
          intro z hz
          rw [Finset.mem_filter] at hz
          exact mem_Sz_of_gnorm_eq hz.2
        have h1 : (s.filter (fun z => Work.FIPlan.gnorm z = m)).card ≤ (Sz m).card :=
          Finset.card_le_card hsub
        have h2 : (Sz m).card = r2count m := (r2count_eq_Sz_card m).symm
        have h3 := r2count_upper m hmpos
        have h4 : (∏ p ∈ m.primeFactors.filter (fun p => p % 4 = 1),
              (m.factorization p + 1))
            ≤ ∏ p ∈ m.primeFactors, (m.factorization p + 1) :=
          Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
            (fun p _ _ => Nat.succ_le_succ (Nat.zero_le _))
        have hnat : (s.filter (fun z => Work.FIPlan.gnorm z = m)).card ≤ 4 * m.divisors.card := by
          calc (s.filter (fun z => Work.FIPlan.gnorm z = m)).card ≤ (Sz m).card := h1
            _ = r2count m := h2
            _ ≤ 4 * ∏ p ∈ m.primeFactors.filter (fun p => p % 4 = 1),
                  (m.factorization p + 1) := h3
            _ ≤ 4 * ∏ p ∈ m.primeFactors, (m.factorization p + 1) :=
                Nat.mul_le_mul_left 4 h4
            _ = 4 * m.divisors.card := by rw [Nat.card_divisors (by omega)]
        have hcast : (((s.filter (fun z => Work.FIPlan.gnorm z = m)).card : ℕ) : ℝ)
            ≤ 4 * (m.divisors.card : ℝ) := by
          exact_mod_cast hnat
        simpa [tauR] using hcast
      calc (((s.filter (fun z => Work.FIPlan.gnorm z = m)).card : ℕ) : ℝ) * tauR m ^ 2
          ≤ (4 * tauR m) * tauR m ^ 2 :=
            mul_le_mul_of_nonneg_right hcard (pow_nonneg (tauR_nonneg m) 2)
        _ = 4 * tauR m ^ 3 := by ring
  calc ∑ m ∈ t, ∑ z ∈ s.filter (fun z => Work.FIPlan.gnorm z = m),
          tauR (Work.FIPlan.gnorm z) ^ 2
      ≤ ∑ m ∈ t, 4 * tauR m ^ 3 := Finset.sum_le_sum hinner
    _ ≤ ∑ m ∈ insert 0 (Finset.Icc 1 (2 * R.natAbs ^ 2)), 4 * tauR m ^ 3 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          rw [Finset.mem_image] at hm
          obtain ⟨z, hz, rfl⟩ := hm
          rcases Nat.eq_zero_or_pos (Work.FIPlan.gnorm z) with h0 | hpos
          · exact Finset.mem_insert.mpr (Or.inl h0)
          · exact Finset.mem_insert.mpr (Or.inr (by
              rw [Finset.mem_Icc]
              exact ⟨hpos, gBox_gnorm_le R hz⟩))
        · intro m _ _
          exact mul_nonneg (by norm_num) (pow_nonneg (tauR_nonneg m) 3)
    _ = ∑ m ∈ Finset.Icc 1 (2 * R.natAbs ^ 2), 4 * tauR m ^ 3 := by
        rw [Finset.sum_insert (by simp)]
        simp [tauR]
    _ = 4 * ∑ n ∈ Finset.Icc 1 (2 * R.natAbs ^ 2), tauR n ^ 3 := by
        rw [Finset.mul_sum]

/-! ### Part C: the pointwise truncation bound -/

lemma deriv_ofReal_comp (q : ℝ → ℝ) (hq : Differentiable ℝ q) :
    deriv (fun t => ((q t : ℝ) : ℂ)) = fun t => ((deriv q t : ℝ) : ℂ) := by
  funext t
  exact ((hq t).hasDerivAt.ofReal_comp).deriv

lemma iteratedDeriv_one_ofReal (q : ℝ → ℝ) (hq : Differentiable ℝ q) :
    iteratedDeriv 1 (fun t => ((q t : ℝ) : ℂ)) = fun t => ((deriv q t : ℝ) : ℂ) := by
  rw [iteratedDeriv_one]
  exact deriv_ofReal_comp q hq

lemma iteratedDeriv_two_ofReal (q : ℝ → ℝ) (hq : Differentiable ℝ q)
    (hd : Differentiable ℝ (deriv q)) :
    iteratedDeriv 2 (fun t => ((q t : ℝ) : ℂ)) = fun t => ((iteratedDeriv 2 q t : ℝ) : ℂ) := by
  have h : iteratedDeriv 2 (fun t => ((q t : ℝ) : ℂ))
      = deriv (fun t => ((deriv q t : ℝ) : ℂ)) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one_ofReal q hq]
  rw [h, deriv_ofReal_comp (deriv q) hd]
  have h2 : iteratedDeriv 2 q = deriv (deriv q) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2]

lemma angTruncSum_periodic (q : ℝ → ℝ) (L : ℕ) (α : ℝ) :
    angTruncSum q L (α + 2 * Real.pi) = angTruncSum q L α := by
  unfold angTruncSum
  refine Finset.sum_congr rfl (fun ℓ _ => ?_)
  congr 1
  have hsplit : Complex.I * (ℓ : ℂ) * (((α : ℝ) : ℂ) + 2 * ((Real.pi : ℝ) : ℂ))
      = Complex.I * (ℓ : ℂ) * ((α : ℝ) : ℂ)
        + (ℓ : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) := by ring
  have hcast : (((α + 2 * Real.pi : ℝ)) : ℂ)
      = ((α : ℝ) : ℂ) + 2 * ((Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **Pointwise truncation bound of (16.27) at every angle of the annulus.** -/
theorem angTrunc_pointwise_le (C : ℝ) (hC : 0 < C) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ (q : ℝ → ℝ) (θ : ℝ) (L : ℕ) (α : ℝ),
        0 < θ → θ ≤ 1 → ContDiff ℝ 2 q →
        (∀ t, 0 ≤ q t ∧ q t ≤ 1) →
        (∀ t, q t ≠ 0 → 0 ≤ t ∧ t ≤ 2 * Real.pi * θ) →
        (∀ j : ℕ, j ≤ 2 → ∀ t : ℝ, |iteratedDeriv j q t| ≤ C * θ ^ (-(j : ℝ))) →
        1 ≤ L → -2 * Real.pi + 2 * Real.pi * θ < α → α ≤ 2 * Real.pi →
        ‖(q α : ℂ) - angTruncSum q L α‖
          ≤ C' * (θ⁻¹ * Real.log ((L : ℝ) + 2) / (L : ℝ)) := by
  obtain ⟨C', hC', hle⟩ := angTrunc_le C hC
  refine ⟨C', hC', ?_⟩
  intro q θ L α hθ0 hθ1 hq hq01 hqsupp hqder hL hαlo hαhi
  have hdiff : Differentiable ℝ q := hq.differentiable (by norm_num)
  have hdiff1 : Differentiable ℝ (deriv q) := by
    simpa [iteratedDeriv_one] using ContDiff.differentiable_iteratedDeriv' 1 hq
  have hw_cont : ContDiff ℝ 2 (fun t => ((q t : ℝ) : ℂ)) := by
    have h := (ContinuousLinearMap.contDiff Complex.ofRealCLM (n := 2)).comp hq
    simpa [Function.comp_def, Complex.ofRealCLM_apply] using h
  have hw_bd : ∀ t, ‖((q t : ℝ) : ℂ)‖ ≤ 1 := by
    intro t
    rw [Complex.norm_real, Real.norm_of_nonneg (hq01 t).1]
    exact (hq01 t).2
  have hw_supp : ∀ t, ((q t : ℝ) : ℂ) ≠ 0 → 0 ≤ t ∧ t ≤ 2 * Real.pi * θ := by
    intro t ht
    exact hqsupp t (fun h0 => ht (by simp [h0]))
  have hw_der : ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
      ‖iteratedDeriv j (fun t => ((q t : ℝ) : ℂ)) t‖ ≤ C * θ ^ (-(j : ℝ)) := by
    intro j hj t
    have hid : ‖iteratedDeriv j (fun t => ((q t : ℝ) : ℂ)) t‖ = |iteratedDeriv j q t| := by
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · rw [iteratedDeriv_zero, iteratedDeriv_zero, Complex.norm_real, Real.norm_eq_abs]
      · rw [iteratedDeriv_one_ofReal q hdiff, iteratedDeriv_one, Complex.norm_real, Real.norm_eq_abs]
      · rw [iteratedDeriv_two_ofReal q hdiff hdiff1, Complex.norm_real, Real.norm_eq_abs]
    rw [hid]
    exact hqder j hj t
  by_cases hα0 : 0 ≤ α
  · have h := hle (fun t => ((q t : ℝ) : ℂ)) θ L α hθ0 hθ1 hw_cont hw_bd hw_supp hw_der hL
      ⟨hα0, hαhi⟩
    simpa [angTruncSum] using h
  · have hαneg : α < 0 := not_le.mp hα0
    have hq0 : q α = 0 := by
      by_contra hc
      exact absurd (hqsupp α hc).1 (not_le.mpr hαneg)
    have hq2π0 : q (α + 2 * Real.pi) = 0 := by
      by_contra hc
      have h := (hqsupp (α + 2 * Real.pi) hc).2
      have hgt : 2 * Real.pi * θ < α + 2 * Real.pi := by linarith
      linarith
    have hα2 : α + 2 * Real.pi ∈ Set.Icc 0 (2 * Real.pi) := by
      constructor
      · nlinarith [hθ0, Real.pi_pos]
      · linarith
    have hper := angTruncSum_periodic q L α
    have h := hle (fun t => ((q t : ℝ) : ℂ)) θ L (α + 2 * Real.pi) hθ0 hθ1 hw_cont hw_bd
      hw_supp hw_der hL hα2
    have hq0' : ((q α : ℝ) : ℂ) = 0 := by rw [hq0]; simp
    have h2π0 : ((q (α + 2 * Real.pi) : ℝ) : ℂ) = 0 := by rw [hq2π0]; simp
    simp only [angTruncSum] at h hper ⊢
    rw [h2π0, hper] at h
    rw [hq0']
    exact h

/-! ### Part D: the `γ`- and `radBeta`-bounds, and the numeric preparation -/

lemma gammaTrunc_abs_le (Cc : ℝ) (n : ℕ) : |Work.FIPlan.gammaTrunc Cc n| ≤ tauR n := by
  have h1 : |∑ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ Cc),
        (ArithmeticFunction.moebius d : ℝ)|
      ≤ ∑ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ Cc),
        |(ArithmeticFunction.moebius d : ℝ)| :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : ∀ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ Cc),
      |(ArithmeticFunction.moebius d : ℝ)| ≤ (1 : ℝ) := by
    intro d _
    have h := ArithmeticFunction.abs_moebius_le_one (n := d)
    exact_mod_cast h
  have h3 : ∑ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ Cc),
      |(ArithmeticFunction.moebius d : ℝ)| ≤ ((n.divisors.filter
        (fun d => ((d : ℕ) : ℝ) ≤ Cc)).card : ℝ) := by
    calc ∑ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ Cc),
          |(ArithmeticFunction.moebius d : ℝ)|
        ≤ ∑ _d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ Cc), (1 : ℝ) :=
          Finset.sum_le_sum h2
      _ = ((n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ Cc)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have h4 : ((n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ Cc)).card : ℝ)
      ≤ (n.divisors.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have h5 : Work.FIPlan.gammaTrunc Cc n
      = ∑ d ∈ n.divisors.filter (fun d => ((d : ℕ) : ℝ) ≤ Cc),
          (ArithmeticFunction.moebius d : ℝ) := rfl
  rw [h5]
  exact le_trans h1 (le_trans h3 h4)

lemma radBeta_norm_le (Pa : Work.FITop.Params) (p : ℝ → ℝ) (z : GaussianInt)
    (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1) :
    ‖Work.FIArea7.radBeta Pa p Pa.C z‖ ≤ tauR (Work.FIPlan.gnorm z) := by
  set n : ℕ := Work.FIPlan.gnorm z with hn
  by_cases h : Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z
  · have hval : Work.FIArea7.radBeta Pa p Pa.C z
        = ((p n : ℝ) : ℂ) * ((ArithmeticFunction.moebius n : ℤ) : ℂ)
          * ((Work.FIPlan.gammaTrunc Pa.C n : ℝ) : ℂ) := by
      unfold Work.FIArea7.radBeta
      rw [if_pos h]
    rw [hval, norm_mul, norm_mul]
    have h1 : ‖((p n : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (hp0 n)]
      exact hp1 n
    have h2 : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    have h3 : ‖((Work.FIPlan.gammaTrunc Pa.C n : ℝ) : ℂ)‖ ≤ tauR n := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact gammaTrunc_abs_le Pa.C n
    have h4 : ‖((p n : ℝ) : ℂ)‖ * ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 * 1 :=
      mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
    calc ‖((p n : ℝ) : ℂ)‖ * ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖
            * ‖((Work.FIPlan.gammaTrunc Pa.C n : ℝ) : ℂ)‖
        ≤ (1 * 1) * tauR n := mul_le_mul h4 h3 (norm_nonneg _) (by norm_num)
      _ = tauR n := by ring
  · have hval : Work.FIArea7.radBeta Pa p Pa.C z = 0 := by
      unfold Work.FIArea7.radBeta
      rw [if_neg h]
    rw [hval, norm_zero]
    exact tauR_nonneg n

lemma radBetaCls_norm_le (Pa : Work.FITop.Params) (p : ℝ → ℝ) (z0 z : GaussianInt)
    (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1) :
    ‖Work.FIArea7.radBetaCls Pa p z0 z‖ ≤ tauR (Work.FIPlan.gnorm z) := by
  unfold Work.FIArea7.radBetaCls
  rw [norm_mul]
  have h1 : ‖(if Work.FITop4.SameClass8 z z0 then (1 : ℂ) else 0)‖ ≤ 1 := by
    by_cases h : Work.FITop4.SameClass8 z z0
    · simp [h]
    · simp [h]
  calc ‖(if Work.FITop4.SameClass8 z z0 then (1 : ℂ) else 0)‖
          * ‖Work.FIArea7.radBeta Pa p Pa.C z‖
      ≤ 1 * tauR (Work.FIPlan.gnorm z) :=
        mul_le_mul h1 (radBeta_norm_le Pa p z hp0 hp1) (norm_nonneg _) (by norm_num)
    _ = tauR (Work.FIPlan.gnorm z) := one_mul _

/-- The `τ²`-mass of the box at scale `radN Pa`: `≪ N log⁷(N+2)` uniformly in `Pa`
(the box has `≍ N` points and `|z|² ≤ 18N` inside it). -/
lemma box_tau_sq_bound (Pa : Work.FITop.Params) :
    ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), tauR (Work.FIPlan.gnorm z) ^ 2
      ≤ 512 * 18 * (2 + Real.log 20) ^ 7 * Pa.N * (Real.log (Pa.N + 2)) ^ 7 := by
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hNnn : (0 : ℝ) ≤ Pa.N := by linarith
  have hlogN : (1 : ℝ) ≤ Real.log (Pa.N + 2) := by
    have h3 : Real.log 3 ≤ Real.log (Pa.N + 2) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hone : (1 : ℝ) < Real.log 3 := by
      have h := Real.log_lt_log (Real.exp_pos 1) (show Real.exp 1 < 3 by
        have := Real.exp_one_lt_d9
        linarith)
      rwa [Real.log_exp] at h
    linarith
  have hR : (((Work.FITop.radN Pa).natAbs : ℕ) : ℝ) ≤ 3 * Real.sqrt Pa.N := by
    have hval : (Work.FITop.radN Pa).natAbs = ⌈Real.sqrt (4 * Pa.N)⌉₊ := by
      rw [Work.FITop.radN, Int.natAbs_natCast]
    rw [hval]
    have h1 : ((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℝ) < Real.sqrt (4 * Pa.N) + 1 :=
      Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
    have h2 : Real.sqrt (4 * Pa.N) = 2 * Real.sqrt Pa.N := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
        show Real.sqrt (4 : ℝ) = 2 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs,
            abs_of_nonneg (by norm_num)]]
    have h3 : (1 : ℝ) ≤ Real.sqrt Pa.N := Real.one_le_sqrt.mpr hN1
    linarith
  have hycast : (((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ)) : ℝ)
      = 2 * (((Work.FITop.radN Pa).natAbs : ℕ) : ℝ) ^ 2 := by push_cast; ring
  have hy : (((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ)) : ℝ) ≤ 18 * Pa.N := by
    rw [hycast]
    have hsq := Real.sq_sqrt hNnn
    have h0 : (0 : ℝ) ≤ ((Work.FITop.radN Pa).natAbs : ℕ) := Nat.cast_nonneg _
    nlinarith [hR, Real.sqrt_nonneg Pa.N, hsq]
  have hy0 : (0 : ℝ) ≤ ((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ) := by
    rw [hycast]; positivity
  have hlogy : 1 + Real.log (((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ) + 2)
      ≤ (2 + Real.log 20) * Real.log (Pa.N + 2) := by
    have hy2 : (((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ) + 2) ≤ 20 * (Pa.N + 2) := by
      nlinarith [hy, hN1]
    have hpos : (0 : ℝ) < ((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ) + 2 := by
      linarith
    have h1 : Real.log (((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ) + 2)
        ≤ Real.log (20 * (Pa.N + 2)) := Real.log_le_log hpos hy2
    have h2 : Real.log (20 * (Pa.N + 2)) = Real.log 20 + Real.log (Pa.N + 2) :=
      Real.log_mul (by norm_num) (by linarith)
    have h20 : (0 : ℝ) ≤ Real.log 20 := Real.log_nonneg (by norm_num)
    have h3 : (1 : ℝ) + Real.log 20 + Real.log (Pa.N + 2)
        ≤ (2 + Real.log 20) * Real.log (Pa.N + 2) := by nlinarith [hlogN, h20]
    linarith
  have hpowy : (0 : ℝ) ≤ (1 + Real.log
      (((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ) + 2)) ^ 7 := by
    have : (0 : ℝ) ≤ Real.log (((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ) + 2) :=
      log_two_base_nonneg _
    positivity
  have hstep : 128 * ((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ)
        * (1 + Real.log (((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ) + 2)) ^ 7
      ≤ 128 * (18 * Pa.N) * ((2 + Real.log 20) * Real.log (Pa.N + 2)) ^ 7 := by
    have hmain : ((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ)
          * (1 + Real.log (((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ) + 2)) ^ 7
        ≤ (18 * Pa.N) * ((2 + Real.log 20) * Real.log (Pa.N + 2)) ^ 7 :=
      mul_le_mul hy (pow_le_pow_left₀ (by
        have := log_two_base_nonneg (2 * (Work.FITop.radN Pa).natAbs ^ 2)
        linarith) hlogy 7) hpowy (by linarith)
    calc 128 * ((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ)
          * (1 + Real.log (((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ) + 2)) ^ 7
        = 128 * (((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ)
          * (1 + Real.log (((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ) + 2)) ^ 7) := by
          ring
      _ ≤ 128 * ((18 * Pa.N) * ((2 + Real.log 20) * Real.log (Pa.N + 2)) ^ 7) :=
          mul_le_mul_of_nonneg_left hmain (by norm_num)
      _ = 128 * (18 * Pa.N) * ((2 + Real.log 20) * Real.log (Pa.N + 2)) ^ 7 := by ring
  calc ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), tauR (Work.FIPlan.gnorm z) ^ 2
      ≤ 4 * ∑ n ∈ Finset.Icc 1 (2 * (Work.FITop.radN Pa).natAbs ^ 2), tauR n ^ 3 :=
        gBox_gnorm_tau_sq_le _
    _ ≤ 4 * (128 * ((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ)
          * (1 + Real.log (((2 * (Work.FITop.radN Pa).natAbs ^ 2 : ℕ) : ℝ) + 2)) ^ 7) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
        exact sum_tau_cube_le_aux _
    _ ≤ 4 * (128 * (18 * Pa.N) * ((2 + Real.log 20) * Real.log (Pa.N + 2)) ^ 7) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
        exact hstep
    _ = 512 * 18 * (2 + Real.log 20) ^ 7 * Pa.N * (Real.log (Pa.N + 2)) ^ 7 := by ring


end

end DeltaQ

/-- **A4: the `L²`-mass of the truncation error of (16.27)** — *FI* (16.26)–(16.27) via the proved
`angTrunc_le` (pointwise truncation bound, `α ∈ [0,2π]`) and `angFourierCoeff_le` (16.26), on the
path of `AREA7_ROUTE_LEAD.md` §2.2.

Proof: (1) *pointwise bound*: with `α = arg z − φ ∈ (−2π+2πθ, 2π]`, for `α < 0` shift to
`α + 2π ∈ (2πθ, 2π)`, where `q = 0` and the partial sum is `2π`-periodic, so `angTrunc_le` applies
at every `z`; (2) *summation*: `|radBetaCls| ≤ τ(n)` and `Σ_{|z|²≤2N} τ(n)² ≤ 4Σ τ(n)³` by
`sum_tau_pow_le` with `j = 3` (the disc bound is used on purpose: the short-interval `τ`-sums on the
annulus are not available).  `θ ≤ 1` is a consequence of `Params`. -/
theorem deltaQ_mass_le : ∃ C : ℝ, 0 < C ∧
  ∀ {Pa : Work.FITop.Params} (q p : ℝ → ℝ) (φ : ℝ) (z0 : GaussianInt) (L : ℕ),
    Work.FIArea7.IsMollPair Pa q p → -Real.pi ≤ φ → φ ≤ Real.pi - 2 * Real.pi * Pa.θ → 1 ≤ L →
    ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        ‖Work.FIArea7.betaTilde Pa q p φ z0 z - Work.FIArea7.betaL Pa q p φ z0 L z‖ ^ 2
      ≤ C * (Pa.θ⁻¹ * Real.log ((L : ℝ) + 2) / (L : ℝ)) ^ 2 * Pa.N
          * (Real.log (Pa.N + 2)) ^ 7 := by
  have hcm : 0 < Work.FITop4.cMoll 2 := by
    unfold Work.FITop4.cMoll
    positivity
  obtain ⟨C1, hC1pos, hC1⟩ := DeltaQ.angTrunc_pointwise_le (Work.FITop4.cMoll 2) hcm
  refine ⟨C1 ^ 2 * (512 * 18 * (2 + Real.log 20) ^ 7), by positivity, ?_⟩
  intro Pa q p φ z0 L hmoll hφ1 hφ2 hL
  obtain ⟨hq_cont, hp_cont, hq01, hq_supp, hq_der, hp01, hp_supp, hp_der⟩ := hmoll
  have hθ0 : 0 < Pa.θ := Pa.hθ0
  have hθ1 : Pa.θ ≤ 1 := le_trans (Work.FIArea7.params_theta_le_quarter Pa) (by norm_num)
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hlogL : 0 ≤ Real.log ((L : ℝ) + 2) := by
    apply Real.log_nonneg
    have : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    linarith
  have hXnn : 0 ≤ Pa.θ⁻¹ * Real.log ((L : ℝ) + 2) / (L : ℝ) := by
    apply div_nonneg
    · exact mul_nonneg (inv_nonneg.mpr (le_of_lt hθ0)) hlogL
    · exact Nat.cast_nonneg L
  have hcm2 : ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ,
      |iteratedDeriv j q t| ≤ Work.FITop4.cMoll 2 * Pa.θ ^ (-(j : ℝ)) := by
    intro j hj t
    have h := hq_der j hj t
    have hc : Work.FITop4.cMoll j ≤ Work.FITop4.cMoll 2 := by
      unfold Work.FITop4.cMoll
      apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      omega
    have hp : (0 : ℝ) ≤ Pa.θ ^ (-(j : ℝ)) := Real.rpow_nonneg (le_of_lt hθ0) _
    exact le_trans h (mul_le_mul_of_nonneg_right hc hp)
  have hpt : ∀ z : GaussianInt,
      ‖Work.FIArea7.betaTilde Pa q p φ z0 z - Work.FIArea7.betaL Pa q p φ z0 L z‖
        ≤ (C1 * (Pa.θ⁻¹ * Real.log ((L : ℝ) + 2) / (L : ℝ)))
            * DeltaQ.tauR (Work.FIPlan.gnorm z) := by
    intro z
    set α : ℝ := Complex.arg z.toComplex - φ with hαdef
    have hαlo : -2 * Real.pi + 2 * Real.pi * Pa.θ < α := by
      have h := Complex.neg_pi_lt_arg z.toComplex
      rw [hαdef]
      linarith
    have hαhi : α ≤ 2 * Real.pi := by
      have h := Complex.arg_le_pi z.toComplex
      rw [hαdef]
      linarith
    have htrunc := hC1 q Pa.θ L α hθ0 hθ1 hq_cont hq01 hq_supp hcm2 hL hαlo hαhi
    have hrbc := DeltaQ.radBetaCls_norm_le Pa p z0 z (fun u => (hp01 u).1) (fun u => (hp01 u).2)
    have hsplit : Work.FIArea7.betaTilde Pa q p φ z0 z - Work.FIArea7.betaL Pa q p φ z0 L z
        = (((q α : ℝ) : ℂ) - Work.FIArea7.angTruncSum q L α)
            * Work.FIArea7.radBetaCls Pa p z0 z := by
      unfold Work.FIArea7.betaTilde Work.FIArea7.betaL
      simp only [← hαdef]
      ring
    rw [hsplit, norm_mul]
    exact mul_le_mul htrunc hrbc (norm_nonneg _) (mul_nonneg hC1pos.le hXnn)
  calc ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        ‖Work.FIArea7.betaTilde Pa q p φ z0 z - Work.FIArea7.betaL Pa q p φ z0 L z‖ ^ 2
      ≤ ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ((C1 * (Pa.θ⁻¹ * Real.log ((L : ℝ) + 2) / (L : ℝ)))
            * DeltaQ.tauR (Work.FIPlan.gnorm z)) ^ 2 := by
        apply Finset.sum_le_sum
        intro z _
        exact pow_le_pow_left₀ (norm_nonneg _) (hpt z) 2
    _ = (C1 * (Pa.θ⁻¹ * Real.log ((L : ℝ) + 2) / (L : ℝ))) ^ 2
          * ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              DeltaQ.tauR (Work.FIPlan.gnorm z) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ring
    _ ≤ (C1 * (Pa.θ⁻¹ * Real.log ((L : ℝ) + 2) / (L : ℝ))) ^ 2
          * (512 * 18 * (2 + Real.log 20) ^ 7 * Pa.N * (Real.log (Pa.N + 2)) ^ 7) :=
        mul_le_mul_of_nonneg_left (DeltaQ.box_tau_sq_bound Pa) (sq_nonneg _)
    _ = (C1 ^ 2 * (512 * 18 * (2 + Real.log 20) ^ 7))
          * (Pa.θ⁻¹ * Real.log ((L : ℝ) + 2) / (L : ℝ)) ^ 2 * Pa.N
          * (Real.log (Pa.N + 2)) ^ 7 := by ring

end Work.FIArea7
