import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.sum_log_pow_div_Icc_le
import Submission.Work.ZeroFreeTables.P9.large_prime_factors_sum_le

/-!
# `Work.ZeroFreeTables.P9.primeFactors_logPow_div_le`

For `j ≤ 3` and every `q ≥ 3`,

  `∑_{p | q, p prime} (log p)^j / p  ≤  C · (log log q)^{j+1}`,

with an explicit constant `C = 768 + 1/(log log 3)^5`.

The proof splits the prime factors of `q` at the threshold `y = (log q)^4`:

* the primes `p ≤ y` are dominated by the full integer sum `∑_{n ≤ ⌊y⌋} (log n)^j/n`,
  which is bounded by `3 (log y)^{j+1}` via the telescoping inequality
  `log(n+1) - log n ≥ 1/(n+1)` (`sum_log_pow_div_Icc_le`);
* the primes `p > y` are controlled by `∏_{p | q} p ≤ q`, which forces
  `#{p > y} · log y ≤ log q`; each term is at most `(log q)^j/p`
  (`large_prime_factors_sum_le`), giving `(log q)^{j+1}/(y log y)`.

With `y = (log q)^4` the two pieces become `768 (log log q)^{j+1}` and
`1/(4 log log q)`, and the latter is absorbed into the former because
`log log 3 ≤ log log q` and `log log 3 ≤ 1`.
-/

open scoped BigOperators

namespace Work.ZeroFreeTables.P9

private lemma one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (show (0:ℝ) < 3 by norm_num)]
  exact Real.exp_one_lt_three

private lemma log_three_le_two : Real.log 3 ≤ 2 := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)
  linarith

private lemma clog_pos : 0 < Real.log (Real.log 3) := Real.log_pos one_lt_log_three

private lemma clog_le_one : Real.log (Real.log 3) ≤ 1 := by
  have h2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have h3 : Real.log (Real.log 3) ≤ Real.log 2 :=
    Real.log_le_log (by linarith [one_lt_log_three]) log_three_le_two
  linarith

private lemma main_estimate (j : ℕ) (hj : j ≤ 3) (q : ℕ) (hq : 3 ≤ q) :
    ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ j / (p : ℝ)
      ≤ 768 * (Real.log (Real.log (q : ℝ))) ^ (j + 1)
        + 1 / (4 * Real.log (Real.log (q : ℝ))) := by
  set x : ℝ := Real.log (q : ℝ) with hxdef
  have hq3 : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hx_gt1 : 1 < x := by
    rw [hxdef]
    exact lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num) hq3)
  have hx1 : (1:ℝ) ≤ x := le_of_lt hx_gt1
  have hxpos : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx_gt1
  set y : ℝ := x ^ 4 with hydef
  have hy1 : 1 < y := by rw [hydef]; exact one_lt_pow₀ hx_gt1 (by norm_num)
  have hylog : 0 < Real.log y := Real.log_pos hy1
  have hsplit := Finset.sum_filter_add_sum_filter_not q.primeFactors
    (fun p : ℕ => (p:ℝ) ≤ y) (fun p : ℕ => (Real.log (p:ℝ)) ^ j / (p:ℝ))
  -- small primes
  have hsmall : (q.primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ y)).sum
      (fun p : ℕ => (Real.log (p:ℝ)) ^ j / (p:ℝ)) ≤ 3 * (Real.log y) ^ (j + 1) := by
    have hstep : (q.primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ y)).sum
        (fun p : ℕ => (Real.log (p:ℝ)) ^ j / (p:ℝ))
        ≤ ∑ n ∈ Finset.Icc 2 ⌊y⌋₊, (Real.log (n:ℝ)) ^ j / (n:ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hpm, hple⟩ := hp
        rw [Finset.mem_Icc]
        exact ⟨(Nat.prime_of_mem_primeFactors hpm).two_le, Nat.le_floor hple⟩
      · intro n hn _
        rw [Finset.mem_Icc] at hn
        exact div_nonneg (pow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))) j)
          (by positivity)
    by_cases hM : 2 ≤ ⌊y⌋₊
    · have hA := sum_log_pow_div_Icc_le j ⌊y⌋₊ hM
      have hlogM : Real.log ((⌊y⌋₊ : ℕ) : ℝ) ≤ Real.log y :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊y⌋₊))
          (Nat.floor_le (le_of_lt (by linarith : (0:ℝ) < y)))
      have hlogMnn : 0 ≤ Real.log ((⌊y⌋₊ : ℕ) : ℝ) :=
        le_of_lt (Real.log_pos (by exact_mod_cast (by omega : 1 < ⌊y⌋₊)))
      have hpow : (Real.log ((⌊y⌋₊ : ℕ) : ℝ)) ^ (j+1) ≤ (Real.log y) ^ (j+1) :=
        pow_le_pow_left₀ hlogMnn hlogM (j+1)
      linarith [hstep, hA, mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ) ≤ 3)]
    · have hM1 : ⌊y⌋₊ ≤ 1 := by omega
      have hzero : (q.primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ y)).sum
          (fun p : ℕ => (Real.log (p:ℝ)) ^ j / (p:ℝ)) = 0 := by
        apply Finset.sum_eq_zero
        intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hpm, hple⟩ := hp
        have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hpm).two_le
        have hle : p ≤ ⌊y⌋₊ := Nat.le_floor hple
        exfalso
        omega
      rw [hzero]
      exact mul_nonneg (by norm_num) (pow_nonneg (le_of_lt hylog) _)
  -- large primes
  have hlarge : (q.primeFactors.filter (fun p : ℕ => ¬ (p:ℝ) ≤ y)).sum
      (fun p : ℕ => (Real.log (p:ℝ)) ^ j / (p:ℝ)) ≤ x ^ (j+1) / (y * Real.log y) := by
    have hb := large_prime_factors_sum_le j q (by omega) y hy1
    have hcongr : (q.primeFactors.filter (fun p : ℕ => ¬ (p:ℝ) ≤ y)).sum
        (fun p : ℕ => (Real.log (p:ℝ)) ^ j / (p:ℝ))
        = (q.primeFactors.filter (fun p : ℕ => y < (p:ℝ))).sum
        (fun p : ℕ => (Real.log (p:ℝ)) ^ j / (p:ℝ)) :=
      Finset.sum_congr (Finset.filter_congr (fun p _ => not_le)) (fun p _ => rfl)
    rw [hxdef]
    exact le_of_eq_of_le hcongr hb
  have hbound : (∑ p ∈ q.primeFactors, (Real.log (p:ℝ)) ^ j / (p:ℝ))
      ≤ 3 * (Real.log y) ^ (j+1) + x ^ (j+1) / (y * Real.log y) := by
    rw [← hsplit]
    exact add_le_add hsmall hlarge
  -- substitute y = x^4
  have hlogy : Real.log y = 4 * Real.log x := by
    rw [hydef, Real.log_pow]; push_cast; ring
  have hterm1 : 3 * (Real.log y) ^ (j+1) ≤ 768 * (Real.log x) ^ (j+1) := by
    rw [hlogy]
    have h4 : (4:ℝ) ^ (j+1) ≤ 4 ^ 4 := pow_le_pow_right₀ (by norm_num) (by omega : j+1 ≤ 4)
    have hLnn : 0 ≤ (Real.log x) ^ (j+1) := pow_nonneg (le_of_lt hlx) _
    calc 3 * (4 * Real.log x) ^ (j+1) = 3 * ((4:ℝ)^(j+1) * (Real.log x)^(j+1)) := by rw [mul_pow]
      _ ≤ 3 * (4^4 * (Real.log x)^(j+1)) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact mul_le_mul_of_nonneg_right h4 hLnn
      _ = 768 * (Real.log x)^(j+1) := by norm_num; ring
  have hterm2 : x ^ (j+1) / (y * Real.log y) ≤ 1 / (4 * Real.log x) := by
    rw [hydef, hlogy]
    have hx4pos : 0 < x^4 := pow_pos hxpos 4
    have hpow : x^(j+1) ≤ x^4 := pow_le_pow_right₀ hx1 (by omega : j+1 ≤ 4)
    have h4lpos : 0 < 4 * Real.log x := by linarith
    have hden : 0 ≤ x^4 * (4 * Real.log x) := le_of_lt (mul_pos hx4pos h4lpos)
    have heq : 1 / (4 * Real.log x) = x^4 / (x^4 * (4 * Real.log x)) := by
      rw [div_eq_div_iff (ne_of_gt h4lpos) (ne_of_gt (mul_pos hx4pos h4lpos))]
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right hpow hden
  calc ∑ p ∈ q.primeFactors, (Real.log (p:ℝ)) ^ j / (p:ℝ)
      ≤ 3 * (Real.log y) ^ (j+1) + x ^ (j+1) / (y * Real.log y) := hbound
    _ ≤ 768 * (Real.log x)^(j+1) + 1 / (4 * Real.log x) := add_le_add hterm1 hterm2

theorem primeFactors_logPow_div_le (j : ℕ) (hj : j ≤ 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 3 ≤ q →
      ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ j / (p : ℝ)
        ≤ C * (Real.log (Real.log (q : ℝ))) ^ (j + 1) := by
  refine ⟨768 + 1 / (Real.log (Real.log 3)) ^ 5, ?_, ?_⟩
  · have h := clog_pos; positivity
  · intro q hq
    set x : ℝ := Real.log (q:ℝ) with hxdef
    have hq3 : (3:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    have hx_gt1 : 1 < x := by
      rw [hxdef]
      exact lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num) hq3)
    have hL : 0 < Real.log x := Real.log_pos hx_gt1
    have hmain := main_estimate j hj q hq
    have hlog3pos : (0:ℝ) < Real.log 3 := lt_trans zero_lt_one one_lt_log_three
    have hcL : Real.log (Real.log 3) ≤ Real.log x :=
      Real.log_le_log hlog3pos
        (by rw [hxdef]; exact Real.log_le_log (by norm_num) hq3)
    have hc5 : (Real.log (Real.log 3))^5 ≤ 4 * (Real.log x)^(j+2) := by
      have h1 : (Real.log (Real.log 3))^5 ≤ (Real.log (Real.log 3))^(j+2) :=
        pow_le_pow_of_le_one (le_of_lt clog_pos) clog_le_one (by omega : j+2 ≤ 5)
      have h2 : (Real.log (Real.log 3))^(j+2) ≤ (Real.log x)^(j+2) :=
        pow_le_pow_left₀ (le_of_lt clog_pos) hcL _
      have h3 : 0 ≤ (Real.log x)^(j+2) := pow_nonneg (le_of_lt hL) _
      linarith
    have hkey : 1 / (4 * Real.log x)
        ≤ (1 / (Real.log (Real.log 3))^5) * (Real.log x)^(j+1) := by
      have hc5pos : 0 < (Real.log (Real.log 3))^5 := pow_pos clog_pos 5
      have h1 : 1 ≤ (1 / (Real.log (Real.log 3))^5) * (4 * (Real.log x)^(j+2)) := by
        have h2 := mul_le_mul_of_nonneg_left hc5 (le_of_lt (one_div_pos.mpr hc5pos))
        rwa [one_div_mul_cancel (ne_of_gt hc5pos)] at h2
      have hLpow : (1 / (Real.log (Real.log 3))^5) * (4 * (Real.log x)^(j+2))
          = (1 / (Real.log (Real.log 3))^5) * (Real.log x)^(j+1) * (4 * Real.log x) := by
        rw [show j + 2 = (j+1)+1 by omega, pow_succ]
        ring
      rw [div_le_iff₀ (by linarith : (0:ℝ) < 4 * Real.log x)]
      rw [← hLpow]
      exact h1
    calc ∑ p ∈ q.primeFactors, (Real.log (p:ℝ)) ^ j / (p:ℝ)
        ≤ 768 * (Real.log x)^(j+1) + 1 / (4 * Real.log x) := hmain
      _ ≤ 768 * (Real.log x)^(j+1)
            + (1 / (Real.log (Real.log 3))^5) * (Real.log x)^(j+1) := add_le_add le_rfl hkey
      _ = (768 + 1 / (Real.log (Real.log 3))^5) * (Real.log x)^(j+1) := by ring

end Work.ZeroFreeTables.P9
