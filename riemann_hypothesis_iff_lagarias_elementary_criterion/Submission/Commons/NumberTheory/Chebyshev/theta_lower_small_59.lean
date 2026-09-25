import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Lower bounds for `Chebyshev.theta` on `[2, 59]`

For every prime threshold `p ≤ 59` we bound `θ p` from below by a rational number,
by comparing the primorial `p# = ∏_{q ≤ p} q` with the nearest power of two:
writing `p# = 2^k · ((1+x)/(1-x))` with `x = (p# - 2^k)/(p# + 2^k) ∈ [0,1)`, the
classical `atanh` series `Real.sum_range_le_log_div` gives a rational lower bound
for `log (p#) = θ p`.
-/

open Finset
open scoped BigOperators

namespace Commons.NumberTheory.Chebyshev

/-- Rational lower bound on `log q` obtained from the `atanh` series, with the
argument `q` compared to the nearest power of two.

Writing `x = (q - 2^k)/(q + 2^k)` we have `q = 2^k · (1+x)/(1-x)`, so
`log q = k log 2 + log((1+x)/(1-x))` and the truncated alternating series
`2 * ∑_{i<n} x^{2i+1}/(2i+1)` gives a lower bound for the second term. -/
lemma log_nat_ge_series (q k n : ℕ) (hq : 0 < q) (hk : 2 ^ k ≤ q) :
    (k : ℝ) * (6931471803 / 10000000000) +
      2 * (∑ i ∈ Finset.range n,
        (((q : ℝ) - (2 : ℝ) ^ k) / ((q : ℝ) + (2 : ℝ) ^ k)) ^ (2 * i + 1) / (2 * i + 1))
      ≤ Real.log (q : ℝ) := by
  set x : ℝ := ((q : ℝ) - (2 : ℝ) ^ k) / ((q : ℝ) + (2 : ℝ) ^ k) with hxdef
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h2kpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hqle : (2 : ℝ) ^ k ≤ (q : ℝ) := by
    have h : ((2 ^ k : ℕ) : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast hk
    simpa using h
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  have hx1 : x < 1 := by
    rw [hxdef, div_lt_one (by positivity)]
    linarith
  have hid : (1 + x) / (1 - x) = (q : ℝ) / (2 : ℝ) ^ k := by
    rw [hxdef]
    field_simp
    ring
  have hser := Real.sum_range_le_log_div hx0 hx1 n
  rw [hid] at hser
  have hlog : Real.log ((q : ℝ) / (2 : ℝ) ^ k) = Real.log (q : ℝ) - (k : ℝ) * Real.log 2 := by
    rw [Real.log_div (ne_of_gt hqR) (ne_of_gt h2kpos), Real.log_pow]
  rw [hlog] at hser
  have h2 : (6931471803 / 10000000000 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hk' : (k : ℝ) * (6931471803 / 10000000000) ≤ (k : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg k)
  nlinarith [hser, hk']

theorem theta_ge_2 : (2 / 3 : ℝ) ≤ Chebyshev.theta (2 : ℝ) := by
  rw [Chebyshev.theta_eq_log_primorial, show ⌊(2 : ℝ)⌋₊ = 2 from by norm_num,
    show primorial 2 = 2 from by decide]
  refine le_trans ?_ (log_nat_ge_series 2 1 5 (by norm_num) (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem theta_ge_3 : (7 / 4 : ℝ) ≤ Chebyshev.theta (3 : ℝ) := by
  rw [Chebyshev.theta_eq_log_primorial, show ⌊(3 : ℝ)⌋₊ = 3 from by norm_num,
    show primorial 3 = 6 from by decide]
  refine le_trans ?_ (log_nat_ge_series 6 2 5 (by norm_num) (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem theta_ge_5 : (17 / 5 : ℝ) ≤ Chebyshev.theta (5 : ℝ) := by
  rw [Chebyshev.theta_eq_log_primorial, show ⌊(5 : ℝ)⌋₊ = 5 from by norm_num,
    show primorial 5 = 30 from by decide]
  refine le_trans ?_ (log_nat_ge_series 30 4 5 (by norm_num) (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem theta_ge_7 : (53 / 10 : ℝ) ≤ Chebyshev.theta (7 : ℝ) := by
  rw [Chebyshev.theta_eq_log_primorial, show ⌊(7 : ℝ)⌋₊ = 7 from by norm_num,
    show primorial 7 = 210 from by decide]
  refine le_trans ?_ (log_nat_ge_series 210 7 5 (by norm_num) (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem theta_ge_11 : (77 / 10 : ℝ) ≤ Chebyshev.theta (11 : ℝ) := by
  rw [Chebyshev.theta_eq_log_primorial, show ⌊(11 : ℝ)⌋₊ = 11 from by norm_num,
    show primorial 11 = 2310 from by decide]
  refine le_trans ?_ (log_nat_ge_series 2310 11 5 (by norm_num) (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem theta_ge_13 : (103 / 10 : ℝ) ≤ Chebyshev.theta (13 : ℝ) := by
  rw [Chebyshev.theta_eq_log_primorial, show ⌊(13 : ℝ)⌋₊ = 13 from by norm_num,
    show primorial 13 = 30030 from by decide]
  refine le_trans ?_ (log_nat_ge_series 30030 14 5 (by norm_num) (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem theta_ge_17 : (13 : ℝ) ≤ Chebyshev.theta (17 : ℝ) := by
  rw [Chebyshev.theta_eq_log_primorial, show ⌊(17 : ℝ)⌋₊ = 17 from by norm_num,
    show primorial 17 = 510510 from by decide]
  refine le_trans ?_ (log_nat_ge_series 510510 18 5 (by norm_num) (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem theta_ge_19 : (16 : ℝ) ≤ Chebyshev.theta (19 : ℝ) := by
  rw [Chebyshev.theta_eq_log_primorial, show ⌊(19 : ℝ)⌋₊ = 19 from by norm_num,
    show primorial 19 = 9699690 from by decide]
  refine le_trans ?_ (log_nat_ge_series 9699690 23 5 (by norm_num) (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem theta_ge_23 : (19 : ℝ) ≤ Chebyshev.theta (23 : ℝ) := by
  rw [Chebyshev.theta_eq_log_primorial, show ⌊(23 : ℝ)⌋₊ = 23 from by norm_num,
    show primorial 23 = 223092870 from by decide]
  refine le_trans ?_ (log_nat_ge_series 223092870 27 5 (by norm_num) (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem theta_ge_29 : (22 : ℝ) ≤ Chebyshev.theta (29 : ℝ) := by
  rw [Chebyshev.theta_eq_log_primorial, show ⌊(29 : ℝ)⌋₊ = 29 from by norm_num,
    show primorial 29 = 6469693230 from by decide]
  refine le_trans ?_ (log_nat_ge_series 6469693230 32 5 (by norm_num) (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem theta_ge_31 : (26 : ℝ) ≤ Chebyshev.theta (31 : ℝ) := by
  rw [Chebyshev.theta_eq_log_primorial, show ⌊(31 : ℝ)⌋₊ = 31 from by norm_num,
    show primorial 31 = 200560490130 from by decide]
  refine le_trans ?_ (log_nat_ge_series 200560490130 37 5 (by norm_num) (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem theta_ge_37 : (29 : ℝ) ≤ Chebyshev.theta (37 : ℝ) := by
  rw [Chebyshev.theta_eq_log_primorial, show ⌊(37 : ℝ)⌋₊ = 37 from by norm_num,
    show primorial 37 = 7420738134810 from by decide]
  refine le_trans ?_ (log_nat_ge_series 7420738134810 42 5 (by norm_num) (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem theta_ge_41 : (33 : ℝ) ≤ Chebyshev.theta (41 : ℝ) := by
  rw [Chebyshev.theta_eq_log_primorial, show ⌊(41 : ℝ)⌋₊ = 41 from by norm_num,
    show primorial 41 = 304250263527210 from by decide]
  refine le_trans ?_ (log_nat_ge_series 304250263527210 48 5 (by norm_num) (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem theta_ge_43 : (37 : ℝ) ≤ Chebyshev.theta (43 : ℝ) := by
  rw [Chebyshev.theta_eq_log_primorial, show ⌊(43 : ℝ)⌋₊ = 43 from by norm_num,
    show primorial 43 = 13082761331670030 from by decide]
  refine le_trans ?_ (log_nat_ge_series 13082761331670030 53 5 (by norm_num) (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem theta_ge_47 : (40 : ℝ) ≤ Chebyshev.theta (47 : ℝ) := by
  rw [Chebyshev.theta_eq_log_primorial, show ⌊(47 : ℝ)⌋₊ = 47 from by norm_num,
    show primorial 47 = 614889782588491410 from by decide]
  refine le_trans ?_ (log_nat_ge_series 614889782588491410 59 5 (by norm_num) (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem theta_ge_53 : (44 : ℝ) ≤ Chebyshev.theta (53 : ℝ) := by
  rw [Chebyshev.theta_eq_log_primorial, show ⌊(53 : ℝ)⌋₊ = 53 from by norm_num,
    show primorial 53 = 32589158477190044730 from by decide]
  refine le_trans ?_ (log_nat_ge_series 32589158477190044730 64 5 (by norm_num) (by norm_num))
  norm_num [Finset.sum_range_succ]

/-- The main statement: for every `2 ≤ n ≤ 59` the tabulated rational lower bound
is at most `θ n`. -/
theorem theta_lower_small_59 : ∀ n : ℕ, 2 ≤ n → n ≤ 59 →
    (if n < 3 then (2 / 3 : ℝ) else if n < 5 then 7 / 4 else if n < 7 then 17 / 5
      else if n < 11 then 53 / 10 else if n < 13 then 77 / 10 else if n < 17 then 103 / 10
      else if n < 19 then 13 else if n < 23 then 16 else if n < 29 then 19 else if n < 31 then 22
      else if n < 37 then 26 else if n < 41 then 29 else if n < 43 then 33 else if n < 47 then 37
      else if n < 53 then 40 else 44) ≤ Chebyshev.theta (n : ℝ) := by
  intro n hn2 hn59
  interval_cases n <;> simp <;>
    first
      | exact theta_ge_2
      | exact le_trans theta_ge_3 (Chebyshev.theta_mono (by norm_num))
      | exact le_trans theta_ge_5 (Chebyshev.theta_mono (by norm_num))
      | exact le_trans theta_ge_7 (Chebyshev.theta_mono (by norm_num))
      | exact le_trans theta_ge_11 (Chebyshev.theta_mono (by norm_num))
      | exact le_trans theta_ge_13 (Chebyshev.theta_mono (by norm_num))
      | exact le_trans theta_ge_17 (Chebyshev.theta_mono (by norm_num))
      | exact le_trans theta_ge_19 (Chebyshev.theta_mono (by norm_num))
      | exact le_trans theta_ge_23 (Chebyshev.theta_mono (by norm_num))
      | exact le_trans theta_ge_29 (Chebyshev.theta_mono (by norm_num))
      | exact le_trans theta_ge_31 (Chebyshev.theta_mono (by norm_num))
      | exact le_trans theta_ge_37 (Chebyshev.theta_mono (by norm_num))
      | exact le_trans theta_ge_41 (Chebyshev.theta_mono (by norm_num))
      | exact le_trans theta_ge_43 (Chebyshev.theta_mono (by norm_num))
      | exact le_trans theta_ge_47 (Chebyshev.theta_mono (by norm_num))
      | exact le_trans theta_ge_53 (Chebyshev.theta_mono (by norm_num))

end Commons.NumberTheory.Chebyshev
