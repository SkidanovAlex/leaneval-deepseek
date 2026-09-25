import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Int
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime

open scoped ArithmeticFunction.sigma

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Commons.NumberTheory.Lagarias

private lemma eulerMascheroniSeq_50_gt_567_1000 : Real.eulerMascheroniSeq 50 > 567 / 1000 := by
  have hgoal : (harmonic 50 : ℝ) - 567 / 1000 > Real.log 51 := by
    rw [gt_iff_lt, Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 51)]
    have hx : 0 ≤ (harmonic 50 : ℝ) - 567 / 1000 := by
      norm_num [harmonic]
    have hsum := Real.sum_le_exp_of_nonneg (x := (harmonic 50 : ℝ) - 567 / 1000) hx 13
    have h51 : (51 : ℝ) < ∑ i ∈ Finset.range 13, ((harmonic 50 : ℝ) - 567 / 1000) ^ i / (Nat.factorial i : ℝ) := by
      norm_num [harmonic]
    exact lt_of_lt_of_le h51 hsum
  rw [Real.eulerMascheroniSeq]
  norm_num [Nat.cast_add, Nat.cast_one]
  have hgoal' : Real.log 51 < (harmonic 50 : ℝ) - 567 / 1000 := hgoal
  norm_num [harmonic] at hgoal hgoal'
  linarith

private lemma log_4002_gt_8294_div_1000 : (8294 / 1000 : ℝ) < Real.log 4002 := by
  have h4000 : (4000 : ℝ) < 4002 := by norm_num
  have hlog := Real.log_lt_log (by norm_num : (0 : ℝ) < 4000) h4000
  have hpow : Real.log (4000 : ℝ) = 5 * Real.log 2 + 3 * Real.log 5 := by
    have hfac : (4000 : ℝ) = (2 : ℝ) ^ 5 * (5 : ℝ) ^ 3 := by norm_num
    rw [hfac]
    rw [Real.log_mul, Real.log_pow, Real.log_pow]
    · norm_num
    · norm_num
    · norm_num
  rw [hpow] at hlog
  have h2 := Real.log_two_gt_d9
  have h5 := Real.log_five_gt_d9
  nlinarith

private lemma exp_two_lt : Real.exp 2 < (2.7182818286 : ℝ) ^ 2 := by
  have h := Real.exp_one_lt_d9
  have hpow : Real.exp 1 ^ 2 = Real.exp 2 := Real.exp_one_pow 2
  rw [← hpow]
  refine pow_lt_pow_left₀ h ?_ (by norm_num : (2 : ℕ) ≠ 0)
  exact le_of_lt (Real.exp_pos 1)

private lemma exp_217_100_lt_8861_div_1000 : Real.exp (217 / 100) < 8861 / 1000 := by
  have hsplit : Real.exp (217 / 100) = Real.exp 2 * Real.exp (17 / 100) := by
    rw [← Real.exp_add]
    norm_num
  rw [hsplit]
  have h2 : Real.exp 2 < (2.7182818286 : ℝ) ^ 2 := exp_two_lt
  have h17 : Real.exp (17 / 100) < (2 + 17 / 100) / (2 - 17 / 100) := by
    apply Real.exp_lt_two_add_div_two_sub
    · norm_num
    · norm_num
  have hmul : Real.exp 2 * Real.exp (17 / 100) < (2.7182818286 : ℝ) ^ 2 * ((2 + 17 / 100) / (2 - 17 / 100)) := by
    apply mul_lt_mul h2 h17.le (by positivity) (by norm_num)
  refine lt_trans hmul ?_
  norm_num

private lemma log_8861_div_1000_gt_217_div_100 : (217 / 100 : ℝ) < Real.log (8861 / 1000) := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 8861 / 1000)]
  exact exp_217_100_lt_8861_div_1000

private lemma exp_567_1000_gt_176_100 : (176 / 100 : ℝ) < Real.exp (567 / 1000) := by
  have hx : 0 ≤ (567 / 1000 : ℝ) := by norm_num
  have hsum := Real.sum_le_exp_of_nonneg (x := (567 / 1000 : ℝ)) hx 5
  have h176 : (176 / 100 : ℝ) < ∑ i ∈ Finset.range 5, (567 / 1000 : ℝ) ^ i / (Nat.factorial i : ℝ) := by
    norm_num
  exact lt_of_lt_of_le h176 hsum

private lemma rhs_ge_15120 (n : ℕ) (hn0 : 0 < n) (hL : 4001 ≤ n) :
    (15120 : ℝ) ≤ (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  have hn50 : 50 ≤ n := by omega
  have hseq50 := eulerMascheroniSeq_50_gt_567_1000
  have hseqn_lt : Real.eulerMascheroniSeq 50 < Real.eulerMascheroniSeq n :=
    Real.strictMono_eulerMascheroniSeq (by omega)
  have hseqn : 567 / 1000 < Real.eulerMascheroniSeq n := lt_trans hseq50 hseqn_lt
  have hH_low1 : (567 / 1000 : ℝ) + Real.log (n + 1) < harmonic n := by
    unfold Real.eulerMascheroniSeq at hseqn
    norm_num at hseqn
    linarith
  have hlog4002 : (8294 / 1000 : ℝ) < Real.log 4002 := log_4002_gt_8294_div_1000
  have hlogn : Real.log 4002 ≤ Real.log (n + 1) := by
    apply Real.log_le_log (by norm_num : (0 : ℝ) < 4002)
    exact_mod_cast (Nat.succ_le_succ hL)
  have hlog_low : (8294 / 1000 : ℝ) < Real.log (n + 1) := lt_of_lt_of_le hlog4002 hlogn
  have hH_low : (8861 / 1000 : ℝ) < harmonic n := by
    have : (8861 / 1000 : ℝ) < (567 / 1000 : ℝ) + Real.log (n + 1) := by
      linarith
    exact lt_trans this hH_low1
  have hlogH1 : (217 / 100 : ℝ) < Real.log (8861 / 1000) := log_8861_div_1000_gt_217_div_100
  have hlogH2 : Real.log (8861 / 1000) < Real.log (harmonic n) := by
    apply Real.log_lt_log (by norm_num : (0 : ℝ) < 8861 / 1000)
    exact_mod_cast hH_low
  have hlogH : (217 / 100 : ℝ) < Real.log (harmonic n) := lt_trans hlogH1 hlogH2
  have hexp0 : (176 / 100 : ℝ) < Real.exp (567 / 1000) := exp_567_1000_gt_176_100
  have hH_low1' : Real.log (n + 1) + 567 / 1000 < harmonic n := by
    linarith
  have hexp_H_low : Real.exp (Real.log (n + 1) + 567 / 1000) < Real.exp (harmonic n) := by
    exact Real.exp_lt_exp.mpr hH_low1'
  have hexp_H_eq : Real.exp (Real.log (n + 1) + 567 / 1000) = (n + 1 : ℝ) * Real.exp (567 / 1000) := by
    rw [Real.exp_add, Real.exp_log (show 0 < (n : ℝ) + 1 by positivity)]
  have hexp_H_low' : (n + 1 : ℝ) * Real.exp (567 / 1000) < Real.exp (harmonic n) := by
    rwa [hexp_H_eq] at hexp_H_low
  have hn1 : (4002 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast (Nat.succ_le_succ hL)
  have hprod1 : (4002 : ℝ) * (176 / 100) < (n + 1 : ℝ) * Real.exp (567 / 1000) := by
    apply mul_lt_mul' hn1 hexp0 (by norm_num) (by positivity)
  have hprod2 : (4002 : ℝ) * (176 / 100) * (217 / 100) < ((n + 1 : ℝ) * Real.exp (567 / 1000)) * Real.log (harmonic n) := by
    apply mul_lt_mul hprod1 hlogH.le (by norm_num) (by positivity)
  have hprod3 : ((n + 1 : ℝ) * Real.exp (567 / 1000)) * Real.log (harmonic n) <
      Real.exp (harmonic n) * Real.log (harmonic n) := by
    apply mul_lt_mul_of_pos_right hexp_H_low' (by exact lt_trans (by norm_num : (0 : ℝ) < 217 / 100) hlogH)
  have hconst : (15120 : ℝ) < (4002 : ℝ) * (176 / 100) * (217 / 100) := by norm_num
  have hprod4 : (4002 : ℝ) * (176 / 100) * (217 / 100) < Real.exp (harmonic n) * Real.log (harmonic n) := by
    exact lt_trans hprod2 hprod3
  have hprod_le : (15120 : ℝ) < Real.exp (harmonic n) * Real.log (harmonic n) := lt_trans hconst hprod4
  have hH_pos : 0 < (harmonic n : ℝ) := by
    exact_mod_cast harmonic_pos (Nat.ne_of_gt hn0)
  have hH_nonneg : 0 ≤ (harmonic n : ℝ) := le_of_lt hH_pos
  linarith

private lemma sigma_4001 : (ArithmeticFunction.sigma 1 4001 : ℕ) = 4002 := by
  change (ArithmeticFunction.sigma 1 (4001^1) : ℕ) = 4002
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4001)]
  norm_num

private lemma sigma_4002 : (ArithmeticFunction.sigma 1 4002 : ℕ) = 8640 := by
  have hfac : 4002 = 2^1 * (3^1 * (23^1 * (29^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (23^1 * (29^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 23^1 * (29^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 23^1) (n := 29^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_23_1 : (ArithmeticFunction.sigma 1 (23^1) : ℕ) = 24 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
    norm_num
  have h_29_1 : (ArithmeticFunction.sigma 1 (29^1) : ℕ) = 30 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 29)]
    norm_num
  rw [h_2_1, h_3_1, h_23_1, h_29_1]
  norm_num

private lemma sigma_4003 : (ArithmeticFunction.sigma 1 4003 : ℕ) = 4004 := by
  change (ArithmeticFunction.sigma 1 (4003^1) : ℕ) = 4004
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4003)]
  norm_num

private lemma sigma_4004 : (ArithmeticFunction.sigma 1 4004 : ℕ) = 9408 := by
  have hfac : 4004 = 2^2 * (7^1 * (11^1 * (13^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 7^1 * (11^1 * (13^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 11^1 * (13^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 13^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  rw [h_2_2, h_7_1, h_11_1, h_13_1]
  norm_num

private lemma sigma_4005 : (ArithmeticFunction.sigma 1 4005 : ℕ) = 7020 := by
  have hfac : 4005 = 3^2 * (5^1 * (89^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 5^1 * (89^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 89^1) (by norm_num [Nat.gcd])]
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_89_1 : (ArithmeticFunction.sigma 1 (89^1) : ℕ) = 90 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 89)]
    norm_num
  rw [h_3_2, h_5_1, h_89_1]
  norm_num

private lemma sigma_4006 : (ArithmeticFunction.sigma 1 4006 : ℕ) = 6012 := by
  have hfac : 4006 = 2^1 * (2003^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2003^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2003_1 : (ArithmeticFunction.sigma 1 (2003^1) : ℕ) = 2004 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2003)]
    norm_num
  rw [h_2_1, h_2003_1]
  norm_num

private lemma sigma_4007 : (ArithmeticFunction.sigma 1 4007 : ℕ) = 4008 := by
  change (ArithmeticFunction.sigma 1 (4007^1) : ℕ) = 4008
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4007)]
  norm_num

private lemma sigma_4008 : (ArithmeticFunction.sigma 1 4008 : ℕ) = 10080 := by
  have hfac : 4008 = 2^3 * (3^1 * (167^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 3^1 * (167^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 167^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_167_1 : (ArithmeticFunction.sigma 1 (167^1) : ℕ) = 168 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 167)]
    norm_num
  rw [h_2_3, h_3_1, h_167_1]
  norm_num

private lemma sigma_4009 : (ArithmeticFunction.sigma 1 4009 : ℕ) = 4240 := by
  have hfac : 4009 = 19^1 * (211^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 19^1) (n := 211^1) (by norm_num [Nat.gcd])]
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  have h_211_1 : (ArithmeticFunction.sigma 1 (211^1) : ℕ) = 212 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 211)]
    norm_num
  rw [h_19_1, h_211_1]
  norm_num

private lemma sigma_4010 : (ArithmeticFunction.sigma 1 4010 : ℕ) = 7236 := by
  have hfac : 4010 = 2^1 * (5^1 * (401^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 5^1 * (401^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 401^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_401_1 : (ArithmeticFunction.sigma 1 (401^1) : ℕ) = 402 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 401)]
    norm_num
  rw [h_2_1, h_5_1, h_401_1]
  norm_num

private lemma sigma_4011 : (ArithmeticFunction.sigma 1 4011 : ℕ) = 6144 := by
  have hfac : 4011 = 3^1 * (7^1 * (191^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 7^1 * (191^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 191^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_191_1 : (ArithmeticFunction.sigma 1 (191^1) : ℕ) = 192 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 191)]
    norm_num
  rw [h_3_1, h_7_1, h_191_1]
  norm_num

private lemma sigma_4012 : (ArithmeticFunction.sigma 1 4012 : ℕ) = 7560 := by
  have hfac : 4012 = 2^2 * (17^1 * (59^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 17^1 * (59^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 17^1) (n := 59^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  have h_59_1 : (ArithmeticFunction.sigma 1 (59^1) : ℕ) = 60 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 59)]
    norm_num
  rw [h_2_2, h_17_1, h_59_1]
  norm_num

private lemma sigma_4013 : (ArithmeticFunction.sigma 1 4013 : ℕ) = 4014 := by
  change (ArithmeticFunction.sigma 1 (4013^1) : ℕ) = 4014
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4013)]
  norm_num

private lemma sigma_4014 : (ArithmeticFunction.sigma 1 4014 : ℕ) = 8736 := by
  have hfac : 4014 = 2^1 * (3^2 * (223^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^2 * (223^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 223^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_223_1 : (ArithmeticFunction.sigma 1 (223^1) : ℕ) = 224 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 223)]
    norm_num
  rw [h_2_1, h_3_2, h_223_1]
  norm_num

private lemma sigma_4015 : (ArithmeticFunction.sigma 1 4015 : ℕ) = 5328 := by
  have hfac : 4015 = 5^1 * (11^1 * (73^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 11^1 * (73^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 73^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_73_1 : (ArithmeticFunction.sigma 1 (73^1) : ℕ) = 74 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 73)]
    norm_num
  rw [h_5_1, h_11_1, h_73_1]
  norm_num

private lemma sigma_4016 : (ArithmeticFunction.sigma 1 4016 : ℕ) = 7812 := by
  have hfac : 4016 = 2^4 * (251^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^4) (n := 251^1) (by norm_num [Nat.gcd])]
  have h_2_4 : (ArithmeticFunction.sigma 1 (2^4) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_251_1 : (ArithmeticFunction.sigma 1 (251^1) : ℕ) = 252 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 251)]
    norm_num
  rw [h_2_4, h_251_1]
  norm_num

private lemma sigma_4017 : (ArithmeticFunction.sigma 1 4017 : ℕ) = 5824 := by
  have hfac : 4017 = 3^1 * (13^1 * (103^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 13^1 * (103^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 103^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_103_1 : (ArithmeticFunction.sigma 1 (103^1) : ℕ) = 104 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 103)]
    norm_num
  rw [h_3_1, h_13_1, h_103_1]
  norm_num

private lemma sigma_4018 : (ArithmeticFunction.sigma 1 4018 : ℕ) = 7182 := by
  have hfac : 4018 = 2^1 * (7^2 * (41^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 7^2 * (41^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^2) (n := 41^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_7_2 : (ArithmeticFunction.sigma 1 (7^2) : ℕ) = 57 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_41_1 : (ArithmeticFunction.sigma 1 (41^1) : ℕ) = 42 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 41)]
    norm_num
  rw [h_2_1, h_7_2, h_41_1]
  norm_num

private lemma sigma_4019 : (ArithmeticFunction.sigma 1 4019 : ℕ) = 4020 := by
  change (ArithmeticFunction.sigma 1 (4019^1) : ℕ) = 4020
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4019)]
  norm_num

private lemma sigma_4020 : (ArithmeticFunction.sigma 1 4020 : ℕ) = 11424 := by
  have hfac : 4020 = 2^2 * (3^1 * (5^1 * (67^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 3^1 * (5^1 * (67^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 5^1 * (67^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 67^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_67_1 : (ArithmeticFunction.sigma 1 (67^1) : ℕ) = 68 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 67)]
    norm_num
  rw [h_2_2, h_3_1, h_5_1, h_67_1]
  norm_num

private lemma sigma_4021 : (ArithmeticFunction.sigma 1 4021 : ℕ) = 4022 := by
  change (ArithmeticFunction.sigma 1 (4021^1) : ℕ) = 4022
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4021)]
  norm_num

private lemma sigma_4022 : (ArithmeticFunction.sigma 1 4022 : ℕ) = 6036 := by
  have hfac : 4022 = 2^1 * (2011^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2011^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2011_1 : (ArithmeticFunction.sigma 1 (2011^1) : ℕ) = 2012 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2011)]
    norm_num
  rw [h_2_1, h_2011_1]
  norm_num

private lemma sigma_4023 : (ArithmeticFunction.sigma 1 4023 : ℕ) = 6000 := by
  have hfac : 4023 = 3^3 * (149^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^3) (n := 149^1) (by norm_num [Nat.gcd])]
  have h_3_3 : (ArithmeticFunction.sigma 1 (3^3) : ℕ) = 40 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_149_1 : (ArithmeticFunction.sigma 1 (149^1) : ℕ) = 150 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 149)]
    norm_num
  rw [h_3_3, h_149_1]
  norm_num

private lemma sigma_4024 : (ArithmeticFunction.sigma 1 4024 : ℕ) = 7560 := by
  have hfac : 4024 = 2^3 * (503^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 503^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_503_1 : (ArithmeticFunction.sigma 1 (503^1) : ℕ) = 504 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 503)]
    norm_num
  rw [h_2_3, h_503_1]
  norm_num

private lemma sigma_4025 : (ArithmeticFunction.sigma 1 4025 : ℕ) = 5952 := by
  have hfac : 4025 = 5^2 * (7^1 * (23^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^2) (n := 7^1 * (23^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 23^1) (by norm_num [Nat.gcd])]
  have h_5_2 : (ArithmeticFunction.sigma 1 (5^2) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_23_1 : (ArithmeticFunction.sigma 1 (23^1) : ℕ) = 24 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
    norm_num
  rw [h_5_2, h_7_1, h_23_1]
  norm_num

private lemma sigma_4026 : (ArithmeticFunction.sigma 1 4026 : ℕ) = 8928 := by
  have hfac : 4026 = 2^1 * (3^1 * (11^1 * (61^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (11^1 * (61^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 11^1 * (61^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 61^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_61_1 : (ArithmeticFunction.sigma 1 (61^1) : ℕ) = 62 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 61)]
    norm_num
  rw [h_2_1, h_3_1, h_11_1, h_61_1]
  norm_num

private lemma sigma_4027 : (ArithmeticFunction.sigma 1 4027 : ℕ) = 4028 := by
  change (ArithmeticFunction.sigma 1 (4027^1) : ℕ) = 4028
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4027)]
  norm_num

private lemma sigma_4028 : (ArithmeticFunction.sigma 1 4028 : ℕ) = 7560 := by
  have hfac : 4028 = 2^2 * (19^1 * (53^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 19^1 * (53^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 19^1) (n := 53^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  have h_53_1 : (ArithmeticFunction.sigma 1 (53^1) : ℕ) = 54 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 53)]
    norm_num
  rw [h_2_2, h_19_1, h_53_1]
  norm_num

private lemma sigma_4029 : (ArithmeticFunction.sigma 1 4029 : ℕ) = 5760 := by
  have hfac : 4029 = 3^1 * (17^1 * (79^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 17^1 * (79^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 17^1) (n := 79^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  have h_79_1 : (ArithmeticFunction.sigma 1 (79^1) : ℕ) = 80 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 79)]
    norm_num
  rw [h_3_1, h_17_1, h_79_1]
  norm_num

private lemma sigma_4030 : (ArithmeticFunction.sigma 1 4030 : ℕ) = 8064 := by
  have hfac : 4030 = 2^1 * (5^1 * (13^1 * (31^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 5^1 * (13^1 * (31^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 13^1 * (31^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 31^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_31_1 : (ArithmeticFunction.sigma 1 (31^1) : ℕ) = 32 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31)]
    norm_num
  rw [h_2_1, h_5_1, h_13_1, h_31_1]
  norm_num

private lemma sigma_4031 : (ArithmeticFunction.sigma 1 4031 : ℕ) = 4200 := by
  have hfac : 4031 = 29^1 * (139^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 29^1) (n := 139^1) (by norm_num [Nat.gcd])]
  have h_29_1 : (ArithmeticFunction.sigma 1 (29^1) : ℕ) = 30 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 29)]
    norm_num
  have h_139_1 : (ArithmeticFunction.sigma 1 (139^1) : ℕ) = 140 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 139)]
    norm_num
  rw [h_29_1, h_139_1]
  norm_num

private lemma sigma_4032 : (ArithmeticFunction.sigma 1 4032 : ℕ) = 13208 := by
  have hfac : 4032 = 2^6 * (3^2 * (7^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^6) (n := 3^2 * (7^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 7^1) (by norm_num [Nat.gcd])]
  have h_2_6 : (ArithmeticFunction.sigma 1 (2^6) : ℕ) = 127 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  rw [h_2_6, h_3_2, h_7_1]
  norm_num

private lemma sigma_4033 : (ArithmeticFunction.sigma 1 4033 : ℕ) = 4180 := by
  have hfac : 4033 = 37^1 * (109^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 37^1) (n := 109^1) (by norm_num [Nat.gcd])]
  have h_37_1 : (ArithmeticFunction.sigma 1 (37^1) : ℕ) = 38 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 37)]
    norm_num
  have h_109_1 : (ArithmeticFunction.sigma 1 (109^1) : ℕ) = 110 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 109)]
    norm_num
  rw [h_37_1, h_109_1]
  norm_num

private lemma sigma_4034 : (ArithmeticFunction.sigma 1 4034 : ℕ) = 6054 := by
  have hfac : 4034 = 2^1 * (2017^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2017^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2017_1 : (ArithmeticFunction.sigma 1 (2017^1) : ℕ) = 2018 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2017)]
    norm_num
  rw [h_2_1, h_2017_1]
  norm_num

private lemma sigma_4035 : (ArithmeticFunction.sigma 1 4035 : ℕ) = 6480 := by
  have hfac : 4035 = 3^1 * (5^1 * (269^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 5^1 * (269^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 269^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_269_1 : (ArithmeticFunction.sigma 1 (269^1) : ℕ) = 270 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 269)]
    norm_num
  rw [h_3_1, h_5_1, h_269_1]
  norm_num

private lemma sigma_4036 : (ArithmeticFunction.sigma 1 4036 : ℕ) = 7070 := by
  have hfac : 4036 = 2^2 * (1009^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 1009^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_1009_1 : (ArithmeticFunction.sigma 1 (1009^1) : ℕ) = 1010 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1009)]
    norm_num
  rw [h_2_2, h_1009_1]
  norm_num

private lemma sigma_4037 : (ArithmeticFunction.sigma 1 4037 : ℕ) = 4416 := by
  have hfac : 4037 = 11^1 * (367^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 367^1) (by norm_num [Nat.gcd])]
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_367_1 : (ArithmeticFunction.sigma 1 (367^1) : ℕ) = 368 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 367)]
    norm_num
  rw [h_11_1, h_367_1]
  norm_num

private lemma sigma_4038 : (ArithmeticFunction.sigma 1 4038 : ℕ) = 8088 := by
  have hfac : 4038 = 2^1 * (3^1 * (673^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (673^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 673^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_673_1 : (ArithmeticFunction.sigma 1 (673^1) : ℕ) = 674 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 673)]
    norm_num
  rw [h_2_1, h_3_1, h_673_1]
  norm_num

private lemma sigma_4039 : (ArithmeticFunction.sigma 1 4039 : ℕ) = 4624 := by
  have hfac : 4039 = 7^1 * (577^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 577^1) (by norm_num [Nat.gcd])]
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_577_1 : (ArithmeticFunction.sigma 1 (577^1) : ℕ) = 578 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 577)]
    norm_num
  rw [h_7_1, h_577_1]
  norm_num

private lemma sigma_4040 : (ArithmeticFunction.sigma 1 4040 : ℕ) = 9180 := by
  have hfac : 4040 = 2^3 * (5^1 * (101^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 5^1 * (101^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 101^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_101_1 : (ArithmeticFunction.sigma 1 (101^1) : ℕ) = 102 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 101)]
    norm_num
  rw [h_2_3, h_5_1, h_101_1]
  norm_num

private lemma sigma_4041 : (ArithmeticFunction.sigma 1 4041 : ℕ) = 5850 := by
  have hfac : 4041 = 3^2 * (449^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 449^1) (by norm_num [Nat.gcd])]
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_449_1 : (ArithmeticFunction.sigma 1 (449^1) : ℕ) = 450 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 449)]
    norm_num
  rw [h_3_2, h_449_1]
  norm_num

private lemma sigma_4042 : (ArithmeticFunction.sigma 1 4042 : ℕ) = 6336 := by
  have hfac : 4042 = 2^1 * (43^1 * (47^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 43^1 * (47^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 43^1) (n := 47^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_43_1 : (ArithmeticFunction.sigma 1 (43^1) : ℕ) = 44 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 43)]
    norm_num
  have h_47_1 : (ArithmeticFunction.sigma 1 (47^1) : ℕ) = 48 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 47)]
    norm_num
  rw [h_2_1, h_43_1, h_47_1]
  norm_num

private lemma sigma_4043 : (ArithmeticFunction.sigma 1 4043 : ℕ) = 4368 := by
  have hfac : 4043 = 13^1 * (311^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 311^1) (by norm_num [Nat.gcd])]
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_311_1 : (ArithmeticFunction.sigma 1 (311^1) : ℕ) = 312 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 311)]
    norm_num
  rw [h_13_1, h_311_1]
  norm_num

private lemma sigma_4044 : (ArithmeticFunction.sigma 1 4044 : ℕ) = 9464 := by
  have hfac : 4044 = 2^2 * (3^1 * (337^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 3^1 * (337^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 337^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_337_1 : (ArithmeticFunction.sigma 1 (337^1) : ℕ) = 338 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 337)]
    norm_num
  rw [h_2_2, h_3_1, h_337_1]
  norm_num

private lemma sigma_4045 : (ArithmeticFunction.sigma 1 4045 : ℕ) = 4860 := by
  have hfac : 4045 = 5^1 * (809^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 809^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_809_1 : (ArithmeticFunction.sigma 1 (809^1) : ℕ) = 810 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 809)]
    norm_num
  rw [h_5_1, h_809_1]
  norm_num

private lemma sigma_4046 : (ArithmeticFunction.sigma 1 4046 : ℕ) = 7368 := by
  have hfac : 4046 = 2^1 * (7^1 * (17^2)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 7^1 * (17^2)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 17^2) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_17_2 : (ArithmeticFunction.sigma 1 (17^2) : ℕ) = 307 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  rw [h_2_1, h_7_1, h_17_2]
  norm_num

private lemma sigma_4047 : (ArithmeticFunction.sigma 1 4047 : ℕ) = 5760 := by
  have hfac : 4047 = 3^1 * (19^1 * (71^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 19^1 * (71^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 19^1) (n := 71^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  have h_71_1 : (ArithmeticFunction.sigma 1 (71^1) : ℕ) = 72 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 71)]
    norm_num
  rw [h_3_1, h_19_1, h_71_1]
  norm_num

private lemma sigma_4048 : (ArithmeticFunction.sigma 1 4048 : ℕ) = 8928 := by
  have hfac : 4048 = 2^4 * (11^1 * (23^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^4) (n := 11^1 * (23^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 23^1) (by norm_num [Nat.gcd])]
  have h_2_4 : (ArithmeticFunction.sigma 1 (2^4) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_23_1 : (ArithmeticFunction.sigma 1 (23^1) : ℕ) = 24 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
    norm_num
  rw [h_2_4, h_11_1, h_23_1]
  norm_num

private lemma sigma_4049 : (ArithmeticFunction.sigma 1 4049 : ℕ) = 4050 := by
  change (ArithmeticFunction.sigma 1 (4049^1) : ℕ) = 4050
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4049)]
  norm_num

private lemma sigma_4050 : (ArithmeticFunction.sigma 1 4050 : ℕ) = 11253 := by
  have hfac : 4050 = 2^1 * (3^4 * (5^2)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^4 * (5^2)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^4) (n := 5^2) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_4 : (ArithmeticFunction.sigma 1 (3^4) : ℕ) = 121 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_2 : (ArithmeticFunction.sigma 1 (5^2) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  rw [h_2_1, h_3_4, h_5_2]
  norm_num

private lemma sigma_4051 : (ArithmeticFunction.sigma 1 4051 : ℕ) = 4052 := by
  change (ArithmeticFunction.sigma 1 (4051^1) : ℕ) = 4052
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4051)]
  norm_num

private lemma sigma_4052 : (ArithmeticFunction.sigma 1 4052 : ℕ) = 7098 := by
  have hfac : 4052 = 2^2 * (1013^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 1013^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_1013_1 : (ArithmeticFunction.sigma 1 (1013^1) : ℕ) = 1014 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1013)]
    norm_num
  rw [h_2_2, h_1013_1]
  norm_num

private lemma sigma_4053 : (ArithmeticFunction.sigma 1 4053 : ℕ) = 6208 := by
  have hfac : 4053 = 3^1 * (7^1 * (193^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 7^1 * (193^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 193^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_193_1 : (ArithmeticFunction.sigma 1 (193^1) : ℕ) = 194 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 193)]
    norm_num
  rw [h_3_1, h_7_1, h_193_1]
  norm_num

private lemma sigma_4054 : (ArithmeticFunction.sigma 1 4054 : ℕ) = 6084 := by
  have hfac : 4054 = 2^1 * (2027^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2027^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2027_1 : (ArithmeticFunction.sigma 1 (2027^1) : ℕ) = 2028 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2027)]
    norm_num
  rw [h_2_1, h_2027_1]
  norm_num

private lemma sigma_4055 : (ArithmeticFunction.sigma 1 4055 : ℕ) = 4872 := by
  have hfac : 4055 = 5^1 * (811^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 811^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_811_1 : (ArithmeticFunction.sigma 1 (811^1) : ℕ) = 812 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 811)]
    norm_num
  rw [h_5_1, h_811_1]
  norm_num

private lemma sigma_4056 : (ArithmeticFunction.sigma 1 4056 : ℕ) = 10980 := by
  have hfac : 4056 = 2^3 * (3^1 * (13^2)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 3^1 * (13^2)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 13^2) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_13_2 : (ArithmeticFunction.sigma 1 (13^2) : ℕ) = 183 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  rw [h_2_3, h_3_1, h_13_2]
  norm_num

private lemma sigma_4057 : (ArithmeticFunction.sigma 1 4057 : ℕ) = 4058 := by
  change (ArithmeticFunction.sigma 1 (4057^1) : ℕ) = 4058
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4057)]
  norm_num

private lemma sigma_4058 : (ArithmeticFunction.sigma 1 4058 : ℕ) = 6090 := by
  have hfac : 4058 = 2^1 * (2029^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2029^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2029_1 : (ArithmeticFunction.sigma 1 (2029^1) : ℕ) = 2030 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2029)]
    norm_num
  rw [h_2_1, h_2029_1]
  norm_num

private lemma sigma_4059 : (ArithmeticFunction.sigma 1 4059 : ℕ) = 6552 := by
  have hfac : 4059 = 3^2 * (11^1 * (41^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 11^1 * (41^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 41^1) (by norm_num [Nat.gcd])]
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_41_1 : (ArithmeticFunction.sigma 1 (41^1) : ℕ) = 42 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 41)]
    norm_num
  rw [h_3_2, h_11_1, h_41_1]
  norm_num

private lemma sigma_4060 : (ArithmeticFunction.sigma 1 4060 : ℕ) = 10080 := by
  have hfac : 4060 = 2^2 * (5^1 * (7^1 * (29^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 5^1 * (7^1 * (29^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 7^1 * (29^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 29^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_29_1 : (ArithmeticFunction.sigma 1 (29^1) : ℕ) = 30 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 29)]
    norm_num
  rw [h_2_2, h_5_1, h_7_1, h_29_1]
  norm_num

private lemma sigma_4061 : (ArithmeticFunction.sigma 1 4061 : ℕ) = 4224 := by
  have hfac : 4061 = 31^1 * (131^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 31^1) (n := 131^1) (by norm_num [Nat.gcd])]
  have h_31_1 : (ArithmeticFunction.sigma 1 (31^1) : ℕ) = 32 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31)]
    norm_num
  have h_131_1 : (ArithmeticFunction.sigma 1 (131^1) : ℕ) = 132 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 131)]
    norm_num
  rw [h_31_1, h_131_1]
  norm_num

private lemma sigma_4062 : (ArithmeticFunction.sigma 1 4062 : ℕ) = 8136 := by
  have hfac : 4062 = 2^1 * (3^1 * (677^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (677^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 677^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_677_1 : (ArithmeticFunction.sigma 1 (677^1) : ℕ) = 678 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 677)]
    norm_num
  rw [h_2_1, h_3_1, h_677_1]
  norm_num

private lemma sigma_4063 : (ArithmeticFunction.sigma 1 4063 : ℕ) = 4320 := by
  have hfac : 4063 = 17^1 * (239^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 17^1) (n := 239^1) (by norm_num [Nat.gcd])]
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  have h_239_1 : (ArithmeticFunction.sigma 1 (239^1) : ℕ) = 240 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 239)]
    norm_num
  rw [h_17_1, h_239_1]
  norm_num

private lemma sigma_4064 : (ArithmeticFunction.sigma 1 4064 : ℕ) = 8064 := by
  have hfac : 4064 = 2^5 * (127^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^5) (n := 127^1) (by norm_num [Nat.gcd])]
  have h_2_5 : (ArithmeticFunction.sigma 1 (2^5) : ℕ) = 63 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_127_1 : (ArithmeticFunction.sigma 1 (127^1) : ℕ) = 128 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 127)]
    norm_num
  rw [h_2_5, h_127_1]
  norm_num

private lemma sigma_4065 : (ArithmeticFunction.sigma 1 4065 : ℕ) = 6528 := by
  have hfac : 4065 = 3^1 * (5^1 * (271^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 5^1 * (271^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 271^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_271_1 : (ArithmeticFunction.sigma 1 (271^1) : ℕ) = 272 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 271)]
    norm_num
  rw [h_3_1, h_5_1, h_271_1]
  norm_num

private lemma sigma_4066 : (ArithmeticFunction.sigma 1 4066 : ℕ) = 6480 := by
  have hfac : 4066 = 2^1 * (19^1 * (107^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 19^1 * (107^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 19^1) (n := 107^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  have h_107_1 : (ArithmeticFunction.sigma 1 (107^1) : ℕ) = 108 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 107)]
    norm_num
  rw [h_2_1, h_19_1, h_107_1]
  norm_num

private lemma sigma_4067 : (ArithmeticFunction.sigma 1 4067 : ℕ) = 4788 := by
  have hfac : 4067 = 7^2 * (83^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^2) (n := 83^1) (by norm_num [Nat.gcd])]
  have h_7_2 : (ArithmeticFunction.sigma 1 (7^2) : ℕ) = 57 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_83_1 : (ArithmeticFunction.sigma 1 (83^1) : ℕ) = 84 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 83)]
    norm_num
  rw [h_7_2, h_83_1]
  norm_num

private lemma sigma_4068 : (ArithmeticFunction.sigma 1 4068 : ℕ) = 10374 := by
  have hfac : 4068 = 2^2 * (3^2 * (113^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 3^2 * (113^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 113^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_113_1 : (ArithmeticFunction.sigma 1 (113^1) : ℕ) = 114 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 113)]
    norm_num
  rw [h_2_2, h_3_2, h_113_1]
  norm_num

private lemma sigma_4069 : (ArithmeticFunction.sigma 1 4069 : ℕ) = 4396 := by
  have hfac : 4069 = 13^1 * (313^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 313^1) (by norm_num [Nat.gcd])]
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_313_1 : (ArithmeticFunction.sigma 1 (313^1) : ℕ) = 314 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 313)]
    norm_num
  rw [h_13_1, h_313_1]
  norm_num

private lemma sigma_4070 : (ArithmeticFunction.sigma 1 4070 : ℕ) = 8208 := by
  have hfac : 4070 = 2^1 * (5^1 * (11^1 * (37^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 5^1 * (11^1 * (37^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 11^1 * (37^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 37^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_37_1 : (ArithmeticFunction.sigma 1 (37^1) : ℕ) = 38 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 37)]
    norm_num
  rw [h_2_1, h_5_1, h_11_1, h_37_1]
  norm_num

private lemma sigma_4071 : (ArithmeticFunction.sigma 1 4071 : ℕ) = 5760 := by
  have hfac : 4071 = 3^1 * (23^1 * (59^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 23^1 * (59^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 23^1) (n := 59^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_23_1 : (ArithmeticFunction.sigma 1 (23^1) : ℕ) = 24 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
    norm_num
  have h_59_1 : (ArithmeticFunction.sigma 1 (59^1) : ℕ) = 60 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 59)]
    norm_num
  rw [h_3_1, h_23_1, h_59_1]
  norm_num

private lemma sigma_4072 : (ArithmeticFunction.sigma 1 4072 : ℕ) = 7650 := by
  have hfac : 4072 = 2^3 * (509^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 509^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_509_1 : (ArithmeticFunction.sigma 1 (509^1) : ℕ) = 510 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 509)]
    norm_num
  rw [h_2_3, h_509_1]
  norm_num

private lemma sigma_4073 : (ArithmeticFunction.sigma 1 4073 : ℕ) = 4074 := by
  change (ArithmeticFunction.sigma 1 (4073^1) : ℕ) = 4074
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4073)]
  norm_num

private lemma sigma_4074 : (ArithmeticFunction.sigma 1 4074 : ℕ) = 9408 := by
  have hfac : 4074 = 2^1 * (3^1 * (7^1 * (97^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (7^1 * (97^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 7^1 * (97^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 97^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_97_1 : (ArithmeticFunction.sigma 1 (97^1) : ℕ) = 98 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 97)]
    norm_num
  rw [h_2_1, h_3_1, h_7_1, h_97_1]
  norm_num

private lemma sigma_4075 : (ArithmeticFunction.sigma 1 4075 : ℕ) = 5084 := by
  have hfac : 4075 = 5^2 * (163^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^2) (n := 163^1) (by norm_num [Nat.gcd])]
  have h_5_2 : (ArithmeticFunction.sigma 1 (5^2) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_163_1 : (ArithmeticFunction.sigma 1 (163^1) : ℕ) = 164 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 163)]
    norm_num
  rw [h_5_2, h_163_1]
  norm_num

private lemma sigma_4076 : (ArithmeticFunction.sigma 1 4076 : ℕ) = 7140 := by
  have hfac : 4076 = 2^2 * (1019^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 1019^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_1019_1 : (ArithmeticFunction.sigma 1 (1019^1) : ℕ) = 1020 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1019)]
    norm_num
  rw [h_2_2, h_1019_1]
  norm_num

private lemma sigma_4077 : (ArithmeticFunction.sigma 1 4077 : ℕ) = 6080 := by
  have hfac : 4077 = 3^3 * (151^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^3) (n := 151^1) (by norm_num [Nat.gcd])]
  have h_3_3 : (ArithmeticFunction.sigma 1 (3^3) : ℕ) = 40 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_151_1 : (ArithmeticFunction.sigma 1 (151^1) : ℕ) = 152 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 151)]
    norm_num
  rw [h_3_3, h_151_1]
  norm_num

private lemma sigma_4078 : (ArithmeticFunction.sigma 1 4078 : ℕ) = 6120 := by
  have hfac : 4078 = 2^1 * (2039^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2039^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2039_1 : (ArithmeticFunction.sigma 1 (2039^1) : ℕ) = 2040 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2039)]
    norm_num
  rw [h_2_1, h_2039_1]
  norm_num

private lemma sigma_4079 : (ArithmeticFunction.sigma 1 4079 : ℕ) = 4080 := by
  change (ArithmeticFunction.sigma 1 (4079^1) : ℕ) = 4080
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4079)]
  norm_num

private lemma sigma_4080 : (ArithmeticFunction.sigma 1 4080 : ℕ) = 13392 := by
  have hfac : 4080 = 2^4 * (3^1 * (5^1 * (17^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^4) (n := 3^1 * (5^1 * (17^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 5^1 * (17^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 17^1) (by norm_num [Nat.gcd])]
  have h_2_4 : (ArithmeticFunction.sigma 1 (2^4) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  rw [h_2_4, h_3_1, h_5_1, h_17_1]
  norm_num

private lemma sigma_4081 : (ArithmeticFunction.sigma 1 4081 : ℕ) = 5184 := by
  have hfac : 4081 = 7^1 * (11^1 * (53^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 11^1 * (53^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 53^1) (by norm_num [Nat.gcd])]
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_53_1 : (ArithmeticFunction.sigma 1 (53^1) : ℕ) = 54 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 53)]
    norm_num
  rw [h_7_1, h_11_1, h_53_1]
  norm_num

private lemma sigma_4082 : (ArithmeticFunction.sigma 1 4082 : ℕ) = 6636 := by
  have hfac : 4082 = 2^1 * (13^1 * (157^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 13^1 * (157^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 157^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_157_1 : (ArithmeticFunction.sigma 1 (157^1) : ℕ) = 158 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 157)]
    norm_num
  rw [h_2_1, h_13_1, h_157_1]
  norm_num

private lemma sigma_4083 : (ArithmeticFunction.sigma 1 4083 : ℕ) = 5448 := by
  have hfac : 4083 = 3^1 * (1361^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 1361^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_1361_1 : (ArithmeticFunction.sigma 1 (1361^1) : ℕ) = 1362 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1361)]
    norm_num
  rw [h_3_1, h_1361_1]
  norm_num

private lemma sigma_4084 : (ArithmeticFunction.sigma 1 4084 : ℕ) = 7154 := by
  have hfac : 4084 = 2^2 * (1021^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 1021^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_1021_1 : (ArithmeticFunction.sigma 1 (1021^1) : ℕ) = 1022 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1021)]
    norm_num
  rw [h_2_2, h_1021_1]
  norm_num

private lemma sigma_4085 : (ArithmeticFunction.sigma 1 4085 : ℕ) = 5280 := by
  have hfac : 4085 = 5^1 * (19^1 * (43^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 19^1 * (43^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 19^1) (n := 43^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  have h_43_1 : (ArithmeticFunction.sigma 1 (43^1) : ℕ) = 44 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 43)]
    norm_num
  rw [h_5_1, h_19_1, h_43_1]
  norm_num

private lemma sigma_4086 : (ArithmeticFunction.sigma 1 4086 : ℕ) = 8892 := by
  have hfac : 4086 = 2^1 * (3^2 * (227^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^2 * (227^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 227^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_227_1 : (ArithmeticFunction.sigma 1 (227^1) : ℕ) = 228 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 227)]
    norm_num
  rw [h_2_1, h_3_2, h_227_1]
  norm_num

private lemma sigma_4087 : (ArithmeticFunction.sigma 1 4087 : ℕ) = 4216 := by
  have hfac : 4087 = 61^1 * (67^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 61^1) (n := 67^1) (by norm_num [Nat.gcd])]
  have h_61_1 : (ArithmeticFunction.sigma 1 (61^1) : ℕ) = 62 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 61)]
    norm_num
  have h_67_1 : (ArithmeticFunction.sigma 1 (67^1) : ℕ) = 68 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 67)]
    norm_num
  rw [h_61_1, h_67_1]
  norm_num

private lemma sigma_4088 : (ArithmeticFunction.sigma 1 4088 : ℕ) = 8880 := by
  have hfac : 4088 = 2^3 * (7^1 * (73^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 7^1 * (73^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 73^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_73_1 : (ArithmeticFunction.sigma 1 (73^1) : ℕ) = 74 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 73)]
    norm_num
  rw [h_2_3, h_7_1, h_73_1]
  norm_num

private lemma sigma_4089 : (ArithmeticFunction.sigma 1 4089 : ℕ) = 5760 := by
  have hfac : 4089 = 3^1 * (29^1 * (47^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 29^1 * (47^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 29^1) (n := 47^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_29_1 : (ArithmeticFunction.sigma 1 (29^1) : ℕ) = 30 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 29)]
    norm_num
  have h_47_1 : (ArithmeticFunction.sigma 1 (47^1) : ℕ) = 48 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 47)]
    norm_num
  rw [h_3_1, h_29_1, h_47_1]
  norm_num

private lemma sigma_4090 : (ArithmeticFunction.sigma 1 4090 : ℕ) = 7380 := by
  have hfac : 4090 = 2^1 * (5^1 * (409^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 5^1 * (409^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 409^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_409_1 : (ArithmeticFunction.sigma 1 (409^1) : ℕ) = 410 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 409)]
    norm_num
  rw [h_2_1, h_5_1, h_409_1]
  norm_num

private lemma sigma_4091 : (ArithmeticFunction.sigma 1 4091 : ℕ) = 4092 := by
  change (ArithmeticFunction.sigma 1 (4091^1) : ℕ) = 4092
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4091)]
  norm_num

private lemma sigma_4092 : (ArithmeticFunction.sigma 1 4092 : ℕ) = 10752 := by
  have hfac : 4092 = 2^2 * (3^1 * (11^1 * (31^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 3^1 * (11^1 * (31^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 11^1 * (31^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 31^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_31_1 : (ArithmeticFunction.sigma 1 (31^1) : ℕ) = 32 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31)]
    norm_num
  rw [h_2_2, h_3_1, h_11_1, h_31_1]
  norm_num

private lemma sigma_4093 : (ArithmeticFunction.sigma 1 4093 : ℕ) = 4094 := by
  change (ArithmeticFunction.sigma 1 (4093^1) : ℕ) = 4094
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4093)]
  norm_num

private lemma sigma_4094 : (ArithmeticFunction.sigma 1 4094 : ℕ) = 6480 := by
  have hfac : 4094 = 2^1 * (23^1 * (89^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 23^1 * (89^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 23^1) (n := 89^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_23_1 : (ArithmeticFunction.sigma 1 (23^1) : ℕ) = 24 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
    norm_num
  have h_89_1 : (ArithmeticFunction.sigma 1 (89^1) : ℕ) = 90 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 89)]
    norm_num
  rw [h_2_1, h_23_1, h_89_1]
  norm_num

private lemma sigma_4095 : (ArithmeticFunction.sigma 1 4095 : ℕ) = 8736 := by
  have hfac : 4095 = 3^2 * (5^1 * (7^1 * (13^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 5^1 * (7^1 * (13^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 7^1 * (13^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 13^1) (by norm_num [Nat.gcd])]
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  rw [h_3_2, h_5_1, h_7_1, h_13_1]
  norm_num

private lemma sigma_4096 : (ArithmeticFunction.sigma 1 4096 : ℕ) = 8191 := by
  change (ArithmeticFunction.sigma 1 (2^12) : ℕ) = 8191
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
  norm_num

private lemma sigma_4097 : (ArithmeticFunction.sigma 1 4097 : ℕ) = 4356 := by
  have hfac : 4097 = 17^1 * (241^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 17^1) (n := 241^1) (by norm_num [Nat.gcd])]
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  have h_241_1 : (ArithmeticFunction.sigma 1 (241^1) : ℕ) = 242 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 241)]
    norm_num
  rw [h_17_1, h_241_1]
  norm_num

private lemma sigma_4098 : (ArithmeticFunction.sigma 1 4098 : ℕ) = 8208 := by
  have hfac : 4098 = 2^1 * (3^1 * (683^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (683^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 683^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_683_1 : (ArithmeticFunction.sigma 1 (683^1) : ℕ) = 684 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 683)]
    norm_num
  rw [h_2_1, h_3_1, h_683_1]
  norm_num

private lemma sigma_4099 : (ArithmeticFunction.sigma 1 4099 : ℕ) = 4100 := by
  change (ArithmeticFunction.sigma 1 (4099^1) : ℕ) = 4100
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4099)]
  norm_num

private lemma sigma_4100 : (ArithmeticFunction.sigma 1 4100 : ℕ) = 9114 := by
  have hfac : 4100 = 2^2 * (5^2 * (41^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 5^2 * (41^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^2) (n := 41^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_2 : (ArithmeticFunction.sigma 1 (5^2) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_41_1 : (ArithmeticFunction.sigma 1 (41^1) : ℕ) = 42 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 41)]
    norm_num
  rw [h_2_2, h_5_2, h_41_1]
  norm_num

private lemma sigma_4101 : (ArithmeticFunction.sigma 1 4101 : ℕ) = 5472 := by
  have hfac : 4101 = 3^1 * (1367^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 1367^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_1367_1 : (ArithmeticFunction.sigma 1 (1367^1) : ℕ) = 1368 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1367)]
    norm_num
  rw [h_3_1, h_1367_1]
  norm_num

private lemma sigma_4102 : (ArithmeticFunction.sigma 1 4102 : ℕ) = 7056 := by
  have hfac : 4102 = 2^1 * (7^1 * (293^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 7^1 * (293^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 293^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_293_1 : (ArithmeticFunction.sigma 1 (293^1) : ℕ) = 294 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 293)]
    norm_num
  rw [h_2_1, h_7_1, h_293_1]
  norm_num

private lemma sigma_4103 : (ArithmeticFunction.sigma 1 4103 : ℕ) = 4488 := by
  have hfac : 4103 = 11^1 * (373^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 373^1) (by norm_num [Nat.gcd])]
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_373_1 : (ArithmeticFunction.sigma 1 (373^1) : ℕ) = 374 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 373)]
    norm_num
  rw [h_11_1, h_373_1]
  norm_num

private lemma sigma_4104 : (ArithmeticFunction.sigma 1 4104 : ℕ) = 12000 := by
  have hfac : 4104 = 2^3 * (3^3 * (19^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 3^3 * (19^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^3) (n := 19^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_3 : (ArithmeticFunction.sigma 1 (3^3) : ℕ) = 40 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  rw [h_2_3, h_3_3, h_19_1]
  norm_num

private lemma sigma_4105 : (ArithmeticFunction.sigma 1 4105 : ℕ) = 4932 := by
  have hfac : 4105 = 5^1 * (821^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 821^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_821_1 : (ArithmeticFunction.sigma 1 (821^1) : ℕ) = 822 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 821)]
    norm_num
  rw [h_5_1, h_821_1]
  norm_num

private lemma sigma_4106 : (ArithmeticFunction.sigma 1 4106 : ℕ) = 6162 := by
  have hfac : 4106 = 2^1 * (2053^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2053^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2053_1 : (ArithmeticFunction.sigma 1 (2053^1) : ℕ) = 2054 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2053)]
    norm_num
  rw [h_2_1, h_2053_1]
  norm_num

private lemma sigma_4107 : (ArithmeticFunction.sigma 1 4107 : ℕ) = 5628 := by
  have hfac : 4107 = 3^1 * (37^2) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 37^2) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_37_2 : (ArithmeticFunction.sigma 1 (37^2) : ℕ) = 1407 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 37)]
    norm_num
  rw [h_3_1, h_37_2]
  norm_num

private lemma sigma_4108 : (ArithmeticFunction.sigma 1 4108 : ℕ) = 7840 := by
  have hfac : 4108 = 2^2 * (13^1 * (79^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 13^1 * (79^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 79^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_79_1 : (ArithmeticFunction.sigma 1 (79^1) : ℕ) = 80 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 79)]
    norm_num
  rw [h_2_2, h_13_1, h_79_1]
  norm_num

private lemma sigma_4109 : (ArithmeticFunction.sigma 1 4109 : ℕ) = 4704 := by
  have hfac : 4109 = 7^1 * (587^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 587^1) (by norm_num [Nat.gcd])]
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_587_1 : (ArithmeticFunction.sigma 1 (587^1) : ℕ) = 588 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 587)]
    norm_num
  rw [h_7_1, h_587_1]
  norm_num

private lemma sigma_4110 : (ArithmeticFunction.sigma 1 4110 : ℕ) = 9936 := by
  have hfac : 4110 = 2^1 * (3^1 * (5^1 * (137^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (5^1 * (137^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 5^1 * (137^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 137^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_137_1 : (ArithmeticFunction.sigma 1 (137^1) : ℕ) = 138 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 137)]
    norm_num
  rw [h_2_1, h_3_1, h_5_1, h_137_1]
  norm_num

private lemma sigma_4111 : (ArithmeticFunction.sigma 1 4111 : ℕ) = 4112 := by
  change (ArithmeticFunction.sigma 1 (4111^1) : ℕ) = 4112
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4111)]
  norm_num

private lemma sigma_4112 : (ArithmeticFunction.sigma 1 4112 : ℕ) = 7998 := by
  have hfac : 4112 = 2^4 * (257^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^4) (n := 257^1) (by norm_num [Nat.gcd])]
  have h_2_4 : (ArithmeticFunction.sigma 1 (2^4) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_257_1 : (ArithmeticFunction.sigma 1 (257^1) : ℕ) = 258 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 257)]
    norm_num
  rw [h_2_4, h_257_1]
  norm_num

private lemma sigma_4113 : (ArithmeticFunction.sigma 1 4113 : ℕ) = 5954 := by
  have hfac : 4113 = 3^2 * (457^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 457^1) (by norm_num [Nat.gcd])]
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_457_1 : (ArithmeticFunction.sigma 1 (457^1) : ℕ) = 458 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 457)]
    norm_num
  rw [h_3_2, h_457_1]
  norm_num

private lemma sigma_4114 : (ArithmeticFunction.sigma 1 4114 : ℕ) = 7182 := by
  have hfac : 4114 = 2^1 * (11^2 * (17^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 11^2 * (17^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^2) (n := 17^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_11_2 : (ArithmeticFunction.sigma 1 (11^2) : ℕ) = 133 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  rw [h_2_1, h_11_2, h_17_1]
  norm_num

private lemma sigma_4115 : (ArithmeticFunction.sigma 1 4115 : ℕ) = 4944 := by
  have hfac : 4115 = 5^1 * (823^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 823^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_823_1 : (ArithmeticFunction.sigma 1 (823^1) : ℕ) = 824 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 823)]
    norm_num
  rw [h_5_1, h_823_1]
  norm_num

private lemma sigma_4116 : (ArithmeticFunction.sigma 1 4116 : ℕ) = 11200 := by
  have hfac : 4116 = 2^2 * (3^1 * (7^3)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 3^1 * (7^3)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 7^3) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_7_3 : (ArithmeticFunction.sigma 1 (7^3) : ℕ) = 400 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  rw [h_2_2, h_3_1, h_7_3]
  norm_num

private lemma sigma_4117 : (ArithmeticFunction.sigma 1 4117 : ℕ) = 4320 := by
  have hfac : 4117 = 23^1 * (179^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 23^1) (n := 179^1) (by norm_num [Nat.gcd])]
  have h_23_1 : (ArithmeticFunction.sigma 1 (23^1) : ℕ) = 24 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
    norm_num
  have h_179_1 : (ArithmeticFunction.sigma 1 (179^1) : ℕ) = 180 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 179)]
    norm_num
  rw [h_23_1, h_179_1]
  norm_num

private lemma sigma_4118 : (ArithmeticFunction.sigma 1 4118 : ℕ) = 6480 := by
  have hfac : 4118 = 2^1 * (29^1 * (71^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 29^1 * (71^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 29^1) (n := 71^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_29_1 : (ArithmeticFunction.sigma 1 (29^1) : ℕ) = 30 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 29)]
    norm_num
  have h_71_1 : (ArithmeticFunction.sigma 1 (71^1) : ℕ) = 72 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 71)]
    norm_num
  rw [h_2_1, h_29_1, h_71_1]
  norm_num

private lemma sigma_4119 : (ArithmeticFunction.sigma 1 4119 : ℕ) = 5496 := by
  have hfac : 4119 = 3^1 * (1373^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 1373^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_1373_1 : (ArithmeticFunction.sigma 1 (1373^1) : ℕ) = 1374 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1373)]
    norm_num
  rw [h_3_1, h_1373_1]
  norm_num

private lemma sigma_4120 : (ArithmeticFunction.sigma 1 4120 : ℕ) = 9360 := by
  have hfac : 4120 = 2^3 * (5^1 * (103^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 5^1 * (103^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 103^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_103_1 : (ArithmeticFunction.sigma 1 (103^1) : ℕ) = 104 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 103)]
    norm_num
  rw [h_2_3, h_5_1, h_103_1]
  norm_num

private lemma sigma_4121 : (ArithmeticFunction.sigma 1 4121 : ℕ) = 4452 := by
  have hfac : 4121 = 13^1 * (317^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 317^1) (by norm_num [Nat.gcd])]
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_317_1 : (ArithmeticFunction.sigma 1 (317^1) : ℕ) = 318 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 317)]
    norm_num
  rw [h_13_1, h_317_1]
  norm_num

private lemma sigma_4122 : (ArithmeticFunction.sigma 1 4122 : ℕ) = 8970 := by
  have hfac : 4122 = 2^1 * (3^2 * (229^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^2 * (229^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 229^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_229_1 : (ArithmeticFunction.sigma 1 (229^1) : ℕ) = 230 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 229)]
    norm_num
  rw [h_2_1, h_3_2, h_229_1]
  norm_num

private lemma sigma_4123 : (ArithmeticFunction.sigma 1 4123 : ℕ) = 5120 := by
  have hfac : 4123 = 7^1 * (19^1 * (31^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 19^1 * (31^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 19^1) (n := 31^1) (by norm_num [Nat.gcd])]
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  have h_31_1 : (ArithmeticFunction.sigma 1 (31^1) : ℕ) = 32 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31)]
    norm_num
  rw [h_7_1, h_19_1, h_31_1]
  norm_num

private lemma sigma_4124 : (ArithmeticFunction.sigma 1 4124 : ℕ) = 7224 := by
  have hfac : 4124 = 2^2 * (1031^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 1031^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_1031_1 : (ArithmeticFunction.sigma 1 (1031^1) : ℕ) = 1032 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1031)]
    norm_num
  rw [h_2_2, h_1031_1]
  norm_num

private lemma sigma_4125 : (ArithmeticFunction.sigma 1 4125 : ℕ) = 7488 := by
  have hfac : 4125 = 3^1 * (5^3 * (11^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 5^3 * (11^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^3) (n := 11^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_3 : (ArithmeticFunction.sigma 1 (5^3) : ℕ) = 156 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  rw [h_3_1, h_5_3, h_11_1]
  norm_num

private lemma sigma_4126 : (ArithmeticFunction.sigma 1 4126 : ℕ) = 6192 := by
  have hfac : 4126 = 2^1 * (2063^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2063^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2063_1 : (ArithmeticFunction.sigma 1 (2063^1) : ℕ) = 2064 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2063)]
    norm_num
  rw [h_2_1, h_2063_1]
  norm_num

private lemma sigma_4127 : (ArithmeticFunction.sigma 1 4127 : ℕ) = 4128 := by
  change (ArithmeticFunction.sigma 1 (4127^1) : ℕ) = 4128
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4127)]
  norm_num

private lemma sigma_4128 : (ArithmeticFunction.sigma 1 4128 : ℕ) = 11088 := by
  have hfac : 4128 = 2^5 * (3^1 * (43^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^5) (n := 3^1 * (43^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 43^1) (by norm_num [Nat.gcd])]
  have h_2_5 : (ArithmeticFunction.sigma 1 (2^5) : ℕ) = 63 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_43_1 : (ArithmeticFunction.sigma 1 (43^1) : ℕ) = 44 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 43)]
    norm_num
  rw [h_2_5, h_3_1, h_43_1]
  norm_num

private lemma sigma_4129 : (ArithmeticFunction.sigma 1 4129 : ℕ) = 4130 := by
  change (ArithmeticFunction.sigma 1 (4129^1) : ℕ) = 4130
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4129)]
  norm_num

private lemma sigma_4130 : (ArithmeticFunction.sigma 1 4130 : ℕ) = 8640 := by
  have hfac : 4130 = 2^1 * (5^1 * (7^1 * (59^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 5^1 * (7^1 * (59^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 7^1 * (59^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 59^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_59_1 : (ArithmeticFunction.sigma 1 (59^1) : ℕ) = 60 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 59)]
    norm_num
  rw [h_2_1, h_5_1, h_7_1, h_59_1]
  norm_num

private lemma sigma_4131 : (ArithmeticFunction.sigma 1 4131 : ℕ) = 6552 := by
  have hfac : 4131 = 3^5 * (17^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^5) (n := 17^1) (by norm_num [Nat.gcd])]
  have h_3_5 : (ArithmeticFunction.sigma 1 (3^5) : ℕ) = 364 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  rw [h_3_5, h_17_1]
  norm_num

private lemma sigma_4132 : (ArithmeticFunction.sigma 1 4132 : ℕ) = 7238 := by
  have hfac : 4132 = 2^2 * (1033^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 1033^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_1033_1 : (ArithmeticFunction.sigma 1 (1033^1) : ℕ) = 1034 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1033)]
    norm_num
  rw [h_2_2, h_1033_1]
  norm_num

private lemma sigma_4133 : (ArithmeticFunction.sigma 1 4133 : ℕ) = 4134 := by
  change (ArithmeticFunction.sigma 1 (4133^1) : ℕ) = 4134
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4133)]
  norm_num

private lemma sigma_4134 : (ArithmeticFunction.sigma 1 4134 : ℕ) = 9072 := by
  have hfac : 4134 = 2^1 * (3^1 * (13^1 * (53^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (13^1 * (53^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 13^1 * (53^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 53^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_53_1 : (ArithmeticFunction.sigma 1 (53^1) : ℕ) = 54 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 53)]
    norm_num
  rw [h_2_1, h_3_1, h_13_1, h_53_1]
  norm_num

private lemma sigma_4135 : (ArithmeticFunction.sigma 1 4135 : ℕ) = 4968 := by
  have hfac : 4135 = 5^1 * (827^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 827^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_827_1 : (ArithmeticFunction.sigma 1 (827^1) : ℕ) = 828 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 827)]
    norm_num
  rw [h_5_1, h_827_1]
  norm_num

private lemma sigma_4136 : (ArithmeticFunction.sigma 1 4136 : ℕ) = 8640 := by
  have hfac : 4136 = 2^3 * (11^1 * (47^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 11^1 * (47^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 47^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_47_1 : (ArithmeticFunction.sigma 1 (47^1) : ℕ) = 48 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 47)]
    norm_num
  rw [h_2_3, h_11_1, h_47_1]
  norm_num

private lemma sigma_4137 : (ArithmeticFunction.sigma 1 4137 : ℕ) = 6336 := by
  have hfac : 4137 = 3^1 * (7^1 * (197^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 7^1 * (197^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 197^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_197_1 : (ArithmeticFunction.sigma 1 (197^1) : ℕ) = 198 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 197)]
    norm_num
  rw [h_3_1, h_7_1, h_197_1]
  norm_num

private lemma sigma_4138 : (ArithmeticFunction.sigma 1 4138 : ℕ) = 6210 := by
  have hfac : 4138 = 2^1 * (2069^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2069^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2069_1 : (ArithmeticFunction.sigma 1 (2069^1) : ℕ) = 2070 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2069)]
    norm_num
  rw [h_2_1, h_2069_1]
  norm_num

private lemma sigma_4139 : (ArithmeticFunction.sigma 1 4139 : ℕ) = 4140 := by
  change (ArithmeticFunction.sigma 1 (4139^1) : ℕ) = 4140
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4139)]
  norm_num

private lemma sigma_4140 : (ArithmeticFunction.sigma 1 4140 : ℕ) = 13104 := by
  have hfac : 4140 = 2^2 * (3^2 * (5^1 * (23^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 3^2 * (5^1 * (23^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 5^1 * (23^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 23^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_23_1 : (ArithmeticFunction.sigma 1 (23^1) : ℕ) = 24 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
    norm_num
  rw [h_2_2, h_3_2, h_5_1, h_23_1]
  norm_num

private lemma sigma_4141 : (ArithmeticFunction.sigma 1 4141 : ℕ) = 4284 := by
  have hfac : 4141 = 41^1 * (101^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 41^1) (n := 101^1) (by norm_num [Nat.gcd])]
  have h_41_1 : (ArithmeticFunction.sigma 1 (41^1) : ℕ) = 42 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 41)]
    norm_num
  have h_101_1 : (ArithmeticFunction.sigma 1 (101^1) : ℕ) = 102 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 101)]
    norm_num
  rw [h_41_1, h_101_1]
  norm_num

private lemma sigma_4142 : (ArithmeticFunction.sigma 1 4142 : ℕ) = 6600 := by
  have hfac : 4142 = 2^1 * (19^1 * (109^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 19^1 * (109^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 19^1) (n := 109^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  have h_109_1 : (ArithmeticFunction.sigma 1 (109^1) : ℕ) = 110 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 109)]
    norm_num
  rw [h_2_1, h_19_1, h_109_1]
  norm_num

private lemma sigma_4143 : (ArithmeticFunction.sigma 1 4143 : ℕ) = 5528 := by
  have hfac : 4143 = 3^1 * (1381^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 1381^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_1381_1 : (ArithmeticFunction.sigma 1 (1381^1) : ℕ) = 1382 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1381)]
    norm_num
  rw [h_3_1, h_1381_1]
  norm_num

private lemma sigma_4144 : (ArithmeticFunction.sigma 1 4144 : ℕ) = 9424 := by
  have hfac : 4144 = 2^4 * (7^1 * (37^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^4) (n := 7^1 * (37^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 37^1) (by norm_num [Nat.gcd])]
  have h_2_4 : (ArithmeticFunction.sigma 1 (2^4) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_37_1 : (ArithmeticFunction.sigma 1 (37^1) : ℕ) = 38 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 37)]
    norm_num
  rw [h_2_4, h_7_1, h_37_1]
  norm_num

private lemma sigma_4145 : (ArithmeticFunction.sigma 1 4145 : ℕ) = 4980 := by
  have hfac : 4145 = 5^1 * (829^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 829^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_829_1 : (ArithmeticFunction.sigma 1 (829^1) : ℕ) = 830 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 829)]
    norm_num
  rw [h_5_1, h_829_1]
  norm_num

private lemma sigma_4146 : (ArithmeticFunction.sigma 1 4146 : ℕ) = 8304 := by
  have hfac : 4146 = 2^1 * (3^1 * (691^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (691^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 691^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_691_1 : (ArithmeticFunction.sigma 1 (691^1) : ℕ) = 692 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 691)]
    norm_num
  rw [h_2_1, h_3_1, h_691_1]
  norm_num

private lemma sigma_4147 : (ArithmeticFunction.sigma 1 4147 : ℕ) = 5040 := by
  have hfac : 4147 = 11^1 * (13^1 * (29^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 13^1 * (29^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 29^1) (by norm_num [Nat.gcd])]
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_29_1 : (ArithmeticFunction.sigma 1 (29^1) : ℕ) = 30 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 29)]
    norm_num
  rw [h_11_1, h_13_1, h_29_1]
  norm_num

private lemma sigma_4148 : (ArithmeticFunction.sigma 1 4148 : ℕ) = 7812 := by
  have hfac : 4148 = 2^2 * (17^1 * (61^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 17^1 * (61^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 17^1) (n := 61^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  have h_61_1 : (ArithmeticFunction.sigma 1 (61^1) : ℕ) = 62 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 61)]
    norm_num
  rw [h_2_2, h_17_1, h_61_1]
  norm_num

private lemma sigma_4149 : (ArithmeticFunction.sigma 1 4149 : ℕ) = 6006 := by
  have hfac : 4149 = 3^2 * (461^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 461^1) (by norm_num [Nat.gcd])]
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_461_1 : (ArithmeticFunction.sigma 1 (461^1) : ℕ) = 462 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 461)]
    norm_num
  rw [h_3_2, h_461_1]
  norm_num

private lemma sigma_4150 : (ArithmeticFunction.sigma 1 4150 : ℕ) = 7812 := by
  have hfac : 4150 = 2^1 * (5^2 * (83^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 5^2 * (83^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^2) (n := 83^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_2 : (ArithmeticFunction.sigma 1 (5^2) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_83_1 : (ArithmeticFunction.sigma 1 (83^1) : ℕ) = 84 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 83)]
    norm_num
  rw [h_2_1, h_5_2, h_83_1]
  norm_num

private lemma sigma_4151 : (ArithmeticFunction.sigma 1 4151 : ℕ) = 4752 := by
  have hfac : 4151 = 7^1 * (593^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 593^1) (by norm_num [Nat.gcd])]
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_593_1 : (ArithmeticFunction.sigma 1 (593^1) : ℕ) = 594 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 593)]
    norm_num
  rw [h_7_1, h_593_1]
  norm_num

private lemma sigma_4152 : (ArithmeticFunction.sigma 1 4152 : ℕ) = 10440 := by
  have hfac : 4152 = 2^3 * (3^1 * (173^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 3^1 * (173^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 173^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_173_1 : (ArithmeticFunction.sigma 1 (173^1) : ℕ) = 174 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 173)]
    norm_num
  rw [h_2_3, h_3_1, h_173_1]
  norm_num

private lemma sigma_4153 : (ArithmeticFunction.sigma 1 4153 : ℕ) = 4154 := by
  change (ArithmeticFunction.sigma 1 (4153^1) : ℕ) = 4154
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4153)]
  norm_num

private lemma sigma_4154 : (ArithmeticFunction.sigma 1 4154 : ℕ) = 6528 := by
  have hfac : 4154 = 2^1 * (31^1 * (67^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 31^1 * (67^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 31^1) (n := 67^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_31_1 : (ArithmeticFunction.sigma 1 (31^1) : ℕ) = 32 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31)]
    norm_num
  have h_67_1 : (ArithmeticFunction.sigma 1 (67^1) : ℕ) = 68 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 67)]
    norm_num
  rw [h_2_1, h_31_1, h_67_1]
  norm_num

private lemma sigma_4155 : (ArithmeticFunction.sigma 1 4155 : ℕ) = 6672 := by
  have hfac : 4155 = 3^1 * (5^1 * (277^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 5^1 * (277^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 277^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_277_1 : (ArithmeticFunction.sigma 1 (277^1) : ℕ) = 278 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 277)]
    norm_num
  rw [h_3_1, h_5_1, h_277_1]
  norm_num

private lemma sigma_4156 : (ArithmeticFunction.sigma 1 4156 : ℕ) = 7280 := by
  have hfac : 4156 = 2^2 * (1039^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 1039^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_1039_1 : (ArithmeticFunction.sigma 1 (1039^1) : ℕ) = 1040 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1039)]
    norm_num
  rw [h_2_2, h_1039_1]
  norm_num

private lemma sigma_4157 : (ArithmeticFunction.sigma 1 4157 : ℕ) = 4158 := by
  change (ArithmeticFunction.sigma 1 (4157^1) : ℕ) = 4158
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4157)]
  norm_num

private lemma sigma_4158 : (ArithmeticFunction.sigma 1 4158 : ℕ) = 11520 := by
  have hfac : 4158 = 2^1 * (3^3 * (7^1 * (11^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^3 * (7^1 * (11^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^3) (n := 7^1 * (11^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 11^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_3 : (ArithmeticFunction.sigma 1 (3^3) : ℕ) = 40 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  rw [h_2_1, h_3_3, h_7_1, h_11_1]
  norm_num

private lemma sigma_4159 : (ArithmeticFunction.sigma 1 4159 : ℕ) = 4160 := by
  change (ArithmeticFunction.sigma 1 (4159^1) : ℕ) = 4160
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4159)]
  norm_num

private lemma sigma_4160 : (ArithmeticFunction.sigma 1 4160 : ℕ) = 10668 := by
  have hfac : 4160 = 2^6 * (5^1 * (13^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^6) (n := 5^1 * (13^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 13^1) (by norm_num [Nat.gcd])]
  have h_2_6 : (ArithmeticFunction.sigma 1 (2^6) : ℕ) = 127 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  rw [h_2_6, h_5_1, h_13_1]
  norm_num

private lemma sigma_4161 : (ArithmeticFunction.sigma 1 4161 : ℕ) = 5920 := by
  have hfac : 4161 = 3^1 * (19^1 * (73^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 19^1 * (73^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 19^1) (n := 73^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  have h_73_1 : (ArithmeticFunction.sigma 1 (73^1) : ℕ) = 74 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 73)]
    norm_num
  rw [h_3_1, h_19_1, h_73_1]
  norm_num

private lemma sigma_4162 : (ArithmeticFunction.sigma 1 4162 : ℕ) = 6246 := by
  have hfac : 4162 = 2^1 * (2081^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2081^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2081_1 : (ArithmeticFunction.sigma 1 (2081^1) : ℕ) = 2082 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2081)]
    norm_num
  rw [h_2_1, h_2081_1]
  norm_num

private lemma sigma_4163 : (ArithmeticFunction.sigma 1 4163 : ℕ) = 4368 := by
  have hfac : 4163 = 23^1 * (181^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 23^1) (n := 181^1) (by norm_num [Nat.gcd])]
  have h_23_1 : (ArithmeticFunction.sigma 1 (23^1) : ℕ) = 24 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
    norm_num
  have h_181_1 : (ArithmeticFunction.sigma 1 (181^1) : ℕ) = 182 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 181)]
    norm_num
  rw [h_23_1, h_181_1]
  norm_num

private lemma sigma_4164 : (ArithmeticFunction.sigma 1 4164 : ℕ) = 9744 := by
  have hfac : 4164 = 2^2 * (3^1 * (347^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 3^1 * (347^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 347^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_347_1 : (ArithmeticFunction.sigma 1 (347^1) : ℕ) = 348 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 347)]
    norm_num
  rw [h_2_2, h_3_1, h_347_1]
  norm_num

private lemma sigma_4165 : (ArithmeticFunction.sigma 1 4165 : ℕ) = 6156 := by
  have hfac : 4165 = 5^1 * (7^2 * (17^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 7^2 * (17^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^2) (n := 17^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_7_2 : (ArithmeticFunction.sigma 1 (7^2) : ℕ) = 57 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  rw [h_5_1, h_7_2, h_17_1]
  norm_num

private lemma sigma_4166 : (ArithmeticFunction.sigma 1 4166 : ℕ) = 6252 := by
  have hfac : 4166 = 2^1 * (2083^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2083^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2083_1 : (ArithmeticFunction.sigma 1 (2083^1) : ℕ) = 2084 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2083)]
    norm_num
  rw [h_2_1, h_2083_1]
  norm_num

private lemma sigma_4167 : (ArithmeticFunction.sigma 1 4167 : ℕ) = 6032 := by
  have hfac : 4167 = 3^2 * (463^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 463^1) (by norm_num [Nat.gcd])]
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_463_1 : (ArithmeticFunction.sigma 1 (463^1) : ℕ) = 464 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 463)]
    norm_num
  rw [h_3_2, h_463_1]
  norm_num

private lemma sigma_4168 : (ArithmeticFunction.sigma 1 4168 : ℕ) = 7830 := by
  have hfac : 4168 = 2^3 * (521^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 521^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_521_1 : (ArithmeticFunction.sigma 1 (521^1) : ℕ) = 522 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 521)]
    norm_num
  rw [h_2_3, h_521_1]
  norm_num

private lemma sigma_4169 : (ArithmeticFunction.sigma 1 4169 : ℕ) = 4560 := by
  have hfac : 4169 = 11^1 * (379^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 379^1) (by norm_num [Nat.gcd])]
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_379_1 : (ArithmeticFunction.sigma 1 (379^1) : ℕ) = 380 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 379)]
    norm_num
  rw [h_11_1, h_379_1]
  norm_num

private lemma sigma_4170 : (ArithmeticFunction.sigma 1 4170 : ℕ) = 10080 := by
  have hfac : 4170 = 2^1 * (3^1 * (5^1 * (139^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (5^1 * (139^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 5^1 * (139^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 139^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_139_1 : (ArithmeticFunction.sigma 1 (139^1) : ℕ) = 140 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 139)]
    norm_num
  rw [h_2_1, h_3_1, h_5_1, h_139_1]
  norm_num

private lemma sigma_4171 : (ArithmeticFunction.sigma 1 4171 : ℕ) = 4312 := by
  have hfac : 4171 = 43^1 * (97^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 43^1) (n := 97^1) (by norm_num [Nat.gcd])]
  have h_43_1 : (ArithmeticFunction.sigma 1 (43^1) : ℕ) = 44 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 43)]
    norm_num
  have h_97_1 : (ArithmeticFunction.sigma 1 (97^1) : ℕ) = 98 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 97)]
    norm_num
  rw [h_43_1, h_97_1]
  norm_num

private lemma sigma_4172 : (ArithmeticFunction.sigma 1 4172 : ℕ) = 8400 := by
  have hfac : 4172 = 2^2 * (7^1 * (149^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 7^1 * (149^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 149^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_149_1 : (ArithmeticFunction.sigma 1 (149^1) : ℕ) = 150 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 149)]
    norm_num
  rw [h_2_2, h_7_1, h_149_1]
  norm_num

private lemma sigma_4173 : (ArithmeticFunction.sigma 1 4173 : ℕ) = 6048 := by
  have hfac : 4173 = 3^1 * (13^1 * (107^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 13^1 * (107^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 107^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_107_1 : (ArithmeticFunction.sigma 1 (107^1) : ℕ) = 108 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 107)]
    norm_num
  rw [h_3_1, h_13_1, h_107_1]
  norm_num

private lemma sigma_4174 : (ArithmeticFunction.sigma 1 4174 : ℕ) = 6264 := by
  have hfac : 4174 = 2^1 * (2087^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2087^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2087_1 : (ArithmeticFunction.sigma 1 (2087^1) : ℕ) = 2088 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2087)]
    norm_num
  rw [h_2_1, h_2087_1]
  norm_num

private lemma sigma_4175 : (ArithmeticFunction.sigma 1 4175 : ℕ) = 5208 := by
  have hfac : 4175 = 5^2 * (167^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^2) (n := 167^1) (by norm_num [Nat.gcd])]
  have h_5_2 : (ArithmeticFunction.sigma 1 (5^2) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_167_1 : (ArithmeticFunction.sigma 1 (167^1) : ℕ) = 168 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 167)]
    norm_num
  rw [h_5_2, h_167_1]
  norm_num

private lemma sigma_4176 : (ArithmeticFunction.sigma 1 4176 : ℕ) = 12090 := by
  have hfac : 4176 = 2^4 * (3^2 * (29^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^4) (n := 3^2 * (29^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 29^1) (by norm_num [Nat.gcd])]
  have h_2_4 : (ArithmeticFunction.sigma 1 (2^4) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_29_1 : (ArithmeticFunction.sigma 1 (29^1) : ℕ) = 30 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 29)]
    norm_num
  rw [h_2_4, h_3_2, h_29_1]
  norm_num

private lemma sigma_4177 : (ArithmeticFunction.sigma 1 4177 : ℕ) = 4178 := by
  change (ArithmeticFunction.sigma 1 (4177^1) : ℕ) = 4178
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4177)]
  norm_num

private lemma sigma_4178 : (ArithmeticFunction.sigma 1 4178 : ℕ) = 6270 := by
  have hfac : 4178 = 2^1 * (2089^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2089^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2089_1 : (ArithmeticFunction.sigma 1 (2089^1) : ℕ) = 2090 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2089)]
    norm_num
  rw [h_2_1, h_2089_1]
  norm_num

private lemma sigma_4179 : (ArithmeticFunction.sigma 1 4179 : ℕ) = 6400 := by
  have hfac : 4179 = 3^1 * (7^1 * (199^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 7^1 * (199^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 199^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_199_1 : (ArithmeticFunction.sigma 1 (199^1) : ℕ) = 200 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 199)]
    norm_num
  rw [h_3_1, h_7_1, h_199_1]
  norm_num

private lemma sigma_4180 : (ArithmeticFunction.sigma 1 4180 : ℕ) = 10080 := by
  have hfac : 4180 = 2^2 * (5^1 * (11^1 * (19^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 5^1 * (11^1 * (19^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 11^1 * (19^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 19^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  rw [h_2_2, h_5_1, h_11_1, h_19_1]
  norm_num

private lemma sigma_4181 : (ArithmeticFunction.sigma 1 4181 : ℕ) = 4332 := by
  have hfac : 4181 = 37^1 * (113^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 37^1) (n := 113^1) (by norm_num [Nat.gcd])]
  have h_37_1 : (ArithmeticFunction.sigma 1 (37^1) : ℕ) = 38 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 37)]
    norm_num
  have h_113_1 : (ArithmeticFunction.sigma 1 (113^1) : ℕ) = 114 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 113)]
    norm_num
  rw [h_37_1, h_113_1]
  norm_num

private lemma sigma_4182 : (ArithmeticFunction.sigma 1 4182 : ℕ) = 9072 := by
  have hfac : 4182 = 2^1 * (3^1 * (17^1 * (41^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (17^1 * (41^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 17^1 * (41^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 17^1) (n := 41^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  have h_41_1 : (ArithmeticFunction.sigma 1 (41^1) : ℕ) = 42 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 41)]
    norm_num
  rw [h_2_1, h_3_1, h_17_1, h_41_1]
  norm_num

private lemma sigma_4183 : (ArithmeticFunction.sigma 1 4183 : ℕ) = 4320 := by
  have hfac : 4183 = 47^1 * (89^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 47^1) (n := 89^1) (by norm_num [Nat.gcd])]
  have h_47_1 : (ArithmeticFunction.sigma 1 (47^1) : ℕ) = 48 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 47)]
    norm_num
  have h_89_1 : (ArithmeticFunction.sigma 1 (89^1) : ℕ) = 90 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 89)]
    norm_num
  rw [h_47_1, h_89_1]
  norm_num

private lemma sigma_4184 : (ArithmeticFunction.sigma 1 4184 : ℕ) = 7860 := by
  have hfac : 4184 = 2^3 * (523^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 523^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_523_1 : (ArithmeticFunction.sigma 1 (523^1) : ℕ) = 524 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 523)]
    norm_num
  rw [h_2_3, h_523_1]
  norm_num

private lemma sigma_4185 : (ArithmeticFunction.sigma 1 4185 : ℕ) = 7680 := by
  have hfac : 4185 = 3^3 * (5^1 * (31^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^3) (n := 5^1 * (31^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 31^1) (by norm_num [Nat.gcd])]
  have h_3_3 : (ArithmeticFunction.sigma 1 (3^3) : ℕ) = 40 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_31_1 : (ArithmeticFunction.sigma 1 (31^1) : ℕ) = 32 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31)]
    norm_num
  rw [h_3_3, h_5_1, h_31_1]
  norm_num

private lemma sigma_4186 : (ArithmeticFunction.sigma 1 4186 : ℕ) = 8064 := by
  have hfac : 4186 = 2^1 * (7^1 * (13^1 * (23^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 7^1 * (13^1 * (23^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 13^1 * (23^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 23^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_23_1 : (ArithmeticFunction.sigma 1 (23^1) : ℕ) = 24 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
    norm_num
  rw [h_2_1, h_7_1, h_13_1, h_23_1]
  norm_num

private lemma sigma_4187 : (ArithmeticFunction.sigma 1 4187 : ℕ) = 4320 := by
  have hfac : 4187 = 53^1 * (79^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 53^1) (n := 79^1) (by norm_num [Nat.gcd])]
  have h_53_1 : (ArithmeticFunction.sigma 1 (53^1) : ℕ) = 54 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 53)]
    norm_num
  have h_79_1 : (ArithmeticFunction.sigma 1 (79^1) : ℕ) = 80 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 79)]
    norm_num
  rw [h_53_1, h_79_1]
  norm_num

private lemma sigma_4188 : (ArithmeticFunction.sigma 1 4188 : ℕ) = 9800 := by
  have hfac : 4188 = 2^2 * (3^1 * (349^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 3^1 * (349^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 349^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_349_1 : (ArithmeticFunction.sigma 1 (349^1) : ℕ) = 350 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 349)]
    norm_num
  rw [h_2_2, h_3_1, h_349_1]
  norm_num

private lemma sigma_4189 : (ArithmeticFunction.sigma 1 4189 : ℕ) = 4320 := by
  have hfac : 4189 = 59^1 * (71^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 59^1) (n := 71^1) (by norm_num [Nat.gcd])]
  have h_59_1 : (ArithmeticFunction.sigma 1 (59^1) : ℕ) = 60 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 59)]
    norm_num
  have h_71_1 : (ArithmeticFunction.sigma 1 (71^1) : ℕ) = 72 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 71)]
    norm_num
  rw [h_59_1, h_71_1]
  norm_num

private lemma sigma_4190 : (ArithmeticFunction.sigma 1 4190 : ℕ) = 7560 := by
  have hfac : 4190 = 2^1 * (5^1 * (419^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 5^1 * (419^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 419^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_419_1 : (ArithmeticFunction.sigma 1 (419^1) : ℕ) = 420 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 419)]
    norm_num
  rw [h_2_1, h_5_1, h_419_1]
  norm_num

private lemma sigma_4191 : (ArithmeticFunction.sigma 1 4191 : ℕ) = 6144 := by
  have hfac : 4191 = 3^1 * (11^1 * (127^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 11^1 * (127^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 127^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_127_1 : (ArithmeticFunction.sigma 1 (127^1) : ℕ) = 128 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 127)]
    norm_num
  rw [h_3_1, h_11_1, h_127_1]
  norm_num

private lemma sigma_4192 : (ArithmeticFunction.sigma 1 4192 : ℕ) = 8316 := by
  have hfac : 4192 = 2^5 * (131^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^5) (n := 131^1) (by norm_num [Nat.gcd])]
  have h_2_5 : (ArithmeticFunction.sigma 1 (2^5) : ℕ) = 63 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_131_1 : (ArithmeticFunction.sigma 1 (131^1) : ℕ) = 132 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 131)]
    norm_num
  rw [h_2_5, h_131_1]
  norm_num

private lemma sigma_4193 : (ArithmeticFunction.sigma 1 4193 : ℕ) = 4800 := by
  have hfac : 4193 = 7^1 * (599^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 599^1) (by norm_num [Nat.gcd])]
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_599_1 : (ArithmeticFunction.sigma 1 (599^1) : ℕ) = 600 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 599)]
    norm_num
  rw [h_7_1, h_599_1]
  norm_num

private lemma sigma_4194 : (ArithmeticFunction.sigma 1 4194 : ℕ) = 9126 := by
  have hfac : 4194 = 2^1 * (3^2 * (233^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^2 * (233^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 233^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_233_1 : (ArithmeticFunction.sigma 1 (233^1) : ℕ) = 234 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 233)]
    norm_num
  rw [h_2_1, h_3_2, h_233_1]
  norm_num

private lemma sigma_4195 : (ArithmeticFunction.sigma 1 4195 : ℕ) = 5040 := by
  have hfac : 4195 = 5^1 * (839^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 839^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_839_1 : (ArithmeticFunction.sigma 1 (839^1) : ℕ) = 840 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 839)]
    norm_num
  rw [h_5_1, h_839_1]
  norm_num

private lemma sigma_4196 : (ArithmeticFunction.sigma 1 4196 : ℕ) = 7350 := by
  have hfac : 4196 = 2^2 * (1049^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 1049^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_1049_1 : (ArithmeticFunction.sigma 1 (1049^1) : ℕ) = 1050 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1049)]
    norm_num
  rw [h_2_2, h_1049_1]
  norm_num

private lemma sigma_4197 : (ArithmeticFunction.sigma 1 4197 : ℕ) = 5600 := by
  have hfac : 4197 = 3^1 * (1399^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 1399^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_1399_1 : (ArithmeticFunction.sigma 1 (1399^1) : ℕ) = 1400 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1399)]
    norm_num
  rw [h_3_1, h_1399_1]
  norm_num

private lemma sigma_4198 : (ArithmeticFunction.sigma 1 4198 : ℕ) = 6300 := by
  have hfac : 4198 = 2^1 * (2099^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2099^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2099_1 : (ArithmeticFunction.sigma 1 (2099^1) : ℕ) = 2100 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2099)]
    norm_num
  rw [h_2_1, h_2099_1]
  norm_num

private lemma sigma_4199 : (ArithmeticFunction.sigma 1 4199 : ℕ) = 5040 := by
  have hfac : 4199 = 13^1 * (17^1 * (19^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 17^1 * (19^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 17^1) (n := 19^1) (by norm_num [Nat.gcd])]
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  rw [h_13_1, h_17_1, h_19_1]
  norm_num

private lemma sigma_4200 : (ArithmeticFunction.sigma 1 4200 : ℕ) = 14880 := by
  have hfac : 4200 = 2^3 * (3^1 * (5^2 * (7^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 3^1 * (5^2 * (7^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 5^2 * (7^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^2) (n := 7^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_2 : (ArithmeticFunction.sigma 1 (5^2) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  rw [h_2_3, h_3_1, h_5_2, h_7_1]
  norm_num

private lemma sigma_4201 : (ArithmeticFunction.sigma 1 4201 : ℕ) = 4202 := by
  change (ArithmeticFunction.sigma 1 (4201^1) : ℕ) = 4202
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4201)]
  norm_num

private lemma sigma_4202 : (ArithmeticFunction.sigma 1 4202 : ℕ) = 6912 := by
  have hfac : 4202 = 2^1 * (11^1 * (191^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 11^1 * (191^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 191^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_191_1 : (ArithmeticFunction.sigma 1 (191^1) : ℕ) = 192 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 191)]
    norm_num
  rw [h_2_1, h_11_1, h_191_1]
  norm_num

private lemma sigma_4203 : (ArithmeticFunction.sigma 1 4203 : ℕ) = 6084 := by
  have hfac : 4203 = 3^2 * (467^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 467^1) (by norm_num [Nat.gcd])]
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_467_1 : (ArithmeticFunction.sigma 1 (467^1) : ℕ) = 468 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 467)]
    norm_num
  rw [h_3_2, h_467_1]
  norm_num

private lemma sigma_4204 : (ArithmeticFunction.sigma 1 4204 : ℕ) = 7364 := by
  have hfac : 4204 = 2^2 * (1051^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 1051^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_1051_1 : (ArithmeticFunction.sigma 1 (1051^1) : ℕ) = 1052 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1051)]
    norm_num
  rw [h_2_2, h_1051_1]
  norm_num

private lemma sigma_4205 : (ArithmeticFunction.sigma 1 4205 : ℕ) = 5226 := by
  have hfac : 4205 = 5^1 * (29^2) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 29^2) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_29_2 : (ArithmeticFunction.sigma 1 (29^2) : ℕ) = 871 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 29)]
    norm_num
  rw [h_5_1, h_29_2]
  norm_num

private lemma sigma_4206 : (ArithmeticFunction.sigma 1 4206 : ℕ) = 8424 := by
  have hfac : 4206 = 2^1 * (3^1 * (701^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (701^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 701^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_701_1 : (ArithmeticFunction.sigma 1 (701^1) : ℕ) = 702 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 701)]
    norm_num
  rw [h_2_1, h_3_1, h_701_1]
  norm_num

private lemma sigma_4207 : (ArithmeticFunction.sigma 1 4207 : ℕ) = 4816 := by
  have hfac : 4207 = 7^1 * (601^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 601^1) (by norm_num [Nat.gcd])]
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_601_1 : (ArithmeticFunction.sigma 1 (601^1) : ℕ) = 602 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 601)]
    norm_num
  rw [h_7_1, h_601_1]
  norm_num

private lemma sigma_4208 : (ArithmeticFunction.sigma 1 4208 : ℕ) = 8184 := by
  have hfac : 4208 = 2^4 * (263^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^4) (n := 263^1) (by norm_num [Nat.gcd])]
  have h_2_4 : (ArithmeticFunction.sigma 1 (2^4) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_263_1 : (ArithmeticFunction.sigma 1 (263^1) : ℕ) = 264 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 263)]
    norm_num
  rw [h_2_4, h_263_1]
  norm_num

private lemma sigma_4209 : (ArithmeticFunction.sigma 1 4209 : ℕ) = 5952 := by
  have hfac : 4209 = 3^1 * (23^1 * (61^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 23^1 * (61^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 23^1) (n := 61^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_23_1 : (ArithmeticFunction.sigma 1 (23^1) : ℕ) = 24 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
    norm_num
  have h_61_1 : (ArithmeticFunction.sigma 1 (61^1) : ℕ) = 62 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 61)]
    norm_num
  rw [h_3_1, h_23_1, h_61_1]
  norm_num

private lemma sigma_4210 : (ArithmeticFunction.sigma 1 4210 : ℕ) = 7596 := by
  have hfac : 4210 = 2^1 * (5^1 * (421^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 5^1 * (421^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 421^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_421_1 : (ArithmeticFunction.sigma 1 (421^1) : ℕ) = 422 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 421)]
    norm_num
  rw [h_2_1, h_5_1, h_421_1]
  norm_num

private lemma sigma_4211 : (ArithmeticFunction.sigma 1 4211 : ℕ) = 4212 := by
  change (ArithmeticFunction.sigma 1 (4211^1) : ℕ) = 4212
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4211)]
  norm_num

private lemma sigma_4212 : (ArithmeticFunction.sigma 1 4212 : ℕ) = 11858 := by
  have hfac : 4212 = 2^2 * (3^4 * (13^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 3^4 * (13^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^4) (n := 13^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_4 : (ArithmeticFunction.sigma 1 (3^4) : ℕ) = 121 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  rw [h_2_2, h_3_4, h_13_1]
  norm_num

private lemma sigma_4213 : (ArithmeticFunction.sigma 1 4213 : ℕ) = 4608 := by
  have hfac : 4213 = 11^1 * (383^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 383^1) (by norm_num [Nat.gcd])]
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_383_1 : (ArithmeticFunction.sigma 1 (383^1) : ℕ) = 384 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 383)]
    norm_num
  rw [h_11_1, h_383_1]
  norm_num

private lemma sigma_4214 : (ArithmeticFunction.sigma 1 4214 : ℕ) = 7524 := by
  have hfac : 4214 = 2^1 * (7^2 * (43^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 7^2 * (43^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^2) (n := 43^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_7_2 : (ArithmeticFunction.sigma 1 (7^2) : ℕ) = 57 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_43_1 : (ArithmeticFunction.sigma 1 (43^1) : ℕ) = 44 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 43)]
    norm_num
  rw [h_2_1, h_7_2, h_43_1]
  norm_num

private lemma sigma_4215 : (ArithmeticFunction.sigma 1 4215 : ℕ) = 6768 := by
  have hfac : 4215 = 3^1 * (5^1 * (281^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 5^1 * (281^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 281^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_281_1 : (ArithmeticFunction.sigma 1 (281^1) : ℕ) = 282 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 281)]
    norm_num
  rw [h_3_1, h_5_1, h_281_1]
  norm_num

private lemma sigma_4216 : (ArithmeticFunction.sigma 1 4216 : ℕ) = 8640 := by
  have hfac : 4216 = 2^3 * (17^1 * (31^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 17^1 * (31^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 17^1) (n := 31^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  have h_31_1 : (ArithmeticFunction.sigma 1 (31^1) : ℕ) = 32 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31)]
    norm_num
  rw [h_2_3, h_17_1, h_31_1]
  norm_num

private lemma sigma_4217 : (ArithmeticFunction.sigma 1 4217 : ℕ) = 4218 := by
  change (ArithmeticFunction.sigma 1 (4217^1) : ℕ) = 4218
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4217)]
  norm_num

private lemma sigma_4218 : (ArithmeticFunction.sigma 1 4218 : ℕ) = 9120 := by
  have hfac : 4218 = 2^1 * (3^1 * (19^1 * (37^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (19^1 * (37^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 19^1 * (37^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 19^1) (n := 37^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  have h_37_1 : (ArithmeticFunction.sigma 1 (37^1) : ℕ) = 38 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 37)]
    norm_num
  rw [h_2_1, h_3_1, h_19_1, h_37_1]
  norm_num

private lemma sigma_4219 : (ArithmeticFunction.sigma 1 4219 : ℕ) = 4220 := by
  change (ArithmeticFunction.sigma 1 (4219^1) : ℕ) = 4220
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4219)]
  norm_num

private lemma sigma_4220 : (ArithmeticFunction.sigma 1 4220 : ℕ) = 8904 := by
  have hfac : 4220 = 2^2 * (5^1 * (211^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 5^1 * (211^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 211^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_211_1 : (ArithmeticFunction.sigma 1 (211^1) : ℕ) = 212 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 211)]
    norm_num
  rw [h_2_2, h_5_1, h_211_1]
  norm_num

private lemma sigma_4221 : (ArithmeticFunction.sigma 1 4221 : ℕ) = 7072 := by
  have hfac : 4221 = 3^2 * (7^1 * (67^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 7^1 * (67^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 67^1) (by norm_num [Nat.gcd])]
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_67_1 : (ArithmeticFunction.sigma 1 (67^1) : ℕ) = 68 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 67)]
    norm_num
  rw [h_3_2, h_7_1, h_67_1]
  norm_num

private lemma sigma_4222 : (ArithmeticFunction.sigma 1 4222 : ℕ) = 6336 := by
  have hfac : 4222 = 2^1 * (2111^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2111^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2111_1 : (ArithmeticFunction.sigma 1 (2111^1) : ℕ) = 2112 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2111)]
    norm_num
  rw [h_2_1, h_2111_1]
  norm_num

private lemma sigma_4223 : (ArithmeticFunction.sigma 1 4223 : ℕ) = 4368 := by
  have hfac : 4223 = 41^1 * (103^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 41^1) (n := 103^1) (by norm_num [Nat.gcd])]
  have h_41_1 : (ArithmeticFunction.sigma 1 (41^1) : ℕ) = 42 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 41)]
    norm_num
  have h_103_1 : (ArithmeticFunction.sigma 1 (103^1) : ℕ) = 104 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 103)]
    norm_num
  rw [h_41_1, h_103_1]
  norm_num

private lemma sigma_4224 : (ArithmeticFunction.sigma 1 4224 : ℕ) = 12240 := by
  have hfac : 4224 = 2^7 * (3^1 * (11^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^7) (n := 3^1 * (11^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 11^1) (by norm_num [Nat.gcd])]
  have h_2_7 : (ArithmeticFunction.sigma 1 (2^7) : ℕ) = 255 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  rw [h_2_7, h_3_1, h_11_1]
  norm_num

private lemma sigma_4225 : (ArithmeticFunction.sigma 1 4225 : ℕ) = 5673 := by
  have hfac : 4225 = 5^2 * (13^2) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^2) (n := 13^2) (by norm_num [Nat.gcd])]
  have h_5_2 : (ArithmeticFunction.sigma 1 (5^2) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_13_2 : (ArithmeticFunction.sigma 1 (13^2) : ℕ) = 183 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  rw [h_5_2, h_13_2]
  norm_num

private lemma sigma_4226 : (ArithmeticFunction.sigma 1 4226 : ℕ) = 6342 := by
  have hfac : 4226 = 2^1 * (2113^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2113^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2113_1 : (ArithmeticFunction.sigma 1 (2113^1) : ℕ) = 2114 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2113)]
    norm_num
  rw [h_2_1, h_2113_1]
  norm_num

private lemma sigma_4227 : (ArithmeticFunction.sigma 1 4227 : ℕ) = 5640 := by
  have hfac : 4227 = 3^1 * (1409^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 1409^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_1409_1 : (ArithmeticFunction.sigma 1 (1409^1) : ℕ) = 1410 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1409)]
    norm_num
  rw [h_3_1, h_1409_1]
  norm_num

private lemma sigma_4228 : (ArithmeticFunction.sigma 1 4228 : ℕ) = 8512 := by
  have hfac : 4228 = 2^2 * (7^1 * (151^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 7^1 * (151^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 151^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_151_1 : (ArithmeticFunction.sigma 1 (151^1) : ℕ) = 152 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 151)]
    norm_num
  rw [h_2_2, h_7_1, h_151_1]
  norm_num

private lemma sigma_4229 : (ArithmeticFunction.sigma 1 4229 : ℕ) = 4230 := by
  change (ArithmeticFunction.sigma 1 (4229^1) : ℕ) = 4230
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4229)]
  norm_num

private lemma sigma_4230 : (ArithmeticFunction.sigma 1 4230 : ℕ) = 11232 := by
  have hfac : 4230 = 2^1 * (3^2 * (5^1 * (47^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^2 * (5^1 * (47^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 5^1 * (47^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 47^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_47_1 : (ArithmeticFunction.sigma 1 (47^1) : ℕ) = 48 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 47)]
    norm_num
  rw [h_2_1, h_3_2, h_5_1, h_47_1]
  norm_num

private lemma sigma_4231 : (ArithmeticFunction.sigma 1 4231 : ℕ) = 4232 := by
  change (ArithmeticFunction.sigma 1 (4231^1) : ℕ) = 4232
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4231)]
  norm_num

private lemma sigma_4232 : (ArithmeticFunction.sigma 1 4232 : ℕ) = 8295 := by
  have hfac : 4232 = 2^3 * (23^2) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 23^2) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_23_2 : (ArithmeticFunction.sigma 1 (23^2) : ℕ) = 553 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
    norm_num
  rw [h_2_3, h_23_2]
  norm_num

private lemma sigma_4233 : (ArithmeticFunction.sigma 1 4233 : ℕ) = 6048 := by
  have hfac : 4233 = 3^1 * (17^1 * (83^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 17^1 * (83^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 17^1) (n := 83^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  have h_83_1 : (ArithmeticFunction.sigma 1 (83^1) : ℕ) = 84 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 83)]
    norm_num
  rw [h_3_1, h_17_1, h_83_1]
  norm_num

private lemma sigma_4234 : (ArithmeticFunction.sigma 1 4234 : ℕ) = 6660 := by
  have hfac : 4234 = 2^1 * (29^1 * (73^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 29^1 * (73^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 29^1) (n := 73^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_29_1 : (ArithmeticFunction.sigma 1 (29^1) : ℕ) = 30 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 29)]
    norm_num
  have h_73_1 : (ArithmeticFunction.sigma 1 (73^1) : ℕ) = 74 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 73)]
    norm_num
  rw [h_2_1, h_29_1, h_73_1]
  norm_num

private lemma sigma_4235 : (ArithmeticFunction.sigma 1 4235 : ℕ) = 6384 := by
  have hfac : 4235 = 5^1 * (7^1 * (11^2)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 7^1 * (11^2)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 11^2) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_11_2 : (ArithmeticFunction.sigma 1 (11^2) : ℕ) = 133 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  rw [h_5_1, h_7_1, h_11_2]
  norm_num

private lemma sigma_4236 : (ArithmeticFunction.sigma 1 4236 : ℕ) = 9912 := by
  have hfac : 4236 = 2^2 * (3^1 * (353^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 3^1 * (353^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 353^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_353_1 : (ArithmeticFunction.sigma 1 (353^1) : ℕ) = 354 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 353)]
    norm_num
  rw [h_2_2, h_3_1, h_353_1]
  norm_num

private lemma sigma_4237 : (ArithmeticFunction.sigma 1 4237 : ℕ) = 4480 := by
  have hfac : 4237 = 19^1 * (223^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 19^1) (n := 223^1) (by norm_num [Nat.gcd])]
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  have h_223_1 : (ArithmeticFunction.sigma 1 (223^1) : ℕ) = 224 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 223)]
    norm_num
  rw [h_19_1, h_223_1]
  norm_num

private lemma sigma_4238 : (ArithmeticFunction.sigma 1 4238 : ℕ) = 6888 := by
  have hfac : 4238 = 2^1 * (13^1 * (163^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 13^1 * (163^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 163^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_163_1 : (ArithmeticFunction.sigma 1 (163^1) : ℕ) = 164 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 163)]
    norm_num
  rw [h_2_1, h_13_1, h_163_1]
  norm_num

private lemma sigma_4239 : (ArithmeticFunction.sigma 1 4239 : ℕ) = 6320 := by
  have hfac : 4239 = 3^3 * (157^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^3) (n := 157^1) (by norm_num [Nat.gcd])]
  have h_3_3 : (ArithmeticFunction.sigma 1 (3^3) : ℕ) = 40 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_157_1 : (ArithmeticFunction.sigma 1 (157^1) : ℕ) = 158 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 157)]
    norm_num
  rw [h_3_3, h_157_1]
  norm_num

private lemma sigma_4240 : (ArithmeticFunction.sigma 1 4240 : ℕ) = 10044 := by
  have hfac : 4240 = 2^4 * (5^1 * (53^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^4) (n := 5^1 * (53^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 53^1) (by norm_num [Nat.gcd])]
  have h_2_4 : (ArithmeticFunction.sigma 1 (2^4) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_53_1 : (ArithmeticFunction.sigma 1 (53^1) : ℕ) = 54 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 53)]
    norm_num
  rw [h_2_4, h_5_1, h_53_1]
  norm_num

private lemma sigma_4241 : (ArithmeticFunction.sigma 1 4241 : ℕ) = 4242 := by
  change (ArithmeticFunction.sigma 1 (4241^1) : ℕ) = 4242
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4241)]
  norm_num

private lemma sigma_4242 : (ArithmeticFunction.sigma 1 4242 : ℕ) = 9792 := by
  have hfac : 4242 = 2^1 * (3^1 * (7^1 * (101^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (7^1 * (101^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 7^1 * (101^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 101^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_101_1 : (ArithmeticFunction.sigma 1 (101^1) : ℕ) = 102 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 101)]
    norm_num
  rw [h_2_1, h_3_1, h_7_1, h_101_1]
  norm_num

private lemma sigma_4243 : (ArithmeticFunction.sigma 1 4243 : ℕ) = 4244 := by
  change (ArithmeticFunction.sigma 1 (4243^1) : ℕ) = 4244
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4243)]
  norm_num

private lemma sigma_4244 : (ArithmeticFunction.sigma 1 4244 : ℕ) = 7434 := by
  have hfac : 4244 = 2^2 * (1061^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 1061^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_1061_1 : (ArithmeticFunction.sigma 1 (1061^1) : ℕ) = 1062 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1061)]
    norm_num
  rw [h_2_2, h_1061_1]
  norm_num

private lemma sigma_4245 : (ArithmeticFunction.sigma 1 4245 : ℕ) = 6816 := by
  have hfac : 4245 = 3^1 * (5^1 * (283^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 5^1 * (283^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 283^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_283_1 : (ArithmeticFunction.sigma 1 (283^1) : ℕ) = 284 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 283)]
    norm_num
  rw [h_3_1, h_5_1, h_283_1]
  norm_num

private lemma sigma_4246 : (ArithmeticFunction.sigma 1 4246 : ℕ) = 6984 := by
  have hfac : 4246 = 2^1 * (11^1 * (193^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 11^1 * (193^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 193^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_193_1 : (ArithmeticFunction.sigma 1 (193^1) : ℕ) = 194 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 193)]
    norm_num
  rw [h_2_1, h_11_1, h_193_1]
  norm_num

private lemma sigma_4247 : (ArithmeticFunction.sigma 1 4247 : ℕ) = 4416 := by
  have hfac : 4247 = 31^1 * (137^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 31^1) (n := 137^1) (by norm_num [Nat.gcd])]
  have h_31_1 : (ArithmeticFunction.sigma 1 (31^1) : ℕ) = 32 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31)]
    norm_num
  have h_137_1 : (ArithmeticFunction.sigma 1 (137^1) : ℕ) = 138 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 137)]
    norm_num
  rw [h_31_1, h_137_1]
  norm_num

private lemma sigma_4248 : (ArithmeticFunction.sigma 1 4248 : ℕ) = 11700 := by
  have hfac : 4248 = 2^3 * (3^2 * (59^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 3^2 * (59^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 59^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_59_1 : (ArithmeticFunction.sigma 1 (59^1) : ℕ) = 60 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 59)]
    norm_num
  rw [h_2_3, h_3_2, h_59_1]
  norm_num

private lemma sigma_4249 : (ArithmeticFunction.sigma 1 4249 : ℕ) = 4864 := by
  have hfac : 4249 = 7^1 * (607^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 607^1) (by norm_num [Nat.gcd])]
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_607_1 : (ArithmeticFunction.sigma 1 (607^1) : ℕ) = 608 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 607)]
    norm_num
  rw [h_7_1, h_607_1]
  norm_num

private lemma sigma_4250 : (ArithmeticFunction.sigma 1 4250 : ℕ) = 8424 := by
  have hfac : 4250 = 2^1 * (5^3 * (17^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 5^3 * (17^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^3) (n := 17^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_3 : (ArithmeticFunction.sigma 1 (5^3) : ℕ) = 156 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  rw [h_2_1, h_5_3, h_17_1]
  norm_num

private lemma sigma_4251 : (ArithmeticFunction.sigma 1 4251 : ℕ) = 6160 := by
  have hfac : 4251 = 3^1 * (13^1 * (109^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 13^1 * (109^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 109^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_109_1 : (ArithmeticFunction.sigma 1 (109^1) : ℕ) = 110 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 109)]
    norm_num
  rw [h_3_1, h_13_1, h_109_1]
  norm_num

private lemma sigma_4252 : (ArithmeticFunction.sigma 1 4252 : ℕ) = 7448 := by
  have hfac : 4252 = 2^2 * (1063^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 1063^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_1063_1 : (ArithmeticFunction.sigma 1 (1063^1) : ℕ) = 1064 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1063)]
    norm_num
  rw [h_2_2, h_1063_1]
  norm_num

private lemma sigma_4253 : (ArithmeticFunction.sigma 1 4253 : ℕ) = 4254 := by
  change (ArithmeticFunction.sigma 1 (4253^1) : ℕ) = 4254
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4253)]
  norm_num

private lemma sigma_4254 : (ArithmeticFunction.sigma 1 4254 : ℕ) = 8520 := by
  have hfac : 4254 = 2^1 * (3^1 * (709^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (709^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 709^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_709_1 : (ArithmeticFunction.sigma 1 (709^1) : ℕ) = 710 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 709)]
    norm_num
  rw [h_2_1, h_3_1, h_709_1]
  norm_num

private lemma sigma_4255 : (ArithmeticFunction.sigma 1 4255 : ℕ) = 5472 := by
  have hfac : 4255 = 5^1 * (23^1 * (37^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 23^1 * (37^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 23^1) (n := 37^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_23_1 : (ArithmeticFunction.sigma 1 (23^1) : ℕ) = 24 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
    norm_num
  have h_37_1 : (ArithmeticFunction.sigma 1 (37^1) : ℕ) = 38 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 37)]
    norm_num
  rw [h_5_1, h_23_1, h_37_1]
  norm_num

private lemma sigma_4256 : (ArithmeticFunction.sigma 1 4256 : ℕ) = 10080 := by
  have hfac : 4256 = 2^5 * (7^1 * (19^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^5) (n := 7^1 * (19^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 19^1) (by norm_num [Nat.gcd])]
  have h_2_5 : (ArithmeticFunction.sigma 1 (2^5) : ℕ) = 63 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  rw [h_2_5, h_7_1, h_19_1]
  norm_num

private lemma sigma_4257 : (ArithmeticFunction.sigma 1 4257 : ℕ) = 6864 := by
  have hfac : 4257 = 3^2 * (11^1 * (43^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 11^1 * (43^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 43^1) (by norm_num [Nat.gcd])]
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_43_1 : (ArithmeticFunction.sigma 1 (43^1) : ℕ) = 44 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 43)]
    norm_num
  rw [h_3_2, h_11_1, h_43_1]
  norm_num

private lemma sigma_4258 : (ArithmeticFunction.sigma 1 4258 : ℕ) = 6390 := by
  have hfac : 4258 = 2^1 * (2129^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2129^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2129_1 : (ArithmeticFunction.sigma 1 (2129^1) : ℕ) = 2130 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2129)]
    norm_num
  rw [h_2_1, h_2129_1]
  norm_num

private lemma sigma_4259 : (ArithmeticFunction.sigma 1 4259 : ℕ) = 4260 := by
  change (ArithmeticFunction.sigma 1 (4259^1) : ℕ) = 4260
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4259)]
  norm_num

private lemma sigma_4260 : (ArithmeticFunction.sigma 1 4260 : ℕ) = 12096 := by
  have hfac : 4260 = 2^2 * (3^1 * (5^1 * (71^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 3^1 * (5^1 * (71^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 5^1 * (71^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 71^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_71_1 : (ArithmeticFunction.sigma 1 (71^1) : ℕ) = 72 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 71)]
    norm_num
  rw [h_2_2, h_3_1, h_5_1, h_71_1]
  norm_num

private lemma sigma_4261 : (ArithmeticFunction.sigma 1 4261 : ℕ) = 4262 := by
  change (ArithmeticFunction.sigma 1 (4261^1) : ℕ) = 4262
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4261)]
  norm_num

private lemma sigma_4262 : (ArithmeticFunction.sigma 1 4262 : ℕ) = 6396 := by
  have hfac : 4262 = 2^1 * (2131^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2131^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2131_1 : (ArithmeticFunction.sigma 1 (2131^1) : ℕ) = 2132 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2131)]
    norm_num
  rw [h_2_1, h_2131_1]
  norm_num

private lemma sigma_4263 : (ArithmeticFunction.sigma 1 4263 : ℕ) = 6840 := by
  have hfac : 4263 = 3^1 * (7^2 * (29^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 7^2 * (29^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^2) (n := 29^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_7_2 : (ArithmeticFunction.sigma 1 (7^2) : ℕ) = 57 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_29_1 : (ArithmeticFunction.sigma 1 (29^1) : ℕ) = 30 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 29)]
    norm_num
  rw [h_3_1, h_7_2, h_29_1]
  norm_num

private lemma sigma_4264 : (ArithmeticFunction.sigma 1 4264 : ℕ) = 8820 := by
  have hfac : 4264 = 2^3 * (13^1 * (41^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 13^1 * (41^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 41^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_41_1 : (ArithmeticFunction.sigma 1 (41^1) : ℕ) = 42 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 41)]
    norm_num
  rw [h_2_3, h_13_1, h_41_1]
  norm_num

private lemma sigma_4265 : (ArithmeticFunction.sigma 1 4265 : ℕ) = 5124 := by
  have hfac : 4265 = 5^1 * (853^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 853^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_853_1 : (ArithmeticFunction.sigma 1 (853^1) : ℕ) = 854 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 853)]
    norm_num
  rw [h_5_1, h_853_1]
  norm_num

private lemma sigma_4266 : (ArithmeticFunction.sigma 1 4266 : ℕ) = 9600 := by
  have hfac : 4266 = 2^1 * (3^3 * (79^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^3 * (79^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^3) (n := 79^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_3 : (ArithmeticFunction.sigma 1 (3^3) : ℕ) = 40 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_79_1 : (ArithmeticFunction.sigma 1 (79^1) : ℕ) = 80 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 79)]
    norm_num
  rw [h_2_1, h_3_3, h_79_1]
  norm_num

private lemma sigma_4267 : (ArithmeticFunction.sigma 1 4267 : ℕ) = 4536 := by
  have hfac : 4267 = 17^1 * (251^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 17^1) (n := 251^1) (by norm_num [Nat.gcd])]
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  have h_251_1 : (ArithmeticFunction.sigma 1 (251^1) : ℕ) = 252 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 251)]
    norm_num
  rw [h_17_1, h_251_1]
  norm_num

private lemma sigma_4268 : (ArithmeticFunction.sigma 1 4268 : ℕ) = 8232 := by
  have hfac : 4268 = 2^2 * (11^1 * (97^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 11^1 * (97^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 97^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_97_1 : (ArithmeticFunction.sigma 1 (97^1) : ℕ) = 98 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 97)]
    norm_num
  rw [h_2_2, h_11_1, h_97_1]
  norm_num

private lemma sigma_4269 : (ArithmeticFunction.sigma 1 4269 : ℕ) = 5696 := by
  have hfac : 4269 = 3^1 * (1423^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 1423^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_1423_1 : (ArithmeticFunction.sigma 1 (1423^1) : ℕ) = 1424 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1423)]
    norm_num
  rw [h_3_1, h_1423_1]
  norm_num

private lemma sigma_4270 : (ArithmeticFunction.sigma 1 4270 : ℕ) = 8928 := by
  have hfac : 4270 = 2^1 * (5^1 * (7^1 * (61^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 5^1 * (7^1 * (61^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 7^1 * (61^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 61^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_61_1 : (ArithmeticFunction.sigma 1 (61^1) : ℕ) = 62 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 61)]
    norm_num
  rw [h_2_1, h_5_1, h_7_1, h_61_1]
  norm_num

private lemma sigma_4271 : (ArithmeticFunction.sigma 1 4271 : ℕ) = 4272 := by
  change (ArithmeticFunction.sigma 1 (4271^1) : ℕ) = 4272
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4271)]
  norm_num

private lemma sigma_4272 : (ArithmeticFunction.sigma 1 4272 : ℕ) = 11160 := by
  have hfac : 4272 = 2^4 * (3^1 * (89^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^4) (n := 3^1 * (89^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 89^1) (by norm_num [Nat.gcd])]
  have h_2_4 : (ArithmeticFunction.sigma 1 (2^4) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_89_1 : (ArithmeticFunction.sigma 1 (89^1) : ℕ) = 90 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 89)]
    norm_num
  rw [h_2_4, h_3_1, h_89_1]
  norm_num

private lemma sigma_4273 : (ArithmeticFunction.sigma 1 4273 : ℕ) = 4274 := by
  change (ArithmeticFunction.sigma 1 (4273^1) : ℕ) = 4274
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4273)]
  norm_num

private lemma sigma_4274 : (ArithmeticFunction.sigma 1 4274 : ℕ) = 6414 := by
  have hfac : 4274 = 2^1 * (2137^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2137^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2137_1 : (ArithmeticFunction.sigma 1 (2137^1) : ℕ) = 2138 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2137)]
    norm_num
  rw [h_2_1, h_2137_1]
  norm_num

private lemma sigma_4275 : (ArithmeticFunction.sigma 1 4275 : ℕ) = 8060 := by
  have hfac : 4275 = 3^2 * (5^2 * (19^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 5^2 * (19^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^2) (n := 19^1) (by norm_num [Nat.gcd])]
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_2 : (ArithmeticFunction.sigma 1 (5^2) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  rw [h_3_2, h_5_2, h_19_1]
  norm_num

private lemma sigma_4276 : (ArithmeticFunction.sigma 1 4276 : ℕ) = 7490 := by
  have hfac : 4276 = 2^2 * (1069^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 1069^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_1069_1 : (ArithmeticFunction.sigma 1 (1069^1) : ℕ) = 1070 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1069)]
    norm_num
  rw [h_2_2, h_1069_1]
  norm_num

private lemma sigma_4277 : (ArithmeticFunction.sigma 1 4277 : ℕ) = 5376 := by
  have hfac : 4277 = 7^1 * (13^1 * (47^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 13^1 * (47^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 47^1) (by norm_num [Nat.gcd])]
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_47_1 : (ArithmeticFunction.sigma 1 (47^1) : ℕ) = 48 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 47)]
    norm_num
  rw [h_7_1, h_13_1, h_47_1]
  norm_num

private lemma sigma_4278 : (ArithmeticFunction.sigma 1 4278 : ℕ) = 9216 := by
  have hfac : 4278 = 2^1 * (3^1 * (23^1 * (31^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (23^1 * (31^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 23^1 * (31^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 23^1) (n := 31^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_23_1 : (ArithmeticFunction.sigma 1 (23^1) : ℕ) = 24 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
    norm_num
  have h_31_1 : (ArithmeticFunction.sigma 1 (31^1) : ℕ) = 32 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31)]
    norm_num
  rw [h_2_1, h_3_1, h_23_1, h_31_1]
  norm_num

private lemma sigma_4279 : (ArithmeticFunction.sigma 1 4279 : ℕ) = 4680 := by
  have hfac : 4279 = 11^1 * (389^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 389^1) (by norm_num [Nat.gcd])]
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_389_1 : (ArithmeticFunction.sigma 1 (389^1) : ℕ) = 390 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 389)]
    norm_num
  rw [h_11_1, h_389_1]
  norm_num

private lemma sigma_4280 : (ArithmeticFunction.sigma 1 4280 : ℕ) = 9720 := by
  have hfac : 4280 = 2^3 * (5^1 * (107^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 5^1 * (107^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 107^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_107_1 : (ArithmeticFunction.sigma 1 (107^1) : ℕ) = 108 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 107)]
    norm_num
  rw [h_2_3, h_5_1, h_107_1]
  norm_num

private lemma sigma_4281 : (ArithmeticFunction.sigma 1 4281 : ℕ) = 5712 := by
  have hfac : 4281 = 3^1 * (1427^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 1427^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_1427_1 : (ArithmeticFunction.sigma 1 (1427^1) : ℕ) = 1428 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1427)]
    norm_num
  rw [h_3_1, h_1427_1]
  norm_num

private lemma sigma_4282 : (ArithmeticFunction.sigma 1 4282 : ℕ) = 6426 := by
  have hfac : 4282 = 2^1 * (2141^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2141^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2141_1 : (ArithmeticFunction.sigma 1 (2141^1) : ℕ) = 2142 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2141)]
    norm_num
  rw [h_2_1, h_2141_1]
  norm_num

private lemma sigma_4283 : (ArithmeticFunction.sigma 1 4283 : ℕ) = 4284 := by
  change (ArithmeticFunction.sigma 1 (4283^1) : ℕ) = 4284
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4283)]
  norm_num

private lemma sigma_4284 : (ArithmeticFunction.sigma 1 4284 : ℕ) = 13104 := by
  have hfac : 4284 = 2^2 * (3^2 * (7^1 * (17^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 3^2 * (7^1 * (17^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 7^1 * (17^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 17^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  rw [h_2_2, h_3_2, h_7_1, h_17_1]
  norm_num

private lemma sigma_4285 : (ArithmeticFunction.sigma 1 4285 : ℕ) = 5148 := by
  have hfac : 4285 = 5^1 * (857^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 857^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_857_1 : (ArithmeticFunction.sigma 1 (857^1) : ℕ) = 858 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 857)]
    norm_num
  rw [h_5_1, h_857_1]
  norm_num

private lemma sigma_4286 : (ArithmeticFunction.sigma 1 4286 : ℕ) = 6432 := by
  have hfac : 4286 = 2^1 * (2143^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2143^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2143_1 : (ArithmeticFunction.sigma 1 (2143^1) : ℕ) = 2144 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2143)]
    norm_num
  rw [h_2_1, h_2143_1]
  norm_num

private lemma sigma_4287 : (ArithmeticFunction.sigma 1 4287 : ℕ) = 5720 := by
  have hfac : 4287 = 3^1 * (1429^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 1429^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_1429_1 : (ArithmeticFunction.sigma 1 (1429^1) : ℕ) = 1430 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1429)]
    norm_num
  rw [h_3_1, h_1429_1]
  norm_num

private lemma sigma_4288 : (ArithmeticFunction.sigma 1 4288 : ℕ) = 8636 := by
  have hfac : 4288 = 2^6 * (67^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^6) (n := 67^1) (by norm_num [Nat.gcd])]
  have h_2_6 : (ArithmeticFunction.sigma 1 (2^6) : ℕ) = 127 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_67_1 : (ArithmeticFunction.sigma 1 (67^1) : ℕ) = 68 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 67)]
    norm_num
  rw [h_2_6, h_67_1]
  norm_num

private lemma sigma_4289 : (ArithmeticFunction.sigma 1 4289 : ℕ) = 4290 := by
  change (ArithmeticFunction.sigma 1 (4289^1) : ℕ) = 4290
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4289)]
  norm_num

private lemma sigma_4290 : (ArithmeticFunction.sigma 1 4290 : ℕ) = 12096 := by
  have hfac : 4290 = 2^1 * (3^1 * (5^1 * (11^1 * (13^1)))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (5^1 * (11^1 * (13^1)))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 5^1 * (11^1 * (13^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 11^1 * (13^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 13^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  rw [h_2_1, h_3_1, h_5_1, h_11_1, h_13_1]
  norm_num

private lemma sigma_4291 : (ArithmeticFunction.sigma 1 4291 : ℕ) = 4912 := by
  have hfac : 4291 = 7^1 * (613^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 613^1) (by norm_num [Nat.gcd])]
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_613_1 : (ArithmeticFunction.sigma 1 (613^1) : ℕ) = 614 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 613)]
    norm_num
  rw [h_7_1, h_613_1]
  norm_num

private lemma sigma_4292 : (ArithmeticFunction.sigma 1 4292 : ℕ) = 7980 := by
  have hfac : 4292 = 2^2 * (29^1 * (37^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 29^1 * (37^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 29^1) (n := 37^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_29_1 : (ArithmeticFunction.sigma 1 (29^1) : ℕ) = 30 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 29)]
    norm_num
  have h_37_1 : (ArithmeticFunction.sigma 1 (37^1) : ℕ) = 38 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 37)]
    norm_num
  rw [h_2_2, h_29_1, h_37_1]
  norm_num

private lemma sigma_4293 : (ArithmeticFunction.sigma 1 4293 : ℕ) = 6534 := by
  have hfac : 4293 = 3^4 * (53^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^4) (n := 53^1) (by norm_num [Nat.gcd])]
  have h_3_4 : (ArithmeticFunction.sigma 1 (3^4) : ℕ) = 121 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_53_1 : (ArithmeticFunction.sigma 1 (53^1) : ℕ) = 54 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 53)]
    norm_num
  rw [h_3_4, h_53_1]
  norm_num

private lemma sigma_4294 : (ArithmeticFunction.sigma 1 4294 : ℕ) = 6840 := by
  have hfac : 4294 = 2^1 * (19^1 * (113^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 19^1 * (113^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 19^1) (n := 113^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  have h_113_1 : (ArithmeticFunction.sigma 1 (113^1) : ℕ) = 114 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 113)]
    norm_num
  rw [h_2_1, h_19_1, h_113_1]
  norm_num

private lemma sigma_4295 : (ArithmeticFunction.sigma 1 4295 : ℕ) = 5160 := by
  have hfac : 4295 = 5^1 * (859^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 859^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_859_1 : (ArithmeticFunction.sigma 1 (859^1) : ℕ) = 860 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 859)]
    norm_num
  rw [h_5_1, h_859_1]
  norm_num

private lemma sigma_4296 : (ArithmeticFunction.sigma 1 4296 : ℕ) = 10800 := by
  have hfac : 4296 = 2^3 * (3^1 * (179^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 3^1 * (179^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 179^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_179_1 : (ArithmeticFunction.sigma 1 (179^1) : ℕ) = 180 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 179)]
    norm_num
  rw [h_2_3, h_3_1, h_179_1]
  norm_num

private lemma sigma_4297 : (ArithmeticFunction.sigma 1 4297 : ℕ) = 4298 := by
  change (ArithmeticFunction.sigma 1 (4297^1) : ℕ) = 4298
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4297)]
  norm_num

private lemma sigma_4298 : (ArithmeticFunction.sigma 1 4298 : ℕ) = 7392 := by
  have hfac : 4298 = 2^1 * (7^1 * (307^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 7^1 * (307^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 307^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_307_1 : (ArithmeticFunction.sigma 1 (307^1) : ℕ) = 308 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 307)]
    norm_num
  rw [h_2_1, h_7_1, h_307_1]
  norm_num

private lemma sigma_4299 : (ArithmeticFunction.sigma 1 4299 : ℕ) = 5736 := by
  have hfac : 4299 = 3^1 * (1433^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 1433^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_1433_1 : (ArithmeticFunction.sigma 1 (1433^1) : ℕ) = 1434 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1433)]
    norm_num
  rw [h_3_1, h_1433_1]
  norm_num

private lemma sigma_4300 : (ArithmeticFunction.sigma 1 4300 : ℕ) = 9548 := by
  have hfac : 4300 = 2^2 * (5^2 * (43^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 5^2 * (43^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^2) (n := 43^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_2 : (ArithmeticFunction.sigma 1 (5^2) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_43_1 : (ArithmeticFunction.sigma 1 (43^1) : ℕ) = 44 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 43)]
    norm_num
  rw [h_2_2, h_5_2, h_43_1]
  norm_num

private lemma sigma_4301 : (ArithmeticFunction.sigma 1 4301 : ℕ) = 5184 := by
  have hfac : 4301 = 11^1 * (17^1 * (23^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 17^1 * (23^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 17^1) (n := 23^1) (by norm_num [Nat.gcd])]
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  have h_23_1 : (ArithmeticFunction.sigma 1 (23^1) : ℕ) = 24 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
    norm_num
  rw [h_11_1, h_17_1, h_23_1]
  norm_num

private lemma sigma_4302 : (ArithmeticFunction.sigma 1 4302 : ℕ) = 9360 := by
  have hfac : 4302 = 2^1 * (3^2 * (239^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^2 * (239^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 239^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_239_1 : (ArithmeticFunction.sigma 1 (239^1) : ℕ) = 240 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 239)]
    norm_num
  rw [h_2_1, h_3_2, h_239_1]
  norm_num

private lemma sigma_4303 : (ArithmeticFunction.sigma 1 4303 : ℕ) = 4648 := by
  have hfac : 4303 = 13^1 * (331^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 331^1) (by norm_num [Nat.gcd])]
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_331_1 : (ArithmeticFunction.sigma 1 (331^1) : ℕ) = 332 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 331)]
    norm_num
  rw [h_13_1, h_331_1]
  norm_num

private lemma sigma_4304 : (ArithmeticFunction.sigma 1 4304 : ℕ) = 8370 := by
  have hfac : 4304 = 2^4 * (269^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^4) (n := 269^1) (by norm_num [Nat.gcd])]
  have h_2_4 : (ArithmeticFunction.sigma 1 (2^4) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_269_1 : (ArithmeticFunction.sigma 1 (269^1) : ℕ) = 270 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 269)]
    norm_num
  rw [h_2_4, h_269_1]
  norm_num

private lemma sigma_4305 : (ArithmeticFunction.sigma 1 4305 : ℕ) = 8064 := by
  have hfac : 4305 = 3^1 * (5^1 * (7^1 * (41^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 5^1 * (7^1 * (41^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 7^1 * (41^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 41^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_41_1 : (ArithmeticFunction.sigma 1 (41^1) : ℕ) = 42 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 41)]
    norm_num
  rw [h_3_1, h_5_1, h_7_1, h_41_1]
  norm_num

private lemma sigma_4306 : (ArithmeticFunction.sigma 1 4306 : ℕ) = 6462 := by
  have hfac : 4306 = 2^1 * (2153^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2153^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2153_1 : (ArithmeticFunction.sigma 1 (2153^1) : ℕ) = 2154 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2153)]
    norm_num
  rw [h_2_1, h_2153_1]
  norm_num

private lemma sigma_4307 : (ArithmeticFunction.sigma 1 4307 : ℕ) = 4440 := by
  have hfac : 4307 = 59^1 * (73^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 59^1) (n := 73^1) (by norm_num [Nat.gcd])]
  have h_59_1 : (ArithmeticFunction.sigma 1 (59^1) : ℕ) = 60 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 59)]
    norm_num
  have h_73_1 : (ArithmeticFunction.sigma 1 (73^1) : ℕ) = 74 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 73)]
    norm_num
  rw [h_59_1, h_73_1]
  norm_num

private lemma sigma_4308 : (ArithmeticFunction.sigma 1 4308 : ℕ) = 10080 := by
  have hfac : 4308 = 2^2 * (3^1 * (359^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 3^1 * (359^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 359^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_359_1 : (ArithmeticFunction.sigma 1 (359^1) : ℕ) = 360 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 359)]
    norm_num
  rw [h_2_2, h_3_1, h_359_1]
  norm_num

private lemma sigma_4309 : (ArithmeticFunction.sigma 1 4309 : ℕ) = 4480 := by
  have hfac : 4309 = 31^1 * (139^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 31^1) (n := 139^1) (by norm_num [Nat.gcd])]
  have h_31_1 : (ArithmeticFunction.sigma 1 (31^1) : ℕ) = 32 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31)]
    norm_num
  have h_139_1 : (ArithmeticFunction.sigma 1 (139^1) : ℕ) = 140 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 139)]
    norm_num
  rw [h_31_1, h_139_1]
  norm_num

private lemma sigma_4310 : (ArithmeticFunction.sigma 1 4310 : ℕ) = 7776 := by
  have hfac : 4310 = 2^1 * (5^1 * (431^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 5^1 * (431^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 431^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_431_1 : (ArithmeticFunction.sigma 1 (431^1) : ℕ) = 432 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 431)]
    norm_num
  rw [h_2_1, h_5_1, h_431_1]
  norm_num

private lemma sigma_4311 : (ArithmeticFunction.sigma 1 4311 : ℕ) = 6240 := by
  have hfac : 4311 = 3^2 * (479^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 479^1) (by norm_num [Nat.gcd])]
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_479_1 : (ArithmeticFunction.sigma 1 (479^1) : ℕ) = 480 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 479)]
    norm_num
  rw [h_3_2, h_479_1]
  norm_num

private lemma sigma_4312 : (ArithmeticFunction.sigma 1 4312 : ℕ) = 10260 := by
  have hfac : 4312 = 2^3 * (7^2 * (11^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 7^2 * (11^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^2) (n := 11^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_7_2 : (ArithmeticFunction.sigma 1 (7^2) : ℕ) = 57 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  rw [h_2_3, h_7_2, h_11_1]
  norm_num

private lemma sigma_4313 : (ArithmeticFunction.sigma 1 4313 : ℕ) = 4560 := by
  have hfac : 4313 = 19^1 * (227^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 19^1) (n := 227^1) (by norm_num [Nat.gcd])]
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  have h_227_1 : (ArithmeticFunction.sigma 1 (227^1) : ℕ) = 228 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 227)]
    norm_num
  rw [h_19_1, h_227_1]
  norm_num

private lemma sigma_4314 : (ArithmeticFunction.sigma 1 4314 : ℕ) = 8640 := by
  have hfac : 4314 = 2^1 * (3^1 * (719^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (719^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 719^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_719_1 : (ArithmeticFunction.sigma 1 (719^1) : ℕ) = 720 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 719)]
    norm_num
  rw [h_2_1, h_3_1, h_719_1]
  norm_num

private lemma sigma_4315 : (ArithmeticFunction.sigma 1 4315 : ℕ) = 5184 := by
  have hfac : 4315 = 5^1 * (863^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 863^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_863_1 : (ArithmeticFunction.sigma 1 (863^1) : ℕ) = 864 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 863)]
    norm_num
  rw [h_5_1, h_863_1]
  norm_num

private lemma sigma_4316 : (ArithmeticFunction.sigma 1 4316 : ℕ) = 8232 := by
  have hfac : 4316 = 2^2 * (13^1 * (83^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 13^1 * (83^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 83^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_83_1 : (ArithmeticFunction.sigma 1 (83^1) : ℕ) = 84 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 83)]
    norm_num
  rw [h_2_2, h_13_1, h_83_1]
  norm_num

private lemma sigma_4317 : (ArithmeticFunction.sigma 1 4317 : ℕ) = 5760 := by
  have hfac : 4317 = 3^1 * (1439^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 1439^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_1439_1 : (ArithmeticFunction.sigma 1 (1439^1) : ℕ) = 1440 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1439)]
    norm_num
  rw [h_3_1, h_1439_1]
  norm_num

private lemma sigma_4318 : (ArithmeticFunction.sigma 1 4318 : ℕ) = 6912 := by
  have hfac : 4318 = 2^1 * (17^1 * (127^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 17^1 * (127^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 17^1) (n := 127^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  have h_127_1 : (ArithmeticFunction.sigma 1 (127^1) : ℕ) = 128 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 127)]
    norm_num
  rw [h_2_1, h_17_1, h_127_1]
  norm_num

private lemma sigma_4319 : (ArithmeticFunction.sigma 1 4319 : ℕ) = 4944 := by
  have hfac : 4319 = 7^1 * (617^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 617^1) (by norm_num [Nat.gcd])]
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_617_1 : (ArithmeticFunction.sigma 1 (617^1) : ℕ) = 618 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 617)]
    norm_num
  rw [h_7_1, h_617_1]
  norm_num

private lemma sigma_4320 : (ArithmeticFunction.sigma 1 4320 : ℕ) = 15120 := by
  have hfac : 4320 = 2^5 * (3^3 * (5^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^5) (n := 3^3 * (5^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^3) (n := 5^1) (by norm_num [Nat.gcd])]
  have h_2_5 : (ArithmeticFunction.sigma 1 (2^5) : ℕ) = 63 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_3 : (ArithmeticFunction.sigma 1 (3^3) : ℕ) = 40 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  rw [h_2_5, h_3_3, h_5_1]
  norm_num

private lemma sigma_4321 : (ArithmeticFunction.sigma 1 4321 : ℕ) = 4500 := by
  have hfac : 4321 = 29^1 * (149^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 29^1) (n := 149^1) (by norm_num [Nat.gcd])]
  have h_29_1 : (ArithmeticFunction.sigma 1 (29^1) : ℕ) = 30 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 29)]
    norm_num
  have h_149_1 : (ArithmeticFunction.sigma 1 (149^1) : ℕ) = 150 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 149)]
    norm_num
  rw [h_29_1, h_149_1]
  norm_num

private lemma sigma_4322 : (ArithmeticFunction.sigma 1 4322 : ℕ) = 6486 := by
  have hfac : 4322 = 2^1 * (2161^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2161^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2161_1 : (ArithmeticFunction.sigma 1 (2161^1) : ℕ) = 2162 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2161)]
    norm_num
  rw [h_2_1, h_2161_1]
  norm_num

private lemma sigma_4323 : (ArithmeticFunction.sigma 1 4323 : ℕ) = 6336 := by
  have hfac : 4323 = 3^1 * (11^1 * (131^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 11^1 * (131^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 131^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_131_1 : (ArithmeticFunction.sigma 1 (131^1) : ℕ) = 132 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 131)]
    norm_num
  rw [h_3_1, h_11_1, h_131_1]
  norm_num

private lemma sigma_4324 : (ArithmeticFunction.sigma 1 4324 : ℕ) = 8064 := by
  have hfac : 4324 = 2^2 * (23^1 * (47^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 23^1 * (47^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 23^1) (n := 47^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_23_1 : (ArithmeticFunction.sigma 1 (23^1) : ℕ) = 24 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
    norm_num
  have h_47_1 : (ArithmeticFunction.sigma 1 (47^1) : ℕ) = 48 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 47)]
    norm_num
  rw [h_2_2, h_23_1, h_47_1]
  norm_num

private lemma sigma_4325 : (ArithmeticFunction.sigma 1 4325 : ℕ) = 5394 := by
  have hfac : 4325 = 5^2 * (173^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^2) (n := 173^1) (by norm_num [Nat.gcd])]
  have h_5_2 : (ArithmeticFunction.sigma 1 (5^2) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_173_1 : (ArithmeticFunction.sigma 1 (173^1) : ℕ) = 174 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 173)]
    norm_num
  rw [h_5_2, h_173_1]
  norm_num

private lemma sigma_4326 : (ArithmeticFunction.sigma 1 4326 : ℕ) = 9984 := by
  have hfac : 4326 = 2^1 * (3^1 * (7^1 * (103^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (7^1 * (103^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 7^1 * (103^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 103^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_103_1 : (ArithmeticFunction.sigma 1 (103^1) : ℕ) = 104 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 103)]
    norm_num
  rw [h_2_1, h_3_1, h_7_1, h_103_1]
  norm_num

private lemma sigma_4327 : (ArithmeticFunction.sigma 1 4327 : ℕ) = 4328 := by
  change (ArithmeticFunction.sigma 1 (4327^1) : ℕ) = 4328
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4327)]
  norm_num

private lemma sigma_4328 : (ArithmeticFunction.sigma 1 4328 : ℕ) = 8130 := by
  have hfac : 4328 = 2^3 * (541^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 541^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_541_1 : (ArithmeticFunction.sigma 1 (541^1) : ℕ) = 542 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 541)]
    norm_num
  rw [h_2_3, h_541_1]
  norm_num

private lemma sigma_4329 : (ArithmeticFunction.sigma 1 4329 : ℕ) = 6916 := by
  have hfac : 4329 = 3^2 * (13^1 * (37^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 13^1 * (37^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 37^1) (by norm_num [Nat.gcd])]
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_37_1 : (ArithmeticFunction.sigma 1 (37^1) : ℕ) = 38 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 37)]
    norm_num
  rw [h_3_2, h_13_1, h_37_1]
  norm_num

private lemma sigma_4330 : (ArithmeticFunction.sigma 1 4330 : ℕ) = 7812 := by
  have hfac : 4330 = 2^1 * (5^1 * (433^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 5^1 * (433^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 433^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_433_1 : (ArithmeticFunction.sigma 1 (433^1) : ℕ) = 434 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 433)]
    norm_num
  rw [h_2_1, h_5_1, h_433_1]
  norm_num

private lemma sigma_4331 : (ArithmeticFunction.sigma 1 4331 : ℕ) = 4464 := by
  have hfac : 4331 = 61^1 * (71^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 61^1) (n := 71^1) (by norm_num [Nat.gcd])]
  have h_61_1 : (ArithmeticFunction.sigma 1 (61^1) : ℕ) = 62 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 61)]
    norm_num
  have h_71_1 : (ArithmeticFunction.sigma 1 (71^1) : ℕ) = 72 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 71)]
    norm_num
  rw [h_61_1, h_71_1]
  norm_num

private lemma sigma_4332 : (ArithmeticFunction.sigma 1 4332 : ℕ) = 10668 := by
  have hfac : 4332 = 2^2 * (3^1 * (19^2)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 3^1 * (19^2)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 19^2) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_19_2 : (ArithmeticFunction.sigma 1 (19^2) : ℕ) = 381 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  rw [h_2_2, h_3_1, h_19_2]
  norm_num

private lemma sigma_4333 : (ArithmeticFunction.sigma 1 4333 : ℕ) = 4960 := by
  have hfac : 4333 = 7^1 * (619^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 619^1) (by norm_num [Nat.gcd])]
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_619_1 : (ArithmeticFunction.sigma 1 (619^1) : ℕ) = 620 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 619)]
    norm_num
  rw [h_7_1, h_619_1]
  norm_num

private lemma sigma_4334 : (ArithmeticFunction.sigma 1 4334 : ℕ) = 7128 := by
  have hfac : 4334 = 2^1 * (11^1 * (197^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 11^1 * (197^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 197^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_197_1 : (ArithmeticFunction.sigma 1 (197^1) : ℕ) = 198 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 197)]
    norm_num
  rw [h_2_1, h_11_1, h_197_1]
  norm_num

private lemma sigma_4335 : (ArithmeticFunction.sigma 1 4335 : ℕ) = 7368 := by
  have hfac : 4335 = 3^1 * (5^1 * (17^2)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 5^1 * (17^2)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 17^2) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_17_2 : (ArithmeticFunction.sigma 1 (17^2) : ℕ) = 307 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  rw [h_3_1, h_5_1, h_17_2]
  norm_num

private lemma sigma_4336 : (ArithmeticFunction.sigma 1 4336 : ℕ) = 8432 := by
  have hfac : 4336 = 2^4 * (271^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^4) (n := 271^1) (by norm_num [Nat.gcd])]
  have h_2_4 : (ArithmeticFunction.sigma 1 (2^4) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_271_1 : (ArithmeticFunction.sigma 1 (271^1) : ℕ) = 272 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 271)]
    norm_num
  rw [h_2_4, h_271_1]
  norm_num

private lemma sigma_4337 : (ArithmeticFunction.sigma 1 4337 : ℕ) = 4338 := by
  change (ArithmeticFunction.sigma 1 (4337^1) : ℕ) = 4338
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4337)]
  norm_num

private lemma sigma_4338 : (ArithmeticFunction.sigma 1 4338 : ℕ) = 9438 := by
  have hfac : 4338 = 2^1 * (3^2 * (241^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^2 * (241^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 241^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_241_1 : (ArithmeticFunction.sigma 1 (241^1) : ℕ) = 242 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 241)]
    norm_num
  rw [h_2_1, h_3_2, h_241_1]
  norm_num

private lemma sigma_4339 : (ArithmeticFunction.sigma 1 4339 : ℕ) = 4340 := by
  change (ArithmeticFunction.sigma 1 (4339^1) : ℕ) = 4340
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4339)]
  norm_num

private lemma sigma_4340 : (ArithmeticFunction.sigma 1 4340 : ℕ) = 10752 := by
  have hfac : 4340 = 2^2 * (5^1 * (7^1 * (31^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 5^1 * (7^1 * (31^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 7^1 * (31^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 31^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_31_1 : (ArithmeticFunction.sigma 1 (31^1) : ℕ) = 32 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31)]
    norm_num
  rw [h_2_2, h_5_1, h_7_1, h_31_1]
  norm_num

private lemma sigma_4341 : (ArithmeticFunction.sigma 1 4341 : ℕ) = 5792 := by
  have hfac : 4341 = 3^1 * (1447^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 1447^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_1447_1 : (ArithmeticFunction.sigma 1 (1447^1) : ℕ) = 1448 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1447)]
    norm_num
  rw [h_3_1, h_1447_1]
  norm_num

private lemma sigma_4342 : (ArithmeticFunction.sigma 1 4342 : ℕ) = 7056 := by
  have hfac : 4342 = 2^1 * (13^1 * (167^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 13^1 * (167^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 167^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_167_1 : (ArithmeticFunction.sigma 1 (167^1) : ℕ) = 168 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 167)]
    norm_num
  rw [h_2_1, h_13_1, h_167_1]
  norm_num

private lemma sigma_4343 : (ArithmeticFunction.sigma 1 4343 : ℕ) = 4488 := by
  have hfac : 4343 = 43^1 * (101^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 43^1) (n := 101^1) (by norm_num [Nat.gcd])]
  have h_43_1 : (ArithmeticFunction.sigma 1 (43^1) : ℕ) = 44 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 43)]
    norm_num
  have h_101_1 : (ArithmeticFunction.sigma 1 (101^1) : ℕ) = 102 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 101)]
    norm_num
  rw [h_43_1, h_101_1]
  norm_num

private lemma sigma_4344 : (ArithmeticFunction.sigma 1 4344 : ℕ) = 10920 := by
  have hfac : 4344 = 2^3 * (3^1 * (181^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 3^1 * (181^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 181^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_181_1 : (ArithmeticFunction.sigma 1 (181^1) : ℕ) = 182 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 181)]
    norm_num
  rw [h_2_3, h_3_1, h_181_1]
  norm_num

private lemma sigma_4345 : (ArithmeticFunction.sigma 1 4345 : ℕ) = 5760 := by
  have hfac : 4345 = 5^1 * (11^1 * (79^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 11^1 * (79^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 79^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_79_1 : (ArithmeticFunction.sigma 1 (79^1) : ℕ) = 80 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 79)]
    norm_num
  rw [h_5_1, h_11_1, h_79_1]
  norm_num

private lemma sigma_4346 : (ArithmeticFunction.sigma 1 4346 : ℕ) = 6804 := by
  have hfac : 4346 = 2^1 * (41^1 * (53^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 41^1 * (53^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 41^1) (n := 53^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_41_1 : (ArithmeticFunction.sigma 1 (41^1) : ℕ) = 42 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 41)]
    norm_num
  have h_53_1 : (ArithmeticFunction.sigma 1 (53^1) : ℕ) = 54 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 53)]
    norm_num
  rw [h_2_1, h_41_1, h_53_1]
  norm_num

private lemma sigma_4347 : (ArithmeticFunction.sigma 1 4347 : ℕ) = 7680 := by
  have hfac : 4347 = 3^3 * (7^1 * (23^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^3) (n := 7^1 * (23^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 23^1) (by norm_num [Nat.gcd])]
  have h_3_3 : (ArithmeticFunction.sigma 1 (3^3) : ℕ) = 40 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_23_1 : (ArithmeticFunction.sigma 1 (23^1) : ℕ) = 24 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
    norm_num
  rw [h_3_3, h_7_1, h_23_1]
  norm_num

private lemma sigma_4348 : (ArithmeticFunction.sigma 1 4348 : ℕ) = 7616 := by
  have hfac : 4348 = 2^2 * (1087^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 1087^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_1087_1 : (ArithmeticFunction.sigma 1 (1087^1) : ℕ) = 1088 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1087)]
    norm_num
  rw [h_2_2, h_1087_1]
  norm_num

private lemma sigma_4349 : (ArithmeticFunction.sigma 1 4349 : ℕ) = 4350 := by
  change (ArithmeticFunction.sigma 1 (4349^1) : ℕ) = 4350
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4349)]
  norm_num

private lemma sigma_4350 : (ArithmeticFunction.sigma 1 4350 : ℕ) = 11160 := by
  have hfac : 4350 = 2^1 * (3^1 * (5^2 * (29^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (5^2 * (29^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 5^2 * (29^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^2) (n := 29^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_2 : (ArithmeticFunction.sigma 1 (5^2) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_29_1 : (ArithmeticFunction.sigma 1 (29^1) : ℕ) = 30 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 29)]
    norm_num
  rw [h_2_1, h_3_1, h_5_2, h_29_1]
  norm_num

private lemma sigma_4351 : (ArithmeticFunction.sigma 1 4351 : ℕ) = 4600 := by
  have hfac : 4351 = 19^1 * (229^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 19^1) (n := 229^1) (by norm_num [Nat.gcd])]
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  have h_229_1 : (ArithmeticFunction.sigma 1 (229^1) : ℕ) = 230 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 229)]
    norm_num
  rw [h_19_1, h_229_1]
  norm_num

private lemma sigma_4352 : (ArithmeticFunction.sigma 1 4352 : ℕ) = 9198 := by
  have hfac : 4352 = 2^8 * (17^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^8) (n := 17^1) (by norm_num [Nat.gcd])]
  have h_2_8 : (ArithmeticFunction.sigma 1 (2^8) : ℕ) = 511 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  rw [h_2_8, h_17_1]
  norm_num

private lemma sigma_4353 : (ArithmeticFunction.sigma 1 4353 : ℕ) = 5808 := by
  have hfac : 4353 = 3^1 * (1451^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 1451^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_1451_1 : (ArithmeticFunction.sigma 1 (1451^1) : ℕ) = 1452 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1451)]
    norm_num
  rw [h_3_1, h_1451_1]
  norm_num

private lemma sigma_4354 : (ArithmeticFunction.sigma 1 4354 : ℕ) = 7488 := by
  have hfac : 4354 = 2^1 * (7^1 * (311^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 7^1 * (311^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 311^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_311_1 : (ArithmeticFunction.sigma 1 (311^1) : ℕ) = 312 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 311)]
    norm_num
  rw [h_2_1, h_7_1, h_311_1]
  norm_num

private lemma sigma_4355 : (ArithmeticFunction.sigma 1 4355 : ℕ) = 5712 := by
  have hfac : 4355 = 5^1 * (13^1 * (67^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 13^1 * (67^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 67^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_67_1 : (ArithmeticFunction.sigma 1 (67^1) : ℕ) = 68 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 67)]
    norm_num
  rw [h_5_1, h_13_1, h_67_1]
  norm_num

private lemma sigma_4356 : (ArithmeticFunction.sigma 1 4356 : ℕ) = 12103 := by
  have hfac : 4356 = 2^2 * (3^2 * (11^2)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 3^2 * (11^2)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 11^2) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_11_2 : (ArithmeticFunction.sigma 1 (11^2) : ℕ) = 133 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  rw [h_2_2, h_3_2, h_11_2]
  norm_num

private lemma sigma_4357 : (ArithmeticFunction.sigma 1 4357 : ℕ) = 4358 := by
  change (ArithmeticFunction.sigma 1 (4357^1) : ℕ) = 4358
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4357)]
  norm_num

private lemma sigma_4358 : (ArithmeticFunction.sigma 1 4358 : ℕ) = 6540 := by
  have hfac : 4358 = 2^1 * (2179^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2179^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2179_1 : (ArithmeticFunction.sigma 1 (2179^1) : ℕ) = 2180 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2179)]
    norm_num
  rw [h_2_1, h_2179_1]
  norm_num

private lemma sigma_4359 : (ArithmeticFunction.sigma 1 4359 : ℕ) = 5816 := by
  have hfac : 4359 = 3^1 * (1453^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 1453^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_1453_1 : (ArithmeticFunction.sigma 1 (1453^1) : ℕ) = 1454 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1453)]
    norm_num
  rw [h_3_1, h_1453_1]
  norm_num

private lemma sigma_4360 : (ArithmeticFunction.sigma 1 4360 : ℕ) = 9900 := by
  have hfac : 4360 = 2^3 * (5^1 * (109^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 5^1 * (109^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 109^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_109_1 : (ArithmeticFunction.sigma 1 (109^1) : ℕ) = 110 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 109)]
    norm_num
  rw [h_2_3, h_5_1, h_109_1]
  norm_num

private lemma sigma_4361 : (ArithmeticFunction.sigma 1 4361 : ℕ) = 5130 := by
  have hfac : 4361 = 7^2 * (89^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^2) (n := 89^1) (by norm_num [Nat.gcd])]
  have h_7_2 : (ArithmeticFunction.sigma 1 (7^2) : ℕ) = 57 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_89_1 : (ArithmeticFunction.sigma 1 (89^1) : ℕ) = 90 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 89)]
    norm_num
  rw [h_7_2, h_89_1]
  norm_num

private lemma sigma_4362 : (ArithmeticFunction.sigma 1 4362 : ℕ) = 8736 := by
  have hfac : 4362 = 2^1 * (3^1 * (727^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (727^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 727^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_727_1 : (ArithmeticFunction.sigma 1 (727^1) : ℕ) = 728 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 727)]
    norm_num
  rw [h_2_1, h_3_1, h_727_1]
  norm_num

private lemma sigma_4363 : (ArithmeticFunction.sigma 1 4363 : ℕ) = 4364 := by
  change (ArithmeticFunction.sigma 1 (4363^1) : ℕ) = 4364
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4363)]
  norm_num

private lemma sigma_4364 : (ArithmeticFunction.sigma 1 4364 : ℕ) = 7644 := by
  have hfac : 4364 = 2^2 * (1091^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 1091^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_1091_1 : (ArithmeticFunction.sigma 1 (1091^1) : ℕ) = 1092 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1091)]
    norm_num
  rw [h_2_2, h_1091_1]
  norm_num

private lemma sigma_4365 : (ArithmeticFunction.sigma 1 4365 : ℕ) = 7644 := by
  have hfac : 4365 = 3^2 * (5^1 * (97^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 5^1 * (97^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 97^1) (by norm_num [Nat.gcd])]
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_97_1 : (ArithmeticFunction.sigma 1 (97^1) : ℕ) = 98 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 97)]
    norm_num
  rw [h_3_2, h_5_1, h_97_1]
  norm_num

private lemma sigma_4366 : (ArithmeticFunction.sigma 1 4366 : ℕ) = 6840 := by
  have hfac : 4366 = 2^1 * (37^1 * (59^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 37^1 * (59^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 37^1) (n := 59^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_37_1 : (ArithmeticFunction.sigma 1 (37^1) : ℕ) = 38 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 37)]
    norm_num
  have h_59_1 : (ArithmeticFunction.sigma 1 (59^1) : ℕ) = 60 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 59)]
    norm_num
  rw [h_2_1, h_37_1, h_59_1]
  norm_num

private lemma sigma_4367 : (ArithmeticFunction.sigma 1 4367 : ℕ) = 4776 := by
  have hfac : 4367 = 11^1 * (397^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 397^1) (by norm_num [Nat.gcd])]
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_397_1 : (ArithmeticFunction.sigma 1 (397^1) : ℕ) = 398 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 397)]
    norm_num
  rw [h_11_1, h_397_1]
  norm_num

private lemma sigma_4368 : (ArithmeticFunction.sigma 1 4368 : ℕ) = 13888 := by
  have hfac : 4368 = 2^4 * (3^1 * (7^1 * (13^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^4) (n := 3^1 * (7^1 * (13^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 7^1 * (13^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 13^1) (by norm_num [Nat.gcd])]
  have h_2_4 : (ArithmeticFunction.sigma 1 (2^4) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  rw [h_2_4, h_3_1, h_7_1, h_13_1]
  norm_num

private lemma sigma_4369 : (ArithmeticFunction.sigma 1 4369 : ℕ) = 4644 := by
  have hfac : 4369 = 17^1 * (257^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 17^1) (n := 257^1) (by norm_num [Nat.gcd])]
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  have h_257_1 : (ArithmeticFunction.sigma 1 (257^1) : ℕ) = 258 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 257)]
    norm_num
  rw [h_17_1, h_257_1]
  norm_num

private lemma sigma_4370 : (ArithmeticFunction.sigma 1 4370 : ℕ) = 8640 := by
  have hfac : 4370 = 2^1 * (5^1 * (19^1 * (23^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 5^1 * (19^1 * (23^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 19^1 * (23^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 19^1) (n := 23^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  have h_23_1 : (ArithmeticFunction.sigma 1 (23^1) : ℕ) = 24 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
    norm_num
  rw [h_2_1, h_5_1, h_19_1, h_23_1]
  norm_num

private lemma sigma_4371 : (ArithmeticFunction.sigma 1 4371 : ℕ) = 6144 := by
  have hfac : 4371 = 3^1 * (31^1 * (47^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 31^1 * (47^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 31^1) (n := 47^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_31_1 : (ArithmeticFunction.sigma 1 (31^1) : ℕ) = 32 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31)]
    norm_num
  have h_47_1 : (ArithmeticFunction.sigma 1 (47^1) : ℕ) = 48 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 47)]
    norm_num
  rw [h_3_1, h_31_1, h_47_1]
  norm_num

private lemma sigma_4372 : (ArithmeticFunction.sigma 1 4372 : ℕ) = 7658 := by
  have hfac : 4372 = 2^2 * (1093^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 1093^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_1093_1 : (ArithmeticFunction.sigma 1 (1093^1) : ℕ) = 1094 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1093)]
    norm_num
  rw [h_2_2, h_1093_1]
  norm_num

private lemma sigma_4373 : (ArithmeticFunction.sigma 1 4373 : ℕ) = 4374 := by
  change (ArithmeticFunction.sigma 1 (4373^1) : ℕ) = 4374
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4373)]
  norm_num

private lemma sigma_4374 : (ArithmeticFunction.sigma 1 4374 : ℕ) = 9840 := by
  have hfac : 4374 = 2^1 * (3^7) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^7) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_7 : (ArithmeticFunction.sigma 1 (3^7) : ℕ) = 3280 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  rw [h_2_1, h_3_7]
  norm_num

private lemma sigma_4375 : (ArithmeticFunction.sigma 1 4375 : ℕ) = 6248 := by
  have hfac : 4375 = 5^4 * (7^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^4) (n := 7^1) (by norm_num [Nat.gcd])]
  have h_5_4 : (ArithmeticFunction.sigma 1 (5^4) : ℕ) = 781 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  rw [h_5_4, h_7_1]
  norm_num

private lemma sigma_4376 : (ArithmeticFunction.sigma 1 4376 : ℕ) = 8220 := by
  have hfac : 4376 = 2^3 * (547^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 547^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_547_1 : (ArithmeticFunction.sigma 1 (547^1) : ℕ) = 548 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 547)]
    norm_num
  rw [h_2_3, h_547_1]
  norm_num

private lemma sigma_4377 : (ArithmeticFunction.sigma 1 4377 : ℕ) = 5840 := by
  have hfac : 4377 = 3^1 * (1459^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 1459^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_1459_1 : (ArithmeticFunction.sigma 1 (1459^1) : ℕ) = 1460 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1459)]
    norm_num
  rw [h_3_1, h_1459_1]
  norm_num

private lemma sigma_4378 : (ArithmeticFunction.sigma 1 4378 : ℕ) = 7200 := by
  have hfac : 4378 = 2^1 * (11^1 * (199^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 11^1 * (199^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 199^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_199_1 : (ArithmeticFunction.sigma 1 (199^1) : ℕ) = 200 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 199)]
    norm_num
  rw [h_2_1, h_11_1, h_199_1]
  norm_num

private lemma sigma_4379 : (ArithmeticFunction.sigma 1 4379 : ℕ) = 4560 := by
  have hfac : 4379 = 29^1 * (151^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 29^1) (n := 151^1) (by norm_num [Nat.gcd])]
  have h_29_1 : (ArithmeticFunction.sigma 1 (29^1) : ℕ) = 30 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 29)]
    norm_num
  have h_151_1 : (ArithmeticFunction.sigma 1 (151^1) : ℕ) = 152 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 151)]
    norm_num
  rw [h_29_1, h_151_1]
  norm_num

private lemma sigma_4380 : (ArithmeticFunction.sigma 1 4380 : ℕ) = 12432 := by
  have hfac : 4380 = 2^2 * (3^1 * (5^1 * (73^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 3^1 * (5^1 * (73^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 5^1 * (73^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 73^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_73_1 : (ArithmeticFunction.sigma 1 (73^1) : ℕ) = 74 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 73)]
    norm_num
  rw [h_2_2, h_3_1, h_5_1, h_73_1]
  norm_num

private lemma sigma_4381 : (ArithmeticFunction.sigma 1 4381 : ℕ) = 4732 := by
  have hfac : 4381 = 13^1 * (337^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 337^1) (by norm_num [Nat.gcd])]
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_337_1 : (ArithmeticFunction.sigma 1 (337^1) : ℕ) = 338 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 337)]
    norm_num
  rw [h_13_1, h_337_1]
  norm_num

private lemma sigma_4382 : (ArithmeticFunction.sigma 1 4382 : ℕ) = 7536 := by
  have hfac : 4382 = 2^1 * (7^1 * (313^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 7^1 * (313^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 313^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_313_1 : (ArithmeticFunction.sigma 1 (313^1) : ℕ) = 314 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 313)]
    norm_num
  rw [h_2_1, h_7_1, h_313_1]
  norm_num

private lemma sigma_4383 : (ArithmeticFunction.sigma 1 4383 : ℕ) = 6344 := by
  have hfac : 4383 = 3^2 * (487^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 487^1) (by norm_num [Nat.gcd])]
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_487_1 : (ArithmeticFunction.sigma 1 (487^1) : ℕ) = 488 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 487)]
    norm_num
  rw [h_3_2, h_487_1]
  norm_num

private lemma sigma_4384 : (ArithmeticFunction.sigma 1 4384 : ℕ) = 8694 := by
  have hfac : 4384 = 2^5 * (137^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^5) (n := 137^1) (by norm_num [Nat.gcd])]
  have h_2_5 : (ArithmeticFunction.sigma 1 (2^5) : ℕ) = 63 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_137_1 : (ArithmeticFunction.sigma 1 (137^1) : ℕ) = 138 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 137)]
    norm_num
  rw [h_2_5, h_137_1]
  norm_num

private lemma sigma_4385 : (ArithmeticFunction.sigma 1 4385 : ℕ) = 5268 := by
  have hfac : 4385 = 5^1 * (877^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 877^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_877_1 : (ArithmeticFunction.sigma 1 (877^1) : ℕ) = 878 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 877)]
    norm_num
  rw [h_5_1, h_877_1]
  norm_num

private lemma sigma_4386 : (ArithmeticFunction.sigma 1 4386 : ℕ) = 9504 := by
  have hfac : 4386 = 2^1 * (3^1 * (17^1 * (43^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (17^1 * (43^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 17^1 * (43^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 17^1) (n := 43^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  have h_43_1 : (ArithmeticFunction.sigma 1 (43^1) : ℕ) = 44 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 43)]
    norm_num
  rw [h_2_1, h_3_1, h_17_1, h_43_1]
  norm_num

private lemma sigma_4387 : (ArithmeticFunction.sigma 1 4387 : ℕ) = 4536 := by
  have hfac : 4387 = 41^1 * (107^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 41^1) (n := 107^1) (by norm_num [Nat.gcd])]
  have h_41_1 : (ArithmeticFunction.sigma 1 (41^1) : ℕ) = 42 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 41)]
    norm_num
  have h_107_1 : (ArithmeticFunction.sigma 1 (107^1) : ℕ) = 108 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 107)]
    norm_num
  rw [h_41_1, h_107_1]
  norm_num

private lemma sigma_4388 : (ArithmeticFunction.sigma 1 4388 : ℕ) = 7686 := by
  have hfac : 4388 = 2^2 * (1097^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 1097^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_1097_1 : (ArithmeticFunction.sigma 1 (1097^1) : ℕ) = 1098 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1097)]
    norm_num
  rw [h_2_2, h_1097_1]
  norm_num

private lemma sigma_4389 : (ArithmeticFunction.sigma 1 4389 : ℕ) = 7680 := by
  have hfac : 4389 = 3^1 * (7^1 * (11^1 * (19^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 7^1 * (11^1 * (19^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 11^1 * (19^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 19^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  rw [h_3_1, h_7_1, h_11_1, h_19_1]
  norm_num

private lemma sigma_4390 : (ArithmeticFunction.sigma 1 4390 : ℕ) = 7920 := by
  have hfac : 4390 = 2^1 * (5^1 * (439^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 5^1 * (439^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 439^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_439_1 : (ArithmeticFunction.sigma 1 (439^1) : ℕ) = 440 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 439)]
    norm_num
  rw [h_2_1, h_5_1, h_439_1]
  norm_num

private lemma sigma_4391 : (ArithmeticFunction.sigma 1 4391 : ℕ) = 4392 := by
  change (ArithmeticFunction.sigma 1 (4391^1) : ℕ) = 4392
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4391)]
  norm_num

private lemma sigma_4392 : (ArithmeticFunction.sigma 1 4392 : ℕ) = 12090 := by
  have hfac : 4392 = 2^3 * (3^2 * (61^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 3^2 * (61^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 61^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_61_1 : (ArithmeticFunction.sigma 1 (61^1) : ℕ) = 62 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 61)]
    norm_num
  rw [h_2_3, h_3_2, h_61_1]
  norm_num

private lemma sigma_4393 : (ArithmeticFunction.sigma 1 4393 : ℕ) = 4608 := by
  have hfac : 4393 = 23^1 * (191^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 23^1) (n := 191^1) (by norm_num [Nat.gcd])]
  have h_23_1 : (ArithmeticFunction.sigma 1 (23^1) : ℕ) = 24 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
    norm_num
  have h_191_1 : (ArithmeticFunction.sigma 1 (191^1) : ℕ) = 192 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 191)]
    norm_num
  rw [h_23_1, h_191_1]
  norm_num

private lemma sigma_4394 : (ArithmeticFunction.sigma 1 4394 : ℕ) = 7140 := by
  have hfac : 4394 = 2^1 * (13^3) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 13^3) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_13_3 : (ArithmeticFunction.sigma 1 (13^3) : ℕ) = 2380 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  rw [h_2_1, h_13_3]
  norm_num

private lemma sigma_4395 : (ArithmeticFunction.sigma 1 4395 : ℕ) = 7056 := by
  have hfac : 4395 = 3^1 * (5^1 * (293^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 5^1 * (293^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 293^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_293_1 : (ArithmeticFunction.sigma 1 (293^1) : ℕ) = 294 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 293)]
    norm_num
  rw [h_3_1, h_5_1, h_293_1]
  norm_num

private lemma sigma_4396 : (ArithmeticFunction.sigma 1 4396 : ℕ) = 8848 := by
  have hfac : 4396 = 2^2 * (7^1 * (157^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 7^1 * (157^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 157^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_157_1 : (ArithmeticFunction.sigma 1 (157^1) : ℕ) = 158 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 157)]
    norm_num
  rw [h_2_2, h_7_1, h_157_1]
  norm_num

private lemma sigma_4397 : (ArithmeticFunction.sigma 1 4397 : ℕ) = 4398 := by
  change (ArithmeticFunction.sigma 1 (4397^1) : ℕ) = 4398
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4397)]
  norm_num

private lemma sigma_4398 : (ArithmeticFunction.sigma 1 4398 : ℕ) = 8808 := by
  have hfac : 4398 = 2^1 * (3^1 * (733^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (733^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 733^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_733_1 : (ArithmeticFunction.sigma 1 (733^1) : ℕ) = 734 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 733)]
    norm_num
  rw [h_2_1, h_3_1, h_733_1]
  norm_num

private lemma sigma_4399 : (ArithmeticFunction.sigma 1 4399 : ℕ) = 4536 := by
  have hfac : 4399 = 53^1 * (83^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 53^1) (n := 83^1) (by norm_num [Nat.gcd])]
  have h_53_1 : (ArithmeticFunction.sigma 1 (53^1) : ℕ) = 54 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 53)]
    norm_num
  have h_83_1 : (ArithmeticFunction.sigma 1 (83^1) : ℕ) = 84 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 83)]
    norm_num
  rw [h_53_1, h_83_1]
  norm_num

private lemma sigma_4400 : (ArithmeticFunction.sigma 1 4400 : ℕ) = 11532 := by
  have hfac : 4400 = 2^4 * (5^2 * (11^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^4) (n := 5^2 * (11^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^2) (n := 11^1) (by norm_num [Nat.gcd])]
  have h_2_4 : (ArithmeticFunction.sigma 1 (2^4) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_2 : (ArithmeticFunction.sigma 1 (5^2) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  rw [h_2_4, h_5_2, h_11_1]
  norm_num

private lemma sigma_4401 : (ArithmeticFunction.sigma 1 4401 : ℕ) = 6560 := by
  have hfac : 4401 = 3^3 * (163^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^3) (n := 163^1) (by norm_num [Nat.gcd])]
  have h_3_3 : (ArithmeticFunction.sigma 1 (3^3) : ℕ) = 40 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_163_1 : (ArithmeticFunction.sigma 1 (163^1) : ℕ) = 164 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 163)]
    norm_num
  rw [h_3_3, h_163_1]
  norm_num

private lemma sigma_4402 : (ArithmeticFunction.sigma 1 4402 : ℕ) = 6912 := by
  have hfac : 4402 = 2^1 * (31^1 * (71^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 31^1 * (71^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 31^1) (n := 71^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_31_1 : (ArithmeticFunction.sigma 1 (31^1) : ℕ) = 32 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31)]
    norm_num
  have h_71_1 : (ArithmeticFunction.sigma 1 (71^1) : ℕ) = 72 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 71)]
    norm_num
  rw [h_2_1, h_31_1, h_71_1]
  norm_num

private lemma sigma_4403 : (ArithmeticFunction.sigma 1 4403 : ℕ) = 5472 := by
  have hfac : 4403 = 7^1 * (17^1 * (37^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 17^1 * (37^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 17^1) (n := 37^1) (by norm_num [Nat.gcd])]
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  have h_37_1 : (ArithmeticFunction.sigma 1 (37^1) : ℕ) = 38 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 37)]
    norm_num
  rw [h_7_1, h_17_1, h_37_1]
  norm_num

private lemma sigma_4404 : (ArithmeticFunction.sigma 1 4404 : ℕ) = 10304 := by
  have hfac : 4404 = 2^2 * (3^1 * (367^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 3^1 * (367^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 367^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_367_1 : (ArithmeticFunction.sigma 1 (367^1) : ℕ) = 368 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 367)]
    norm_num
  rw [h_2_2, h_3_1, h_367_1]
  norm_num

private lemma sigma_4405 : (ArithmeticFunction.sigma 1 4405 : ℕ) = 5292 := by
  have hfac : 4405 = 5^1 * (881^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 881^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_881_1 : (ArithmeticFunction.sigma 1 (881^1) : ℕ) = 882 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 881)]
    norm_num
  rw [h_5_1, h_881_1]
  norm_num

private lemma sigma_4406 : (ArithmeticFunction.sigma 1 4406 : ℕ) = 6612 := by
  have hfac : 4406 = 2^1 * (2203^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2203^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2203_1 : (ArithmeticFunction.sigma 1 (2203^1) : ℕ) = 2204 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2203)]
    norm_num
  rw [h_2_1, h_2203_1]
  norm_num

private lemma sigma_4407 : (ArithmeticFunction.sigma 1 4407 : ℕ) = 6384 := by
  have hfac : 4407 = 3^1 * (13^1 * (113^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 13^1 * (113^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 113^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_113_1 : (ArithmeticFunction.sigma 1 (113^1) : ℕ) = 114 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 113)]
    norm_num
  rw [h_3_1, h_13_1, h_113_1]
  norm_num

private lemma sigma_4408 : (ArithmeticFunction.sigma 1 4408 : ℕ) = 9000 := by
  have hfac : 4408 = 2^3 * (19^1 * (29^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 19^1 * (29^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 19^1) (n := 29^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  have h_29_1 : (ArithmeticFunction.sigma 1 (29^1) : ℕ) = 30 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 29)]
    norm_num
  rw [h_2_3, h_19_1, h_29_1]
  norm_num

private lemma sigma_4409 : (ArithmeticFunction.sigma 1 4409 : ℕ) = 4410 := by
  change (ArithmeticFunction.sigma 1 (4409^1) : ℕ) = 4410
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4409)]
  norm_num

private lemma sigma_4410 : (ArithmeticFunction.sigma 1 4410 : ℕ) = 13338 := by
  have hfac : 4410 = 2^1 * (3^2 * (5^1 * (7^2))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^2 * (5^1 * (7^2))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 5^1 * (7^2)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 7^2) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_7_2 : (ArithmeticFunction.sigma 1 (7^2) : ℕ) = 57 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  rw [h_2_1, h_3_2, h_5_1, h_7_2]
  norm_num

private lemma sigma_4411 : (ArithmeticFunction.sigma 1 4411 : ℕ) = 4824 := by
  have hfac : 4411 = 11^1 * (401^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 401^1) (by norm_num [Nat.gcd])]
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_401_1 : (ArithmeticFunction.sigma 1 (401^1) : ℕ) = 402 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 401)]
    norm_num
  rw [h_11_1, h_401_1]
  norm_num

private lemma sigma_4412 : (ArithmeticFunction.sigma 1 4412 : ℕ) = 7728 := by
  have hfac : 4412 = 2^2 * (1103^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 1103^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_1103_1 : (ArithmeticFunction.sigma 1 (1103^1) : ℕ) = 1104 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1103)]
    norm_num
  rw [h_2_2, h_1103_1]
  norm_num

private lemma sigma_4413 : (ArithmeticFunction.sigma 1 4413 : ℕ) = 5888 := by
  have hfac : 4413 = 3^1 * (1471^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 1471^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_1471_1 : (ArithmeticFunction.sigma 1 (1471^1) : ℕ) = 1472 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1471)]
    norm_num
  rw [h_3_1, h_1471_1]
  norm_num

private lemma sigma_4414 : (ArithmeticFunction.sigma 1 4414 : ℕ) = 6624 := by
  have hfac : 4414 = 2^1 * (2207^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2207^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2207_1 : (ArithmeticFunction.sigma 1 (2207^1) : ℕ) = 2208 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2207)]
    norm_num
  rw [h_2_1, h_2207_1]
  norm_num

private lemma sigma_4415 : (ArithmeticFunction.sigma 1 4415 : ℕ) = 5304 := by
  have hfac : 4415 = 5^1 * (883^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 883^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_883_1 : (ArithmeticFunction.sigma 1 (883^1) : ℕ) = 884 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 883)]
    norm_num
  rw [h_5_1, h_883_1]
  norm_num

private lemma sigma_4416 : (ArithmeticFunction.sigma 1 4416 : ℕ) = 12192 := by
  have hfac : 4416 = 2^6 * (3^1 * (23^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^6) (n := 3^1 * (23^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 23^1) (by norm_num [Nat.gcd])]
  have h_2_6 : (ArithmeticFunction.sigma 1 (2^6) : ℕ) = 127 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_23_1 : (ArithmeticFunction.sigma 1 (23^1) : ℕ) = 24 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
    norm_num
  rw [h_2_6, h_3_1, h_23_1]
  norm_num

private lemma sigma_4417 : (ArithmeticFunction.sigma 1 4417 : ℕ) = 5056 := by
  have hfac : 4417 = 7^1 * (631^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 631^1) (by norm_num [Nat.gcd])]
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_631_1 : (ArithmeticFunction.sigma 1 (631^1) : ℕ) = 632 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 631)]
    norm_num
  rw [h_7_1, h_631_1]
  norm_num

private lemma sigma_4418 : (ArithmeticFunction.sigma 1 4418 : ℕ) = 6771 := by
  have hfac : 4418 = 2^1 * (47^2) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 47^2) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_47_2 : (ArithmeticFunction.sigma 1 (47^2) : ℕ) = 2257 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 47)]
    norm_num
  rw [h_2_1, h_47_2]
  norm_num

private lemma sigma_4419 : (ArithmeticFunction.sigma 1 4419 : ℕ) = 6396 := by
  have hfac : 4419 = 3^2 * (491^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 491^1) (by norm_num [Nat.gcd])]
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_491_1 : (ArithmeticFunction.sigma 1 (491^1) : ℕ) = 492 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 491)]
    norm_num
  rw [h_3_2, h_491_1]
  norm_num

private lemma sigma_4420 : (ArithmeticFunction.sigma 1 4420 : ℕ) = 10584 := by
  have hfac : 4420 = 2^2 * (5^1 * (13^1 * (17^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 5^1 * (13^1 * (17^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 13^1 * (17^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 17^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  rw [h_2_2, h_5_1, h_13_1, h_17_1]
  norm_num

private lemma sigma_4421 : (ArithmeticFunction.sigma 1 4421 : ℕ) = 4422 := by
  change (ArithmeticFunction.sigma 1 (4421^1) : ℕ) = 4422
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4421)]
  norm_num

private lemma sigma_4422 : (ArithmeticFunction.sigma 1 4422 : ℕ) = 9792 := by
  have hfac : 4422 = 2^1 * (3^1 * (11^1 * (67^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (11^1 * (67^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 11^1 * (67^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 67^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_67_1 : (ArithmeticFunction.sigma 1 (67^1) : ℕ) = 68 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 67)]
    norm_num
  rw [h_2_1, h_3_1, h_11_1, h_67_1]
  norm_num

private lemma sigma_4423 : (ArithmeticFunction.sigma 1 4423 : ℕ) = 4424 := by
  change (ArithmeticFunction.sigma 1 (4423^1) : ℕ) = 4424
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4423)]
  norm_num

private lemma sigma_4424 : (ArithmeticFunction.sigma 1 4424 : ℕ) = 9600 := by
  have hfac : 4424 = 2^3 * (7^1 * (79^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 7^1 * (79^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 79^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_79_1 : (ArithmeticFunction.sigma 1 (79^1) : ℕ) = 80 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 79)]
    norm_num
  rw [h_2_3, h_7_1, h_79_1]
  norm_num

private lemma sigma_4425 : (ArithmeticFunction.sigma 1 4425 : ℕ) = 7440 := by
  have hfac : 4425 = 3^1 * (5^2 * (59^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 5^2 * (59^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^2) (n := 59^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_2 : (ArithmeticFunction.sigma 1 (5^2) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_59_1 : (ArithmeticFunction.sigma 1 (59^1) : ℕ) = 60 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 59)]
    norm_num
  rw [h_3_1, h_5_2, h_59_1]
  norm_num

private lemma sigma_4426 : (ArithmeticFunction.sigma 1 4426 : ℕ) = 6642 := by
  have hfac : 4426 = 2^1 * (2213^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2213^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2213_1 : (ArithmeticFunction.sigma 1 (2213^1) : ℕ) = 2214 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2213)]
    norm_num
  rw [h_2_1, h_2213_1]
  norm_num

private lemma sigma_4427 : (ArithmeticFunction.sigma 1 4427 : ℕ) = 4680 := by
  have hfac : 4427 = 19^1 * (233^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 19^1) (n := 233^1) (by norm_num [Nat.gcd])]
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  have h_233_1 : (ArithmeticFunction.sigma 1 (233^1) : ℕ) = 234 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 233)]
    norm_num
  rw [h_19_1, h_233_1]
  norm_num

private lemma sigma_4428 : (ArithmeticFunction.sigma 1 4428 : ℕ) = 11760 := by
  have hfac : 4428 = 2^2 * (3^3 * (41^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 3^3 * (41^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^3) (n := 41^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_3 : (ArithmeticFunction.sigma 1 (3^3) : ℕ) = 40 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_41_1 : (ArithmeticFunction.sigma 1 (41^1) : ℕ) = 42 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 41)]
    norm_num
  rw [h_2_2, h_3_3, h_41_1]
  norm_num

private lemma sigma_4429 : (ArithmeticFunction.sigma 1 4429 : ℕ) = 4576 := by
  have hfac : 4429 = 43^1 * (103^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 43^1) (n := 103^1) (by norm_num [Nat.gcd])]
  have h_43_1 : (ArithmeticFunction.sigma 1 (43^1) : ℕ) = 44 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 43)]
    norm_num
  have h_103_1 : (ArithmeticFunction.sigma 1 (103^1) : ℕ) = 104 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 103)]
    norm_num
  rw [h_43_1, h_103_1]
  norm_num

private lemma sigma_4430 : (ArithmeticFunction.sigma 1 4430 : ℕ) = 7992 := by
  have hfac : 4430 = 2^1 * (5^1 * (443^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 5^1 * (443^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 443^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_443_1 : (ArithmeticFunction.sigma 1 (443^1) : ℕ) = 444 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 443)]
    norm_num
  rw [h_2_1, h_5_1, h_443_1]
  norm_num

private lemma sigma_4431 : (ArithmeticFunction.sigma 1 4431 : ℕ) = 6784 := by
  have hfac : 4431 = 3^1 * (7^1 * (211^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 7^1 * (211^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 211^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_211_1 : (ArithmeticFunction.sigma 1 (211^1) : ℕ) = 212 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 211)]
    norm_num
  rw [h_3_1, h_7_1, h_211_1]
  norm_num

private lemma sigma_4432 : (ArithmeticFunction.sigma 1 4432 : ℕ) = 8618 := by
  have hfac : 4432 = 2^4 * (277^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^4) (n := 277^1) (by norm_num [Nat.gcd])]
  have h_2_4 : (ArithmeticFunction.sigma 1 (2^4) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_277_1 : (ArithmeticFunction.sigma 1 (277^1) : ℕ) = 278 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 277)]
    norm_num
  rw [h_2_4, h_277_1]
  norm_num

private lemma sigma_4433 : (ArithmeticFunction.sigma 1 4433 : ℕ) = 5376 := by
  have hfac : 4433 = 11^1 * (13^1 * (31^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 13^1 * (31^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 31^1) (by norm_num [Nat.gcd])]
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_31_1 : (ArithmeticFunction.sigma 1 (31^1) : ℕ) = 32 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31)]
    norm_num
  rw [h_11_1, h_13_1, h_31_1]
  norm_num

private lemma sigma_4434 : (ArithmeticFunction.sigma 1 4434 : ℕ) = 8880 := by
  have hfac : 4434 = 2^1 * (3^1 * (739^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (739^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 739^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_739_1 : (ArithmeticFunction.sigma 1 (739^1) : ℕ) = 740 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 739)]
    norm_num
  rw [h_2_1, h_3_1, h_739_1]
  norm_num

private lemma sigma_4435 : (ArithmeticFunction.sigma 1 4435 : ℕ) = 5328 := by
  have hfac : 4435 = 5^1 * (887^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 887^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_887_1 : (ArithmeticFunction.sigma 1 (887^1) : ℕ) = 888 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 887)]
    norm_num
  rw [h_5_1, h_887_1]
  norm_num

private lemma sigma_4436 : (ArithmeticFunction.sigma 1 4436 : ℕ) = 7770 := by
  have hfac : 4436 = 2^2 * (1109^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 1109^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_1109_1 : (ArithmeticFunction.sigma 1 (1109^1) : ℕ) = 1110 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1109)]
    norm_num
  rw [h_2_2, h_1109_1]
  norm_num

private lemma sigma_4437 : (ArithmeticFunction.sigma 1 4437 : ℕ) = 7020 := by
  have hfac : 4437 = 3^2 * (17^1 * (29^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 17^1 * (29^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 17^1) (n := 29^1) (by norm_num [Nat.gcd])]
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  have h_29_1 : (ArithmeticFunction.sigma 1 (29^1) : ℕ) = 30 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 29)]
    norm_num
  rw [h_3_2, h_17_1, h_29_1]
  norm_num

private lemma sigma_4438 : (ArithmeticFunction.sigma 1 4438 : ℕ) = 7632 := by
  have hfac : 4438 = 2^1 * (7^1 * (317^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 7^1 * (317^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 317^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_317_1 : (ArithmeticFunction.sigma 1 (317^1) : ℕ) = 318 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 317)]
    norm_num
  rw [h_2_1, h_7_1, h_317_1]
  norm_num

private lemma sigma_4439 : (ArithmeticFunction.sigma 1 4439 : ℕ) = 4656 := by
  have hfac : 4439 = 23^1 * (193^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 23^1) (n := 193^1) (by norm_num [Nat.gcd])]
  have h_23_1 : (ArithmeticFunction.sigma 1 (23^1) : ℕ) = 24 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
    norm_num
  have h_193_1 : (ArithmeticFunction.sigma 1 (193^1) : ℕ) = 194 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 193)]
    norm_num
  rw [h_23_1, h_193_1]
  norm_num

private lemma sigma_4440 : (ArithmeticFunction.sigma 1 4440 : ℕ) = 13680 := by
  have hfac : 4440 = 2^3 * (3^1 * (5^1 * (37^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 3^1 * (5^1 * (37^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 5^1 * (37^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 37^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_37_1 : (ArithmeticFunction.sigma 1 (37^1) : ℕ) = 38 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 37)]
    norm_num
  rw [h_2_3, h_3_1, h_5_1, h_37_1]
  norm_num

private lemma sigma_4441 : (ArithmeticFunction.sigma 1 4441 : ℕ) = 4442 := by
  change (ArithmeticFunction.sigma 1 (4441^1) : ℕ) = 4442
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4441)]
  norm_num

private lemma sigma_4442 : (ArithmeticFunction.sigma 1 4442 : ℕ) = 6666 := by
  have hfac : 4442 = 2^1 * (2221^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2221^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2221_1 : (ArithmeticFunction.sigma 1 (2221^1) : ℕ) = 2222 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2221)]
    norm_num
  rw [h_2_1, h_2221_1]
  norm_num

private lemma sigma_4443 : (ArithmeticFunction.sigma 1 4443 : ℕ) = 5928 := by
  have hfac : 4443 = 3^1 * (1481^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 1481^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_1481_1 : (ArithmeticFunction.sigma 1 (1481^1) : ℕ) = 1482 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1481)]
    norm_num
  rw [h_3_1, h_1481_1]
  norm_num

private lemma sigma_4444 : (ArithmeticFunction.sigma 1 4444 : ℕ) = 8568 := by
  have hfac : 4444 = 2^2 * (11^1 * (101^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 11^1 * (101^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 101^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_101_1 : (ArithmeticFunction.sigma 1 (101^1) : ℕ) = 102 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 101)]
    norm_num
  rw [h_2_2, h_11_1, h_101_1]
  norm_num

private lemma sigma_4445 : (ArithmeticFunction.sigma 1 4445 : ℕ) = 6144 := by
  have hfac : 4445 = 5^1 * (7^1 * (127^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 7^1 * (127^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 127^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_127_1 : (ArithmeticFunction.sigma 1 (127^1) : ℕ) = 128 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 127)]
    norm_num
  rw [h_5_1, h_7_1, h_127_1]
  norm_num

private lemma sigma_4446 : (ArithmeticFunction.sigma 1 4446 : ℕ) = 10920 := by
  have hfac : 4446 = 2^1 * (3^2 * (13^1 * (19^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^2 * (13^1 * (19^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 13^1 * (19^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 19^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  rw [h_2_1, h_3_2, h_13_1, h_19_1]
  norm_num

private lemma sigma_4447 : (ArithmeticFunction.sigma 1 4447 : ℕ) = 4448 := by
  change (ArithmeticFunction.sigma 1 (4447^1) : ℕ) = 4448
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4447)]
  norm_num

private lemma sigma_4448 : (ArithmeticFunction.sigma 1 4448 : ℕ) = 8820 := by
  have hfac : 4448 = 2^5 * (139^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^5) (n := 139^1) (by norm_num [Nat.gcd])]
  have h_2_5 : (ArithmeticFunction.sigma 1 (2^5) : ℕ) = 63 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_139_1 : (ArithmeticFunction.sigma 1 (139^1) : ℕ) = 140 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 139)]
    norm_num
  rw [h_2_5, h_139_1]
  norm_num

private lemma sigma_4449 : (ArithmeticFunction.sigma 1 4449 : ℕ) = 5936 := by
  have hfac : 4449 = 3^1 * (1483^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 1483^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_1483_1 : (ArithmeticFunction.sigma 1 (1483^1) : ℕ) = 1484 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1483)]
    norm_num
  rw [h_3_1, h_1483_1]
  norm_num

private lemma sigma_4450 : (ArithmeticFunction.sigma 1 4450 : ℕ) = 8370 := by
  have hfac : 4450 = 2^1 * (5^2 * (89^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 5^2 * (89^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^2) (n := 89^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_2 : (ArithmeticFunction.sigma 1 (5^2) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_89_1 : (ArithmeticFunction.sigma 1 (89^1) : ℕ) = 90 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 89)]
    norm_num
  rw [h_2_1, h_5_2, h_89_1]
  norm_num

private lemma sigma_4451 : (ArithmeticFunction.sigma 1 4451 : ℕ) = 4452 := by
  change (ArithmeticFunction.sigma 1 (4451^1) : ℕ) = 4452
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4451)]
  norm_num

private lemma sigma_4452 : (ArithmeticFunction.sigma 1 4452 : ℕ) = 12096 := by
  have hfac : 4452 = 2^2 * (3^1 * (7^1 * (53^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 3^1 * (7^1 * (53^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 7^1 * (53^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 53^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_53_1 : (ArithmeticFunction.sigma 1 (53^1) : ℕ) = 54 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 53)]
    norm_num
  rw [h_2_2, h_3_1, h_7_1, h_53_1]
  norm_num

private lemma sigma_4453 : (ArithmeticFunction.sigma 1 4453 : ℕ) = 4588 := by
  have hfac : 4453 = 61^1 * (73^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 61^1) (n := 73^1) (by norm_num [Nat.gcd])]
  have h_61_1 : (ArithmeticFunction.sigma 1 (61^1) : ℕ) = 62 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 61)]
    norm_num
  have h_73_1 : (ArithmeticFunction.sigma 1 (73^1) : ℕ) = 74 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 73)]
    norm_num
  rw [h_61_1, h_73_1]
  norm_num

private lemma sigma_4454 : (ArithmeticFunction.sigma 1 4454 : ℕ) = 7128 := by
  have hfac : 4454 = 2^1 * (17^1 * (131^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 17^1 * (131^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 17^1) (n := 131^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  have h_131_1 : (ArithmeticFunction.sigma 1 (131^1) : ℕ) = 132 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 131)]
    norm_num
  rw [h_2_1, h_17_1, h_131_1]
  norm_num

private lemma sigma_4455 : (ArithmeticFunction.sigma 1 4455 : ℕ) = 8712 := by
  have hfac : 4455 = 3^4 * (5^1 * (11^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^4) (n := 5^1 * (11^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 11^1) (by norm_num [Nat.gcd])]
  have h_3_4 : (ArithmeticFunction.sigma 1 (3^4) : ℕ) = 121 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  rw [h_3_4, h_5_1, h_11_1]
  norm_num

private lemma sigma_4456 : (ArithmeticFunction.sigma 1 4456 : ℕ) = 8370 := by
  have hfac : 4456 = 2^3 * (557^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 557^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_557_1 : (ArithmeticFunction.sigma 1 (557^1) : ℕ) = 558 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 557)]
    norm_num
  rw [h_2_3, h_557_1]
  norm_num

private lemma sigma_4457 : (ArithmeticFunction.sigma 1 4457 : ℕ) = 4458 := by
  change (ArithmeticFunction.sigma 1 (4457^1) : ℕ) = 4458
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4457)]
  norm_num

private lemma sigma_4458 : (ArithmeticFunction.sigma 1 4458 : ℕ) = 8928 := by
  have hfac : 4458 = 2^1 * (3^1 * (743^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (743^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 743^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_743_1 : (ArithmeticFunction.sigma 1 (743^1) : ℕ) = 744 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 743)]
    norm_num
  rw [h_2_1, h_3_1, h_743_1]
  norm_num

private lemma sigma_4459 : (ArithmeticFunction.sigma 1 4459 : ℕ) = 5600 := by
  have hfac : 4459 = 7^3 * (13^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^3) (n := 13^1) (by norm_num [Nat.gcd])]
  have h_7_3 : (ArithmeticFunction.sigma 1 (7^3) : ℕ) = 400 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  rw [h_7_3, h_13_1]
  norm_num

private lemma sigma_4460 : (ArithmeticFunction.sigma 1 4460 : ℕ) = 9408 := by
  have hfac : 4460 = 2^2 * (5^1 * (223^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 5^1 * (223^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 223^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_223_1 : (ArithmeticFunction.sigma 1 (223^1) : ℕ) = 224 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 223)]
    norm_num
  rw [h_2_2, h_5_1, h_223_1]
  norm_num

private lemma sigma_4461 : (ArithmeticFunction.sigma 1 4461 : ℕ) = 5952 := by
  have hfac : 4461 = 3^1 * (1487^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 1487^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_1487_1 : (ArithmeticFunction.sigma 1 (1487^1) : ℕ) = 1488 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1487)]
    norm_num
  rw [h_3_1, h_1487_1]
  norm_num

private lemma sigma_4462 : (ArithmeticFunction.sigma 1 4462 : ℕ) = 7056 := by
  have hfac : 4462 = 2^1 * (23^1 * (97^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 23^1 * (97^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 23^1) (n := 97^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_23_1 : (ArithmeticFunction.sigma 1 (23^1) : ℕ) = 24 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
    norm_num
  have h_97_1 : (ArithmeticFunction.sigma 1 (97^1) : ℕ) = 98 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 97)]
    norm_num
  rw [h_2_1, h_23_1, h_97_1]
  norm_num

private lemma sigma_4463 : (ArithmeticFunction.sigma 1 4463 : ℕ) = 4464 := by
  change (ArithmeticFunction.sigma 1 (4463^1) : ℕ) = 4464
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4463)]
  norm_num

private lemma sigma_4464 : (ArithmeticFunction.sigma 1 4464 : ℕ) = 12896 := by
  have hfac : 4464 = 2^4 * (3^2 * (31^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^4) (n := 3^2 * (31^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 31^1) (by norm_num [Nat.gcd])]
  have h_2_4 : (ArithmeticFunction.sigma 1 (2^4) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_31_1 : (ArithmeticFunction.sigma 1 (31^1) : ℕ) = 32 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31)]
    norm_num
  rw [h_2_4, h_3_2, h_31_1]
  norm_num

private lemma sigma_4465 : (ArithmeticFunction.sigma 1 4465 : ℕ) = 5760 := by
  have hfac : 4465 = 5^1 * (19^1 * (47^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 19^1 * (47^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 19^1) (n := 47^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  have h_47_1 : (ArithmeticFunction.sigma 1 (47^1) : ℕ) = 48 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 47)]
    norm_num
  rw [h_5_1, h_19_1, h_47_1]
  norm_num

private lemma sigma_4466 : (ArithmeticFunction.sigma 1 4466 : ℕ) = 8640 := by
  have hfac : 4466 = 2^1 * (7^1 * (11^1 * (29^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 7^1 * (11^1 * (29^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 11^1 * (29^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 29^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_29_1 : (ArithmeticFunction.sigma 1 (29^1) : ℕ) = 30 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 29)]
    norm_num
  rw [h_2_1, h_7_1, h_11_1, h_29_1]
  norm_num

private lemma sigma_4467 : (ArithmeticFunction.sigma 1 4467 : ℕ) = 5960 := by
  have hfac : 4467 = 3^1 * (1489^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 1489^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_1489_1 : (ArithmeticFunction.sigma 1 (1489^1) : ℕ) = 1490 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1489)]
    norm_num
  rw [h_3_1, h_1489_1]
  norm_num

private lemma sigma_4468 : (ArithmeticFunction.sigma 1 4468 : ℕ) = 7826 := by
  have hfac : 4468 = 2^2 * (1117^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 1117^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_1117_1 : (ArithmeticFunction.sigma 1 (1117^1) : ℕ) = 1118 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1117)]
    norm_num
  rw [h_2_2, h_1117_1]
  norm_num

private lemma sigma_4469 : (ArithmeticFunction.sigma 1 4469 : ℕ) = 4620 := by
  have hfac : 4469 = 41^1 * (109^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 41^1) (n := 109^1) (by norm_num [Nat.gcd])]
  have h_41_1 : (ArithmeticFunction.sigma 1 (41^1) : ℕ) = 42 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 41)]
    norm_num
  have h_109_1 : (ArithmeticFunction.sigma 1 (109^1) : ℕ) = 110 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 109)]
    norm_num
  rw [h_41_1, h_109_1]
  norm_num

private lemma sigma_4470 : (ArithmeticFunction.sigma 1 4470 : ℕ) = 10800 := by
  have hfac : 4470 = 2^1 * (3^1 * (5^1 * (149^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (5^1 * (149^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 5^1 * (149^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 149^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_149_1 : (ArithmeticFunction.sigma 1 (149^1) : ℕ) = 150 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 149)]
    norm_num
  rw [h_2_1, h_3_1, h_5_1, h_149_1]
  norm_num

private lemma sigma_4471 : (ArithmeticFunction.sigma 1 4471 : ℕ) = 4752 := by
  have hfac : 4471 = 17^1 * (263^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 17^1) (n := 263^1) (by norm_num [Nat.gcd])]
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  have h_263_1 : (ArithmeticFunction.sigma 1 (263^1) : ℕ) = 264 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 263)]
    norm_num
  rw [h_17_1, h_263_1]
  norm_num

private lemma sigma_4472 : (ArithmeticFunction.sigma 1 4472 : ℕ) = 9240 := by
  have hfac : 4472 = 2^3 * (13^1 * (43^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 13^1 * (43^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 43^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_43_1 : (ArithmeticFunction.sigma 1 (43^1) : ℕ) = 44 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 43)]
    norm_num
  rw [h_2_3, h_13_1, h_43_1]
  norm_num

private lemma sigma_4473 : (ArithmeticFunction.sigma 1 4473 : ℕ) = 7488 := by
  have hfac : 4473 = 3^2 * (7^1 * (71^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 7^1 * (71^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 71^1) (by norm_num [Nat.gcd])]
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_71_1 : (ArithmeticFunction.sigma 1 (71^1) : ℕ) = 72 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 71)]
    norm_num
  rw [h_3_2, h_7_1, h_71_1]
  norm_num

private lemma sigma_4474 : (ArithmeticFunction.sigma 1 4474 : ℕ) = 6714 := by
  have hfac : 4474 = 2^1 * (2237^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2237^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2237_1 : (ArithmeticFunction.sigma 1 (2237^1) : ℕ) = 2238 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2237)]
    norm_num
  rw [h_2_1, h_2237_1]
  norm_num

private lemma sigma_4475 : (ArithmeticFunction.sigma 1 4475 : ℕ) = 5580 := by
  have hfac : 4475 = 5^2 * (179^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^2) (n := 179^1) (by norm_num [Nat.gcd])]
  have h_5_2 : (ArithmeticFunction.sigma 1 (5^2) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_179_1 : (ArithmeticFunction.sigma 1 (179^1) : ℕ) = 180 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 179)]
    norm_num
  rw [h_5_2, h_179_1]
  norm_num

private lemma sigma_4476 : (ArithmeticFunction.sigma 1 4476 : ℕ) = 10472 := by
  have hfac : 4476 = 2^2 * (3^1 * (373^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 3^1 * (373^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 373^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_373_1 : (ArithmeticFunction.sigma 1 (373^1) : ℕ) = 374 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 373)]
    norm_num
  rw [h_2_2, h_3_1, h_373_1]
  norm_num

private lemma sigma_4477 : (ArithmeticFunction.sigma 1 4477 : ℕ) = 5054 := by
  have hfac : 4477 = 11^2 * (37^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^2) (n := 37^1) (by norm_num [Nat.gcd])]
  have h_11_2 : (ArithmeticFunction.sigma 1 (11^2) : ℕ) = 133 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_37_1 : (ArithmeticFunction.sigma 1 (37^1) : ℕ) = 38 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 37)]
    norm_num
  rw [h_11_2, h_37_1]
  norm_num

private lemma sigma_4478 : (ArithmeticFunction.sigma 1 4478 : ℕ) = 6720 := by
  have hfac : 4478 = 2^1 * (2239^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2239^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2239_1 : (ArithmeticFunction.sigma 1 (2239^1) : ℕ) = 2240 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2239)]
    norm_num
  rw [h_2_1, h_2239_1]
  norm_num

private lemma sigma_4479 : (ArithmeticFunction.sigma 1 4479 : ℕ) = 5976 := by
  have hfac : 4479 = 3^1 * (1493^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 1493^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_1493_1 : (ArithmeticFunction.sigma 1 (1493^1) : ℕ) = 1494 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1493)]
    norm_num
  rw [h_3_1, h_1493_1]
  norm_num

private lemma sigma_4480 : (ArithmeticFunction.sigma 1 4480 : ℕ) = 12240 := by
  have hfac : 4480 = 2^7 * (5^1 * (7^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^7) (n := 5^1 * (7^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 7^1) (by norm_num [Nat.gcd])]
  have h_2_7 : (ArithmeticFunction.sigma 1 (2^7) : ℕ) = 255 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  rw [h_2_7, h_5_1, h_7_1]
  norm_num

private lemma sigma_4481 : (ArithmeticFunction.sigma 1 4481 : ℕ) = 4482 := by
  change (ArithmeticFunction.sigma 1 (4481^1) : ℕ) = 4482
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4481)]
  norm_num

private lemma sigma_4482 : (ArithmeticFunction.sigma 1 4482 : ℕ) = 10080 := by
  have hfac : 4482 = 2^1 * (3^3 * (83^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^3 * (83^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^3) (n := 83^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_3 : (ArithmeticFunction.sigma 1 (3^3) : ℕ) = 40 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_83_1 : (ArithmeticFunction.sigma 1 (83^1) : ℕ) = 84 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 83)]
    norm_num
  rw [h_2_1, h_3_3, h_83_1]
  norm_num

private lemma sigma_4483 : (ArithmeticFunction.sigma 1 4483 : ℕ) = 4484 := by
  change (ArithmeticFunction.sigma 1 (4483^1) : ℕ) = 4484
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4483)]
  norm_num

private lemma sigma_4484 : (ArithmeticFunction.sigma 1 4484 : ℕ) = 8400 := by
  have hfac : 4484 = 2^2 * (19^1 * (59^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 19^1 * (59^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 19^1) (n := 59^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_19_1 : (ArithmeticFunction.sigma 1 (19^1) : ℕ) = 20 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 19)]
    norm_num
  have h_59_1 : (ArithmeticFunction.sigma 1 (59^1) : ℕ) = 60 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 59)]
    norm_num
  rw [h_2_2, h_19_1, h_59_1]
  norm_num

private lemma sigma_4485 : (ArithmeticFunction.sigma 1 4485 : ℕ) = 8064 := by
  have hfac : 4485 = 3^1 * (5^1 * (13^1 * (23^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 5^1 * (13^1 * (23^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 13^1 * (23^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 23^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_23_1 : (ArithmeticFunction.sigma 1 (23^1) : ℕ) = 24 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 23)]
    norm_num
  rw [h_3_1, h_5_1, h_13_1, h_23_1]
  norm_num

private lemma sigma_4486 : (ArithmeticFunction.sigma 1 4486 : ℕ) = 6732 := by
  have hfac : 4486 = 2^1 * (2243^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 2243^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_2243_1 : (ArithmeticFunction.sigma 1 (2243^1) : ℕ) = 2244 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2243)]
    norm_num
  rw [h_2_1, h_2243_1]
  norm_num

private lemma sigma_4487 : (ArithmeticFunction.sigma 1 4487 : ℕ) = 5136 := by
  have hfac : 4487 = 7^1 * (641^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 641^1) (by norm_num [Nat.gcd])]
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_641_1 : (ArithmeticFunction.sigma 1 (641^1) : ℕ) = 642 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 641)]
    norm_num
  rw [h_7_1, h_641_1]
  norm_num

private lemma sigma_4488 : (ArithmeticFunction.sigma 1 4488 : ℕ) = 12960 := by
  have hfac : 4488 = 2^3 * (3^1 * (11^1 * (17^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^3) (n := 3^1 * (11^1 * (17^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 11^1 * (17^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 17^1) (by norm_num [Nat.gcd])]
  have h_2_3 : (ArithmeticFunction.sigma 1 (2^3) : ℕ) = 15 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_17_1 : (ArithmeticFunction.sigma 1 (17^1) : ℕ) = 18 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 17)]
    norm_num
  rw [h_2_3, h_3_1, h_11_1, h_17_1]
  norm_num

private lemma sigma_4489 : (ArithmeticFunction.sigma 1 4489 : ℕ) = 4557 := by
  change (ArithmeticFunction.sigma 1 (67^2) : ℕ) = 4557
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 67)]
  norm_num

private lemma sigma_4490 : (ArithmeticFunction.sigma 1 4490 : ℕ) = 8100 := by
  have hfac : 4490 = 2^1 * (5^1 * (449^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 5^1 * (449^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 449^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_449_1 : (ArithmeticFunction.sigma 1 (449^1) : ℕ) = 450 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 449)]
    norm_num
  rw [h_2_1, h_5_1, h_449_1]
  norm_num

private lemma sigma_4491 : (ArithmeticFunction.sigma 1 4491 : ℕ) = 6500 := by
  have hfac : 4491 = 3^2 * (499^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 499^1) (by norm_num [Nat.gcd])]
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_499_1 : (ArithmeticFunction.sigma 1 (499^1) : ℕ) = 500 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 499)]
    norm_num
  rw [h_3_2, h_499_1]
  norm_num

private lemma sigma_4492 : (ArithmeticFunction.sigma 1 4492 : ℕ) = 7868 := by
  have hfac : 4492 = 2^2 * (1123^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 1123^1) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_1123_1 : (ArithmeticFunction.sigma 1 (1123^1) : ℕ) = 1124 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1123)]
    norm_num
  rw [h_2_2, h_1123_1]
  norm_num

private lemma sigma_4493 : (ArithmeticFunction.sigma 1 4493 : ℕ) = 4494 := by
  change (ArithmeticFunction.sigma 1 (4493^1) : ℕ) = 4494
  rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 4493)]
  norm_num

private lemma sigma_4494 : (ArithmeticFunction.sigma 1 4494 : ℕ) = 10368 := by
  have hfac : 4494 = 2^1 * (3^1 * (7^1 * (107^1))) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 3^1 * (7^1 * (107^1))) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 7^1 * (107^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 7^1) (n := 107^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_7_1 : (ArithmeticFunction.sigma 1 (7^1) : ℕ) = 8 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 7)]
    norm_num
  have h_107_1 : (ArithmeticFunction.sigma 1 (107^1) : ℕ) = 108 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 107)]
    norm_num
  rw [h_2_1, h_3_1, h_7_1, h_107_1]
  norm_num

private lemma sigma_4495 : (ArithmeticFunction.sigma 1 4495 : ℕ) = 5760 := by
  have hfac : 4495 = 5^1 * (29^1 * (31^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 5^1) (n := 29^1 * (31^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 29^1) (n := 31^1) (by norm_num [Nat.gcd])]
  have h_5_1 : (ArithmeticFunction.sigma 1 (5^1) : ℕ) = 6 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  have h_29_1 : (ArithmeticFunction.sigma 1 (29^1) : ℕ) = 30 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 29)]
    norm_num
  have h_31_1 : (ArithmeticFunction.sigma 1 (31^1) : ℕ) = 32 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 31)]
    norm_num
  rw [h_5_1, h_29_1, h_31_1]
  norm_num

private lemma sigma_4496 : (ArithmeticFunction.sigma 1 4496 : ℕ) = 8742 := by
  have hfac : 4496 = 2^4 * (281^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^4) (n := 281^1) (by norm_num [Nat.gcd])]
  have h_2_4 : (ArithmeticFunction.sigma 1 (2^4) : ℕ) = 31 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_281_1 : (ArithmeticFunction.sigma 1 (281^1) : ℕ) = 282 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 281)]
    norm_num
  rw [h_2_4, h_281_1]
  norm_num

private lemma sigma_4497 : (ArithmeticFunction.sigma 1 4497 : ℕ) = 6000 := by
  have hfac : 4497 = 3^1 * (1499^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^1) (n := 1499^1) (by norm_num [Nat.gcd])]
  have h_3_1 : (ArithmeticFunction.sigma 1 (3^1) : ℕ) = 4 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_1499_1 : (ArithmeticFunction.sigma 1 (1499^1) : ℕ) = 1500 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 1499)]
    norm_num
  rw [h_3_1, h_1499_1]
  norm_num

private lemma sigma_4498 : (ArithmeticFunction.sigma 1 4498 : ℕ) = 7308 := by
  have hfac : 4498 = 2^1 * (13^1 * (173^1)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^1) (n := 13^1 * (173^1)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 13^1) (n := 173^1) (by norm_num [Nat.gcd])]
  have h_2_1 : (ArithmeticFunction.sigma 1 (2^1) : ℕ) = 3 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_13_1 : (ArithmeticFunction.sigma 1 (13^1) : ℕ) = 14 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 13)]
    norm_num
  have h_173_1 : (ArithmeticFunction.sigma 1 (173^1) : ℕ) = 174 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 173)]
    norm_num
  rw [h_2_1, h_13_1, h_173_1]
  norm_num

private lemma sigma_4499 : (ArithmeticFunction.sigma 1 4499 : ℕ) = 4920 := by
  have hfac : 4499 = 11^1 * (409^1) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 11^1) (n := 409^1) (by norm_num [Nat.gcd])]
  have h_11_1 : (ArithmeticFunction.sigma 1 (11^1) : ℕ) = 12 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 11)]
    norm_num
  have h_409_1 : (ArithmeticFunction.sigma 1 (409^1) : ℕ) = 410 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 409)]
    norm_num
  rw [h_11_1, h_409_1]
  norm_num

private lemma sigma_4500 : (ArithmeticFunction.sigma 1 4500 : ℕ) = 14196 := by
  have hfac : 4500 = 2^2 * (3^2 * (5^3)) := by norm_num
  rw [hfac]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 2^2) (n := 3^2 * (5^3)) (by norm_num [Nat.gcd])]
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (m := 3^2) (n := 5^3) (by norm_num [Nat.gcd])]
  have h_2_2 : (ArithmeticFunction.sigma 1 (2^2) : ℕ) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 2)]
    norm_num
  have h_3_2 : (ArithmeticFunction.sigma 1 (3^2) : ℕ) = 13 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 3)]
    norm_num
  have h_5_3 : (ArithmeticFunction.sigma 1 (5^3) : ℕ) = 156 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5)]
    norm_num
  rw [h_2_2, h_3_2, h_5_3]
  norm_num

private lemma sigma_le_15120 (n : ℕ) (hn : n ∈ Finset.Icc 4001 4500) : (ArithmeticFunction.sigma 1 n : ℕ) ≤ 15120 := by
  rcases Finset.mem_Icc.mp hn with ⟨hL, hU⟩
  interval_cases n <;> norm_num [sigma_4001, sigma_4002, sigma_4003, sigma_4004, sigma_4005, sigma_4006, sigma_4007, sigma_4008, sigma_4009, sigma_4010, sigma_4011, sigma_4012, sigma_4013, sigma_4014, sigma_4015, sigma_4016, sigma_4017, sigma_4018, sigma_4019, sigma_4020, sigma_4021, sigma_4022, sigma_4023, sigma_4024, sigma_4025, sigma_4026, sigma_4027, sigma_4028, sigma_4029, sigma_4030, sigma_4031, sigma_4032, sigma_4033, sigma_4034, sigma_4035, sigma_4036, sigma_4037, sigma_4038, sigma_4039, sigma_4040, sigma_4041, sigma_4042, sigma_4043, sigma_4044, sigma_4045, sigma_4046, sigma_4047, sigma_4048, sigma_4049, sigma_4050, sigma_4051, sigma_4052, sigma_4053, sigma_4054, sigma_4055, sigma_4056, sigma_4057, sigma_4058, sigma_4059, sigma_4060, sigma_4061, sigma_4062, sigma_4063, sigma_4064, sigma_4065, sigma_4066, sigma_4067, sigma_4068, sigma_4069, sigma_4070, sigma_4071, sigma_4072, sigma_4073, sigma_4074, sigma_4075, sigma_4076, sigma_4077, sigma_4078, sigma_4079, sigma_4080, sigma_4081, sigma_4082, sigma_4083, sigma_4084, sigma_4085, sigma_4086, sigma_4087, sigma_4088, sigma_4089, sigma_4090, sigma_4091, sigma_4092, sigma_4093, sigma_4094, sigma_4095, sigma_4096, sigma_4097, sigma_4098, sigma_4099, sigma_4100, sigma_4101, sigma_4102, sigma_4103, sigma_4104, sigma_4105, sigma_4106, sigma_4107, sigma_4108, sigma_4109, sigma_4110, sigma_4111, sigma_4112, sigma_4113, sigma_4114, sigma_4115, sigma_4116, sigma_4117, sigma_4118, sigma_4119, sigma_4120, sigma_4121, sigma_4122, sigma_4123, sigma_4124, sigma_4125, sigma_4126, sigma_4127, sigma_4128, sigma_4129, sigma_4130, sigma_4131, sigma_4132, sigma_4133, sigma_4134, sigma_4135, sigma_4136, sigma_4137, sigma_4138, sigma_4139, sigma_4140, sigma_4141, sigma_4142, sigma_4143, sigma_4144, sigma_4145, sigma_4146, sigma_4147, sigma_4148, sigma_4149, sigma_4150, sigma_4151, sigma_4152, sigma_4153, sigma_4154, sigma_4155, sigma_4156, sigma_4157, sigma_4158, sigma_4159, sigma_4160, sigma_4161, sigma_4162, sigma_4163, sigma_4164, sigma_4165, sigma_4166, sigma_4167, sigma_4168, sigma_4169, sigma_4170, sigma_4171, sigma_4172, sigma_4173, sigma_4174, sigma_4175, sigma_4176, sigma_4177, sigma_4178, sigma_4179, sigma_4180, sigma_4181, sigma_4182, sigma_4183, sigma_4184, sigma_4185, sigma_4186, sigma_4187, sigma_4188, sigma_4189, sigma_4190, sigma_4191, sigma_4192, sigma_4193, sigma_4194, sigma_4195, sigma_4196, sigma_4197, sigma_4198, sigma_4199, sigma_4200, sigma_4201, sigma_4202, sigma_4203, sigma_4204, sigma_4205, sigma_4206, sigma_4207, sigma_4208, sigma_4209, sigma_4210, sigma_4211, sigma_4212, sigma_4213, sigma_4214, sigma_4215, sigma_4216, sigma_4217, sigma_4218, sigma_4219, sigma_4220, sigma_4221, sigma_4222, sigma_4223, sigma_4224, sigma_4225, sigma_4226, sigma_4227, sigma_4228, sigma_4229, sigma_4230, sigma_4231, sigma_4232, sigma_4233, sigma_4234, sigma_4235, sigma_4236, sigma_4237, sigma_4238, sigma_4239, sigma_4240, sigma_4241, sigma_4242, sigma_4243, sigma_4244, sigma_4245, sigma_4246, sigma_4247, sigma_4248, sigma_4249, sigma_4250, sigma_4251, sigma_4252, sigma_4253, sigma_4254, sigma_4255, sigma_4256, sigma_4257, sigma_4258, sigma_4259, sigma_4260, sigma_4261, sigma_4262, sigma_4263, sigma_4264, sigma_4265, sigma_4266, sigma_4267, sigma_4268, sigma_4269, sigma_4270, sigma_4271, sigma_4272, sigma_4273, sigma_4274, sigma_4275, sigma_4276, sigma_4277, sigma_4278, sigma_4279, sigma_4280, sigma_4281, sigma_4282, sigma_4283, sigma_4284, sigma_4285, sigma_4286, sigma_4287, sigma_4288, sigma_4289, sigma_4290, sigma_4291, sigma_4292, sigma_4293, sigma_4294, sigma_4295, sigma_4296, sigma_4297, sigma_4298, sigma_4299, sigma_4300, sigma_4301, sigma_4302, sigma_4303, sigma_4304, sigma_4305, sigma_4306, sigma_4307, sigma_4308, sigma_4309, sigma_4310, sigma_4311, sigma_4312, sigma_4313, sigma_4314, sigma_4315, sigma_4316, sigma_4317, sigma_4318, sigma_4319, sigma_4320, sigma_4321, sigma_4322, sigma_4323, sigma_4324, sigma_4325, sigma_4326, sigma_4327, sigma_4328, sigma_4329, sigma_4330, sigma_4331, sigma_4332, sigma_4333, sigma_4334, sigma_4335, sigma_4336, sigma_4337, sigma_4338, sigma_4339, sigma_4340, sigma_4341, sigma_4342, sigma_4343, sigma_4344, sigma_4345, sigma_4346, sigma_4347, sigma_4348, sigma_4349, sigma_4350, sigma_4351, sigma_4352, sigma_4353, sigma_4354, sigma_4355, sigma_4356, sigma_4357, sigma_4358, sigma_4359, sigma_4360, sigma_4361, sigma_4362, sigma_4363, sigma_4364, sigma_4365, sigma_4366, sigma_4367, sigma_4368, sigma_4369, sigma_4370, sigma_4371, sigma_4372, sigma_4373, sigma_4374, sigma_4375, sigma_4376, sigma_4377, sigma_4378, sigma_4379, sigma_4380, sigma_4381, sigma_4382, sigma_4383, sigma_4384, sigma_4385, sigma_4386, sigma_4387, sigma_4388, sigma_4389, sigma_4390, sigma_4391, sigma_4392, sigma_4393, sigma_4394, sigma_4395, sigma_4396, sigma_4397, sigma_4398, sigma_4399, sigma_4400, sigma_4401, sigma_4402, sigma_4403, sigma_4404, sigma_4405, sigma_4406, sigma_4407, sigma_4408, sigma_4409, sigma_4410, sigma_4411, sigma_4412, sigma_4413, sigma_4414, sigma_4415, sigma_4416, sigma_4417, sigma_4418, sigma_4419, sigma_4420, sigma_4421, sigma_4422, sigma_4423, sigma_4424, sigma_4425, sigma_4426, sigma_4427, sigma_4428, sigma_4429, sigma_4430, sigma_4431, sigma_4432, sigma_4433, sigma_4434, sigma_4435, sigma_4436, sigma_4437, sigma_4438, sigma_4439, sigma_4440, sigma_4441, sigma_4442, sigma_4443, sigma_4444, sigma_4445, sigma_4446, sigma_4447, sigma_4448, sigma_4449, sigma_4450, sigma_4451, sigma_4452, sigma_4453, sigma_4454, sigma_4455, sigma_4456, sigma_4457, sigma_4458, sigma_4459, sigma_4460, sigma_4461, sigma_4462, sigma_4463, sigma_4464, sigma_4465, sigma_4466, sigma_4467, sigma_4468, sigma_4469, sigma_4470, sigma_4471, sigma_4472, sigma_4473, sigma_4474, sigma_4475, sigma_4476, sigma_4477, sigma_4478, sigma_4479, sigma_4480, sigma_4481, sigma_4482, sigma_4483, sigma_4484, sigma_4485, sigma_4486, sigma_4487, sigma_4488, sigma_4489, sigma_4490, sigma_4491, sigma_4492, sigma_4493, sigma_4494, sigma_4495, sigma_4496, sigma_4497, sigma_4498, sigma_4499, sigma_4500]

theorem finite_check_range_4001_4500 (n : ℕ) (hn0 : 0 < n) (hL : 4001 ≤ n) (hU : n ≤ 4500) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
      (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) := by
  have hmem : n ∈ Finset.Icc 4001 4500 := Finset.mem_Icc.mpr ⟨hL, hU⟩
  have hsigma : (ArithmeticFunction.sigma 1 n : ℕ) ≤ 15120 := sigma_le_15120 n hmem
  have hsigma_real : ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤ (15120 : ℝ) := by
    exact_mod_cast hsigma
  have hrhs := rhs_ge_15120 n hn0 hL
  exact le_trans hsigma_real hrhs


end Commons.NumberTheory.Lagarias