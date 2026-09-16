import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Commons.Analysis.Sum.min_log_ratio_sum_le

namespace Commons.NumberTheory.BombieriVinogradov

open Finset
open scoped BigOperators
open Commons.Analysis.Sum

/-- Explicit-constant form of the one-dimensional `min(1, 1/(K |log|))` estimate:
for `1 ≤ m`, `3/2 ≤ x`, `x ≤ M*N+1` the sum over `n ≤ N` is at most `100 log(2MN+2)`.
This is `Commons.Analysis.Sum.min_log_ratio_sum_le` with its existential constant
specialised to its explicit witness `100`. -/
lemma min_log_ratio_sum_le_100 (M N : ℕ) (x : ℝ) (m : ℕ)
    (hM : 1 ≤ M) (hN : 1 ≤ N) (hm : 1 ≤ m) (hx : 3 / 2 ≤ x)
    (hxK : x ≤ (M : ℝ) * (N : ℝ) + 1) :
    ∑ n ∈ Finset.Icc 1 N,
      min 1 (1 / (((M : ℝ) * (N : ℝ)) * |Real.log (x / ((m : ℝ) * (n : ℝ)))|))
      ≤ 100 * Real.log (2 * (M : ℝ) * (N : ℝ) + 2) := by
  set K : ℝ := (M:ℝ)*(N:ℝ) with hK
  have hRHS : 2 * (M:ℝ) * (N:ℝ) + 2 = 2 * K + 2 := by rw [hK]; ring
  rw [hRHS]
  set t : ℕ → ℝ := fun n => |Real.log (x / ((m:ℝ)*(n:ℝ)))| with ht
  change ∑ n ∈ Finset.Icc 1 N, min 1 (1 / (K * t n)) ≤ 100 * Real.log (2 * K + 2)
  -- basic facts
  have hM1 : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hxpos : 0 < x := by linarith
  have hmpos : (0:ℝ) < (m:ℝ) := by linarith
  have hKpos : 0 < K := by rw [hK]; positivity
  have hKge1 : 1 ≤ K := by rw [hK]; nlinarith
  have hxle : x ≤ K + 1 := by rw [hK]; exact hxK
  have hxdiv : x / (m:ℝ) ≤ K + 1 := by
    rw [div_le_iff₀ hmpos]
    nlinarith [hxle, hm1]
  have hxdivK : x / (m:ℝ) / K ≤ 2 := by
    rw [div_le_iff₀ hKpos]
    nlinarith [hxdiv, hKge1]
  -- choose J
  set J : ℕ := Nat.log2 (M*N) with hJdef
  have hMNne : M*N ≠ 0 := by positivity
  have h2J_le : (2:ℕ)^J ≤ M*N := by
    rw [hJdef, Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 hMNne
  have hMN_lt : M*N < 2^(J+1) := by
    rw [hJdef, Nat.log2_eq_log_two]
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (by norm_num) (M*N)
  have h2J_leR : (2:ℝ)^J ≤ K := by
    have h : ((2:ℕ)^J : ℝ) ≤ ((M*N : ℕ) : ℝ) := by exact_mod_cast h2J_le
    rw [hK]
    push_cast at h ⊢
    exact h
  -- termwise comparison with `1/max (K t) 1`
  have stepA : ∑ n ∈ Finset.Icc 1 N, min 1 (1 / (K * t n))
      ≤ ∑ n ∈ Finset.Icc 1 N, 1 / max (K * t n) 1 :=
    Finset.sum_le_sum (fun n _ => min_one_div_le_inv_max (K * t n))
  -- discrete layer cake
  have stepB : ∑ n ∈ Finset.Icc 1 N, 1 / max (K * t n) 1
      ≤ ∑ n ∈ Finset.Icc 1 N, ((∑ j ∈ Finset.range (J+1),
            (1/2:ℝ)^j * (if t n ≤ (2:ℝ)^j / K then 1 else 0)) + (1/2:ℝ)^J) := by
    apply Finset.sum_le_sum
    intro n _
    have hs : 1 ≤ max (K * t n) 1 := le_max_right _ _
    have hmain := inv_le_sum_range_pow (max (K * t n) 1) hs J
    have hle : (∑ j ∈ Finset.range (J+1),
          (if max (K * t n) 1 ≤ (2:ℝ)^j then (1/2:ℝ)^j else 0))
        ≤ ∑ j ∈ Finset.range (J+1),
            (1/2:ℝ)^j * (if t n ≤ (2:ℝ)^j / K then 1 else 0) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hc : max (K * t n) 1 ≤ (2:ℝ)^j
      · rw [if_pos hc]
        have htle : t n ≤ (2:ℝ)^j / K := by
          rw [le_div_iff₀ hKpos]
          have h1 : K * t n ≤ (2:ℝ)^j := le_trans (le_max_left _ _) hc
          nlinarith [h1]
        rw [if_pos htle, mul_one]
      · rw [if_neg hc]
        by_cases hc2 : t n ≤ (2:ℝ)^j / K
        · rw [if_pos hc2]; positivity
        · rw [if_neg hc2, mul_zero]
    linarith [hmain, hle]
  -- distribute the double sum
  have stepC : ∑ n ∈ Finset.Icc 1 N, ((∑ j ∈ Finset.range (J+1),
          (1/2:ℝ)^j * (if t n ≤ (2:ℝ)^j / K then 1 else 0)) + (1/2:ℝ)^J)
      = (∑ j ∈ Finset.range (J+1), (1/2:ℝ)^j *
            (((Finset.Icc 1 N).filter (fun n : ℕ => t n ≤ (2:ℝ)^j / K)).card : ℝ))
        + (N:ℝ) * (1/2:ℝ)^J := by
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_boole]
    · rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [Nat.card_Icc, Nat.add_sub_cancel]
  -- termwise counting bound
  have hband : ∀ j ∈ Finset.range (J+1),
      (1/2:ℝ)^j * (((Finset.Icc 1 N).filter (fun n : ℕ => t n ≤ (2:ℝ)^j / K)).card : ℝ)
        ≤ (1/2:ℝ)^j * (6 * (x/(m:ℝ)) * ((2:ℝ)^j / K) + 1) := by
    intro j hj
    have hjle : j ≤ J := by rw [Finset.mem_range] at hj; omega
    have hT0 : 0 ≤ (2:ℝ)^j / K := by positivity
    have hT1 : (2:ℝ)^j / K ≤ 1 := by
      rw [div_le_one hKpos]
      exact le_trans (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hjle) h2J_leR
    have hcount : (((Finset.Icc 1 N).filter (fun n : ℕ => t n ≤ (2:ℝ)^j / K)).card : ℝ)
        ≤ (x/(m:ℝ)) * (Real.exp ((2:ℝ)^j / K) - Real.exp (-((2:ℝ)^j / K))) + 1 := by
      have h := card_filter_abs_log_le N x m hm hx ((2:ℝ)^j / K) hT0
      simpa only [ht] using h
    have h6 := exp_sub_exp_neg_le_six_mul hT0 hT1
    have hxmp : 0 ≤ x/(m:ℝ) := by positivity
    calc (1/2:ℝ)^j * (((Finset.Icc 1 N).filter (fun n : ℕ => t n ≤ (2:ℝ)^j / K)).card : ℝ)
        ≤ (1/2:ℝ)^j * ((x/(m:ℝ)) *
            (Real.exp ((2:ℝ)^j / K) - Real.exp (-((2:ℝ)^j / K))) + 1) :=
          mul_le_mul_of_nonneg_left hcount (by positivity)
      _ ≤ (1/2:ℝ)^j * (6 * (x/(m:ℝ)) * ((2:ℝ)^j / K) + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith [h6, hxmp]
  have hsum_band : ∑ j ∈ Finset.range (J+1), (1/2:ℝ)^j *
        (((Finset.Icc 1 N).filter (fun n : ℕ => t n ≤ (2:ℝ)^j / K)).card : ℝ)
      ≤ ∑ j ∈ Finset.range (J+1), (1/2:ℝ)^j * (6 * (x/(m:ℝ)) * ((2:ℝ)^j / K) + 1) :=
    Finset.sum_le_sum hband
  have hsum_band2 : ∑ j ∈ Finset.range (J+1),
        (1/2:ℝ)^j * (6 * (x/(m:ℝ)) * ((2:ℝ)^j / K) + 1) ≤ 12 * ((J:ℝ) + 1) + 2 := by
    have hrewrite : ∀ j : ℕ, (1/2:ℝ)^j * (6 * (x/(m:ℝ)) * ((2:ℝ)^j / K) + 1)
        = 6 * (x/(m:ℝ)) / K + (1/2:ℝ)^j := by
      intro j
      have hpt : (1/2:ℝ)^j * ((2:ℝ)^j / K) = 1/K := by
        rw [← mul_div_assoc]
        have h2j : ((1:ℝ)/2)^j * (2:ℝ)^j = 1 := by rw [← mul_pow]; norm_num
        rw [h2j]
      calc (1/2:ℝ)^j * (6 * (x/(m:ℝ)) * ((2:ℝ)^j / K) + 1)
          = 6 * (x/(m:ℝ)) * ((1/2:ℝ)^j * ((2:ℝ)^j / K)) + (1/2:ℝ)^j := by ring
        _ = 6 * (x/(m:ℝ)) * (1/K) + (1/2:ℝ)^j := by rw [hpt]
        _ = 6 * (x/(m:ℝ)) / K + (1/2:ℝ)^j := by ring
    simp_rw [hrewrite]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp only [Nat.cast_add, Nat.cast_one]
    have h1 : 6 * (x/(m:ℝ)) / K ≤ 12 := by
      have hx := hxdivK
      rw [div_le_iff₀ hKpos] at hx ⊢
      nlinarith [hx]
    have h2 := sum_range_half_le_two (J+1)
    nlinarith [h1, h2]
  have hN2J : (N:ℝ) * (1/2:ℝ)^J ≤ 2 := by
    have hNle : N ≤ M*N := Nat.le_mul_of_pos_left N (by omega : 0 < M)
    have hNleR : (N:ℝ) ≤ ((M*N : ℕ) : ℝ) := by exact_mod_cast hNle
    have hMNltR : ((M*N : ℕ) : ℝ) < (2:ℝ)^(J+1) := by exact_mod_cast hMN_lt
    have h2eq : (2:ℝ)^(J+1) * (1/2:ℝ)^J = 2 := by
      rw [pow_succ', mul_assoc, ← mul_pow]; norm_num
    calc (N:ℝ) * (1/2:ℝ)^J ≤ ((M*N : ℕ) : ℝ) * (1/2:ℝ)^J :=
          mul_le_mul_of_nonneg_right hNleR (by positivity)
      _ ≤ (2:ℝ)^(J+1) * (1/2:ℝ)^J :=
          mul_le_mul_of_nonneg_right (le_of_lt hMNltR) (by positivity)
      _ = 2 := h2eq
  -- log bound on J
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hJbound : (J:ℝ) ≤ (3/2) * Real.log (2*K + 2) := by
    have hlog := Real.log_le_log (by positivity : (0:ℝ) < (2:ℝ)^J) h2J_leR
    rw [Real.log_pow] at hlog
    have hlogK : Real.log K ≤ Real.log (2*K+2) :=
      Real.log_le_log hKpos (by linarith)
    have hJK : (J:ℝ) ≤ Real.log (2*K+2) / Real.log 2 := by
      rw [le_div_iff₀ hlog2pos]
      linarith
    have h13 : (1:ℝ) / Real.log 2 < 3/2 := by
      rw [div_lt_iff₀ hlog2pos]
      nlinarith [Real.log_two_gt_d9]
    have hlogKpos : 0 ≤ Real.log (2*K+2) := Real.log_nonneg (by linarith)
    calc (J:ℝ) ≤ Real.log (2*K+2) / Real.log 2 := hJK
      _ = Real.log (2*K+2) * (1/Real.log 2) := by ring
      _ ≤ Real.log (2*K+2) * (3/2) := mul_le_mul_of_nonneg_left h13.le hlogKpos
      _ = 3/2 * Real.log (2*K+2) := by ring
  have hlog1 : 1 ≤ Real.log (2*K+2) := by
    have hlog4 : 1 ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 4)]
      linarith [Real.exp_one_lt_three]
    exact le_trans hlog4 (Real.log_le_log (by norm_num : (0:ℝ) < 4) (by linarith))
  have hfin : 12 * ((J:ℝ) + 1) + 4 ≤ 100 * Real.log (2 * K + 2) := by
    have h1 : (J:ℝ) + 1 ≤ (5/2) * Real.log (2*K+2) := by linarith [hJbound, hlog1]
    nlinarith [h1, hlog1]
  -- finish
  have hS1 : (∑ j ∈ Finset.range (J+1), (1/2:ℝ)^j *
        (((Finset.Icc 1 N).filter (fun n : ℕ => t n ≤ (2:ℝ)^j / K)).card : ℝ))
      ≤ 12 * ((J:ℝ) + 1) + 2 := le_trans hsum_band hsum_band2
  calc ∑ n ∈ Finset.Icc 1 N, min 1 (1 / (K * t n))
      ≤ (∑ j ∈ Finset.range (J+1), (1/2:ℝ)^j *
            (((Finset.Icc 1 N).filter (fun n : ℕ => t n ≤ (2:ℝ)^j / K)).card : ℝ))
          + (N:ℝ) * (1/2:ℝ)^J := le_trans (le_trans stepA stepB) (le_of_eq stepC)
    _ ≤ 12 * ((J:ℝ) + 1) + 2 + 2 := add_le_add hS1 hN2J
    _ = 12 * ((J:ℝ) + 1) + 4 := by ring
    _ ≤ 100 * Real.log (2 * K + 2) := hfin

/-- Symmetric companion of `min_log_ratio_sum_le_100`: same estimate with the roles of the
two summation variables exchanged (sum over `m ≤ M` with `n` fixed). -/
lemma min_log_ratio_sum_le_100_left (M N : ℕ) (x : ℝ) (n : ℕ)
    (hM : 1 ≤ M) (hN : 1 ≤ N) (hn : 1 ≤ n) (hx : 3 / 2 ≤ x)
    (hxK : x ≤ (M : ℝ) * (N : ℝ) + 1) :
    ∑ m ∈ Finset.Icc 1 M,
      min 1 (1 / (((M : ℝ) * (N : ℝ)) * |Real.log (x / ((m : ℝ) * (n : ℝ)))|))
      ≤ 100 * Real.log (2 * (M : ℝ) * (N : ℝ) + 2) := by
  have hxK' : x ≤ (N : ℝ) * (M : ℝ) + 1 := by
    rw [mul_comm (N : ℝ) (M : ℝ)]; exact hxK
  have h := min_log_ratio_sum_le_100 N M x n hN hM hn hx hxK'
  rw [show (2 : ℝ) * (N : ℝ) * (M : ℝ) + 2 = 2 * (M : ℝ) * (N : ℝ) + 2 by ring] at h
  have hsum : (∑ m ∈ Finset.Icc 1 M,
        min 1 (1 / (((M : ℝ) * (N : ℝ)) * |Real.log (x / ((m : ℝ) * (n : ℝ)))|)))
      = (∑ m ∈ Finset.Icc 1 M,
        min 1 (1 / (((N : ℝ) * (M : ℝ)) * |Real.log (x / ((n : ℝ) * (m : ℝ)))|))) := by
    apply Finset.sum_congr rfl
    intro m _
    have hinner : (1 : ℝ) / (((M : ℝ) * (N : ℝ)) * |Real.log (x / ((m : ℝ) * (n : ℝ)))|)
        = 1 / (((N : ℝ) * (M : ℝ)) * |Real.log (x / ((n : ℝ) * (m : ℝ)))|) := by
      rw [mul_comm (M : ℝ) (N : ℝ), mul_comm (m : ℝ) (n : ℝ)]
    rw [hinner]
  rw [hsum]
  exact h

/-- Cauchy--Schwarz for a double sum with weights: for a nonnegative weight `w`,
`(∑∑ x_m y_n w_{mn})^2 ≤ (∑∑ x_m^2 w_{mn}) (∑∑ y_n^2 w_{mn})`. -/
lemma double_sum_cauchy (S T : Finset ℕ) (x y : ℕ → ℝ) (w : ℕ → ℕ → ℝ)
    (hw : ∀ m n, 0 ≤ w m n) :
    (∑ m ∈ S, ∑ n ∈ T, x m * y n * w m n) ^ 2
      ≤ (∑ m ∈ S, ∑ n ∈ T, x m ^ 2 * w m n)
        * (∑ m ∈ S, ∑ n ∈ T, y n ^ 2 * w m n) := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (S ×ˢ T)
      (fun p : ℕ × ℕ => x p.1 * Real.sqrt (w p.1 p.2))
      (fun p : ℕ × ℕ => y p.2 * Real.sqrt (w p.1 p.2))
  have hA : (∑ p ∈ S ×ˢ T,
        (x p.1 * Real.sqrt (w p.1 p.2)) * (y p.2 * Real.sqrt (w p.1 p.2)))
      = ∑ m ∈ S, ∑ n ∈ T, x m * y n * w m n := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl; intro m _
    apply Finset.sum_congr rfl; intro n _
    rw [show (x m * Real.sqrt (w m n)) * (y n * Real.sqrt (w m n))
          = x m * y n * (Real.sqrt (w m n)) ^ 2 by ring, Real.sq_sqrt (hw m n)]
  have hB : (∑ p ∈ S ×ˢ T, (x p.1 * Real.sqrt (w p.1 p.2)) ^ 2)
      = ∑ m ∈ S, ∑ n ∈ T, x m ^ 2 * w m n := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl; intro m _
    apply Finset.sum_congr rfl; intro n _
    rw [mul_pow, Real.sq_sqrt (hw m n)]
  have hC : (∑ p ∈ S ×ˢ T, (y p.2 * Real.sqrt (w p.1 p.2)) ^ 2)
      = ∑ m ∈ S, ∑ n ∈ T, y n ^ 2 * w m n := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl; intro m _
    apply Finset.sum_congr rfl; intro n _
    rw [mul_pow, Real.sq_sqrt (hw m n)]
  rw [hA, hB, hC] at hCS
  exact hCS

/-- **Bilinear error-sum bound** for the Bombieri--Vinogradov / Maynard sieve. -/
theorem bilinear_error_sum_bound (M N : ℕ) (hM : 1 ≤ M) (hN : 1 ≤ N) (x : ℝ) (hx : 3 / 2 ≤ x)
    (hxK : x ≤ (M : ℝ) * (N : ℝ) + 1) (a b : ℕ → ℂ) :
    (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        ‖a m‖ * ‖b n‖ * ((x / ((m : ℝ) * (n : ℝ))) ^ (1 / Real.log (2 * (M : ℝ) * (N : ℝ) + 2)))
          * min 1 (1 / (((M : ℝ) * (N : ℝ)) * |Real.log (x / ((m : ℝ) * (n : ℝ)))|)))
      ≤ Real.exp 1 * (100 * Real.log (2 * (M : ℝ) * (N : ℝ) + 2)) *
          Real.sqrt (∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) *
          Real.sqrt (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  set L : ℝ := Real.log (2 * (M : ℝ) * (N : ℝ) + 2) with hL
  have hLpos : 0 < L := by
    rw [hL]; apply Real.log_pos; nlinarith
  let W : ℕ → ℕ → ℝ :=
    fun m n => min 1 (1 / (((M : ℝ) * (N : ℝ)) * |Real.log (x / ((m : ℝ) * (n : ℝ)))|))
  change (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        ‖a m‖ * ‖b n‖ * ((x / ((m : ℝ) * (n : ℝ))) ^ (1 / L)) * W m n)
      ≤ Real.exp 1 * (100 * L) *
          Real.sqrt (∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) *
          Real.sqrt (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2)
  have hA : ∀ m ∈ Finset.Icc 1 M, (∑ n ∈ Finset.Icc 1 N, W m n) ≤ 100 * L := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have h := min_log_ratio_sum_le_100 M N x m hM hN hm1 hx hxK
    change (∑ n ∈ Finset.Icc 1 N,
        min 1 (1 / (((M : ℝ) * (N : ℝ)) * |Real.log (x / ((m : ℝ) * (n : ℝ)))|))) ≤ 100 * L
    rw [hL]
    exact h
  have hB : ∀ n ∈ Finset.Icc 1 N, (∑ m ∈ Finset.Icc 1 M, W m n) ≤ 100 * L := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have h := min_log_ratio_sum_le_100_left M N x n hM hN hn1 hx hxK
    change (∑ m ∈ Finset.Icc 1 M,
        min 1 (1 / (((M : ℝ) * (N : ℝ)) * |Real.log (x / ((m : ℝ) * (n : ℝ)))|))) ≤ 100 * L
    rw [hL]
    exact h
  have hWnn : ∀ m n : ℕ, 0 ≤ W m n := by
    intro m n
    change 0 ≤ min 1 (1 / (((M : ℝ) * (N : ℝ)) * |Real.log (x / ((m : ℝ) * (n : ℝ)))|))
    apply le_min
    · norm_num
    · apply div_nonneg zero_le_one
      apply mul_nonneg
      · nlinarith [hMpos, hNpos]
      · exact abs_nonneg _
  -- Step 1: the exponential factor is at most `exp 1`, uniformly.
  have hstep1 :
      (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          ‖a m‖ * ‖b n‖ * ((x / ((m : ℝ) * (n : ℝ))) ^ (1 / L)) * W m n)
        ≤ Real.exp 1 * (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
            ‖a m‖ * ‖b n‖ * W m n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro n hn
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hmnpos : 0 < (m : ℝ) * (n : ℝ) := by positivity
    have htpos : 0 < x / ((m : ℝ) * (n : ℝ)) := by positivity
    have hmn1m : (1 : ℝ) ≤ (m : ℝ) * (n : ℝ) := by nlinarith
    have hc1 : (0 : ℝ) ≤ 2 * (M : ℝ) * (N : ℝ) + 2 := by nlinarith
    have htle : x / ((m : ℝ) * (n : ℝ)) ≤ 2 * (M : ℝ) * (N : ℝ) + 2 := by
      rw [div_le_iff₀ hmnpos]
      have hmul := mul_le_mul_of_nonneg_left hmn1m hc1
      simp only [mul_one] at hmul
      nlinarith [hxK, hmul, hM1, hN1]
    have hlogle : Real.log (x / ((m : ℝ) * (n : ℝ))) ≤ Real.log (2 * (M : ℝ) * (N : ℝ) + 2) :=
      Real.log_le_log htpos htle
    have hX : (x / ((m : ℝ) * (n : ℝ))) ^ (1 / L) ≤ Real.exp 1 := by
      rw [Real.rpow_def_of_pos htpos]
      apply Real.exp_le_exp.mpr
      have h2 : Real.log (x / ((m : ℝ) * (n : ℝ))) * (1 / L)
          ≤ Real.log (2 * (M : ℝ) * (N : ℝ) + 2) * (1 / L) :=
        mul_le_mul_of_nonneg_right hlogle (by positivity)
      rw [← hL] at h2
      have h3 : L * (1 / L) = 1 := by
        rw [mul_one_div, div_self (ne_of_gt hLpos)]
      linarith [h2, h3]
    have hnn : (0 : ℝ) ≤ ‖a m‖ * ‖b n‖ := by positivity
    have hw := hWnn m n
    calc ‖a m‖ * ‖b n‖ * (x / ((m : ℝ) * (n : ℝ))) ^ (1 / L) * W m n
        = ((‖a m‖ * ‖b n‖) * (x / ((m : ℝ) * (n : ℝ))) ^ (1 / L)) * W m n := by ring
      _ ≤ ((‖a m‖ * ‖b n‖) * Real.exp 1) * W m n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX hnn) hw
      _ = Real.exp 1 * (‖a m‖ * ‖b n‖ * W m n) := by ring
  -- Step 2: the weighted sum is `≤ 100 L sqrt(Σa²) sqrt(Σb²)`.
  have hF1 : (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N, ‖a m‖ ^ 2 * W m n)
      ≤ 100 * L * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro m hm
    rw [← Finset.mul_sum]
    calc ‖a m‖ ^ 2 * (∑ n ∈ Finset.Icc 1 N, W m n) ≤ ‖a m‖ ^ 2 * (100 * L) :=
          mul_le_mul_of_nonneg_left (hA m hm) (by positivity)
      _ = (100 * L) * ‖a m‖ ^ 2 := by ring
  have hF2 : (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 * W m n)
      ≤ 100 * L * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 := by
    rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum; intro n hn
    rw [← Finset.mul_sum]
    calc ‖b n‖ ^ 2 * (∑ m ∈ Finset.Icc 1 M, W m n) ≤ ‖b n‖ ^ 2 * (100 * L) :=
          mul_le_mul_of_nonneg_left (hB n hn) (by positivity)
      _ = (100 * L) * ‖b n‖ ^ 2 := by ring
  have hCS := double_sum_cauchy (Finset.Icc 1 M) (Finset.Icc 1 N)
      (fun m => ‖a m‖) (fun n => ‖b n‖) W hWnn
  have hB2nn : 0 ≤ ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 * W m n :=
    Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun n _ => by positivity
  have hF1nn : 0 ≤ 100 * L * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2 := by positivity
  have hsq1 : Real.sqrt (∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) ^ 2
      = ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun m _ => by positivity)
  have hsq2 : Real.sqrt (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) ^ 2
      = ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun n _ => by positivity)
  have hsqform : (100 * L * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2)
        * (100 * L * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2)
      = (100 * L * Real.sqrt (∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2)
          * Real.sqrt (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2)) ^ 2 := by
    have e1 : (100 * L * Real.sqrt (∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2)
          * Real.sqrt (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2)) ^ 2
        = (100 * L) ^ 2 * Real.sqrt (∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2) ^ 2
          * Real.sqrt (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) ^ 2 := by ring
    rw [e1, hsq1, hsq2]; ring
  have hmain2 : (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N, ‖a m‖ * ‖b n‖ * W m n) ^ 2
      ≤ (100 * L * Real.sqrt (∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2)
          * Real.sqrt (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2)) ^ 2 := by
    refine le_trans hCS ?_
    refine le_trans (mul_le_mul hF1 hF2 hB2nn hF1nn) ?_
    rw [hsqform]
  have hT2nn : 0 ≤ ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
      ‖a m‖ * ‖b n‖ * W m n :=
    Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun n _ => by positivity
  have hc_nn : 0 ≤ 100 * L * Real.sqrt (∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2)
      * Real.sqrt (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) := by positivity
  have hT2le : (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N, ‖a m‖ * ‖b n‖ * W m n)
      ≤ 100 * L * Real.sqrt (∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2)
          * Real.sqrt (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) := by
    have hs := sq_le_sq.mp hmain2
    rwa [abs_of_nonneg hT2nn, abs_of_nonneg hc_nn] at hs
  calc (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          ‖a m‖ * ‖b n‖ * ((x / ((m : ℝ) * (n : ℝ))) ^ (1 / L)) * W m n)
      ≤ Real.exp 1 * (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          ‖a m‖ * ‖b n‖ * W m n) := hstep1
    _ ≤ Real.exp 1 * (100 * L * Real.sqrt (∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2)
          * Real.sqrt (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hT2le (Real.exp_pos 1).le
    _ = Real.exp 1 * (100 * L) * Real.sqrt (∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2)
          * Real.sqrt (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) := by ring

end Commons.NumberTheory.BombieriVinogradov