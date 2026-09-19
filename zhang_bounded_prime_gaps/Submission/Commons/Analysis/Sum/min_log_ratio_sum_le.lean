import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Submission.Commons.Analysis.InfiniteSum.rpowDiff_loglog_add_log_tendsto

open Finset
open scoped BigOperators

namespace Commons.Analysis.Sum

/-! ### Helper lemmas -/

/-- `min 1 (1/s) ≤ 1/max s 1` for every real `s`. -/
lemma min_one_div_le_inv_max (s : ℝ) : min 1 (1 / s) ≤ 1 / max s 1 := by
  by_cases h : s ≤ 1
  · rw [max_eq_right h]
    simp
  · rw [max_eq_left (le_of_lt (not_le.mp h))]
    exact min_le_right 1 (1/s)

/-- The discrete layer-cake estimate: for `s ≥ 1` and every `J`,
`1/s` is bounded by a weighted count of the dyadic levels `j ≤ J` at which `s ≤ 2^j`,
plus the tail term `(1/2)^J`. -/
lemma inv_le_sum_range_pow (s : ℝ) (hs : 1 ≤ s) :
    ∀ J : ℕ, 1 / s ≤
      (∑ j ∈ Finset.range (J + 1), (if s ≤ (2 : ℝ) ^ j then (1 / 2 : ℝ) ^ j else 0))
        + (1 / 2 : ℝ) ^ J := by
  intro J
  induction J with
  | zero =>
      have hnn : (0 : ℝ) ≤ ∑ j ∈ Finset.range 1,
          (if s ≤ (2:ℝ)^j then (1/2:ℝ)^j else 0) :=
        Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)
      have h1 : 1 / s ≤ 1 := (div_le_one (by linarith : (0:ℝ) < s)).mpr hs
      rw [pow_zero]
      linarith
  | succ J ih =>
      rw [Finset.sum_range_succ]
      by_cases hcase : s ≤ (2:ℝ)^(J+1)
      · rw [if_pos hcase]
        have hid : (1/2:ℝ)^(J+1) + (1/2:ℝ)^(J+1) = (1/2:ℝ)^J := by
          rw [pow_succ]; ring
        linarith [ih, hid]
      · rw [if_neg hcase]
        have hlt : (2:ℝ)^(J+1) < s := not_le.mp hcase
        have hA : (1/2:ℝ)^(J+1) * (2:ℝ)^(J+1) = 1 := by
          rw [← mul_pow]; norm_num
        have hB : (1/2:ℝ)^(J+1) * (2:ℝ)^(J+1) < (1/2:ℝ)^(J+1) * s :=
          mul_lt_mul_of_pos_left hlt (by positivity)
        rw [hA] at hB
        have hinv : 1/s < (1/2:ℝ)^(J+1) := by
          rw [div_lt_iff₀ (by linarith : (0:ℝ) < s)]
          exact hB
        have hnn : (0:ℝ) ≤ ∑ j ∈ Finset.range (J+1),
            (if s ≤ (2:ℝ)^j then (1/2:ℝ)^j else 0) :=
          Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)
        linarith

/-- Counting lattice points: a finset of naturals lying in the real interval `[a,b]`
has at most `b - a + 1` elements. -/
lemma card_le_of_forall_mem_Icc_real {S : Finset ℕ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ n ∈ S, a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b) : (S.card : ℝ) ≤ b - a + 1 := by
  rcases S.eq_empty_or_nonempty with hS | hne
  · rw [hS, Finset.card_empty]
    simp only [Nat.cast_zero]
    linarith
  · have hmin : S.min' hne ∈ S := Finset.min'_mem S hne
    have hmax : S.max' hne ∈ S := Finset.max'_mem S hne
    have hsub : S ⊆ Finset.Icc (S.min' hne) (S.max' hne) := by
      intro n hn
      rw [Finset.mem_Icc]
      exact ⟨Finset.min'_le S n hn, Finset.le_max' S n hn⟩
    have hcard : S.card ≤ (Finset.Icc (S.min' hne) (S.max' hne)).card :=
      Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    have hle : S.min' hne ≤ S.max' hne := Finset.min'_le S _ hmax
    have ha : a ≤ ((S.min' hne : ℕ) : ℝ) := (h _ hmin).1
    have hb : ((S.max' hne : ℕ) : ℝ) ≤ b := (h _ hmax).2
    have hcast : ((S.max' hne + 1 - S.min' hne : ℕ) : ℝ)
        = ((S.max' hne : ℕ) : ℝ) + 1 - ((S.min' hne : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : S.min' hne ≤ S.max' hne + 1),
        Nat.cast_add, Nat.cast_one]
    have hfin : (S.card : ℝ) ≤ ((S.max' hne + 1 - S.min' hne : ℕ) : ℝ) := by
      exact_mod_cast hcard
    rw [hcast] at hfin
    linarith

/-- If `|log y| ≤ T` with `y > 0` then `y` lies between `exp (-T)` and `exp T`. -/
lemma exp_neg_le_and_le_exp_of_abs_log_le {y T : ℝ} (hy : 0 < y)
    (h : |Real.log y| ≤ T) : Real.exp (-T) ≤ y ∧ y ≤ Real.exp T := by
  rw [abs_le] at h
  exact ⟨(Real.le_log_iff_exp_le hy).mp h.1, (Real.log_le_iff_le_exp hy).mp h.2⟩

/-- For `0 ≤ T ≤ 1`, `exp T - exp (-T) ≤ 6 T`. -/
lemma exp_sub_exp_neg_le_six_mul {T : ℝ} (h0 : 0 ≤ T) (h1 : T ≤ 1) :
    Real.exp T - Real.exp (-T) ≤ 6 * T := by
  have hkey : Real.exp (-T) = Real.exp T * Real.exp (-(2 * T)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : 1 - Real.exp (-(2 * T)) ≤ 2 * T := by
    have := Real.one_sub_le_exp_neg (2 * T)
    linarith
  have h3 : 0 ≤ 1 - Real.exp (-(2 * T)) := by
    have hle : Real.exp (-(2*T)) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    linarith
  have h4 : Real.exp T ≤ 3 := by
    have : Real.exp T ≤ Real.exp 1 := Real.exp_le_exp.mpr h1
    linarith [Real.exp_one_lt_three]
  rw [hkey]
  have hrw : Real.exp T - Real.exp T * Real.exp (-(2 * T))
      = Real.exp T * (1 - Real.exp (-(2 * T))) := by ring
  rw [hrw]
  calc Real.exp T * (1 - Real.exp (-(2 * T))) ≤ 3 * (2 * T) :=
        mul_le_mul h4 h2 h3 (by norm_num)
    _ = 6 * T := by ring

/-- Counting bound: the number of `n ∈ {1,…,N}` with `|log (x/(m n))| ≤ T`
is at most `(x/m)(e^T - e^{-T}) + 1`. -/
lemma card_filter_abs_log_le (N : ℕ) (x : ℝ) (m : ℕ) (hm : 1 ≤ m) (hx : 3/2 ≤ x)
    (T : ℝ) (hT : 0 ≤ T) :
    (((Finset.Icc 1 N).filter (fun n : ℕ => |Real.log (x / ((m:ℝ)*(n:ℝ)))| ≤ T)).card : ℝ)
      ≤ (x / (m:ℝ)) * (Real.exp T - Real.exp (-T)) + 1 := by
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hxpos : 0 < x := by linarith
  have hmem : ∀ n ∈ (Finset.Icc 1 N).filter
        (fun n : ℕ => |Real.log (x / ((m:ℝ)*(n:ℝ)))| ≤ T),
      x * Real.exp (-T) / (m:ℝ) ≤ (n:ℝ) ∧ (n:ℝ) ≤ x * Real.exp T / (m:ℝ) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, _⟩, hlog⟩ := hn
    have hmn : (0:ℝ) < (m:ℝ) * (n:ℝ) := by
      have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
      positivity
    have hy : 0 < x / ((m:ℝ)*(n:ℝ)) := by positivity
    obtain ⟨hlo, hhi⟩ := exp_neg_le_and_le_exp_of_abs_log_le hy hlog
    constructor
    · rw [div_le_iff₀ hmpos]
      have hxle : x ≤ Real.exp T * ((m:ℝ)*(n:ℝ)) := (div_le_iff₀ hmn).mp hhi
      have hstep : x / Real.exp T ≤ (m:ℝ)*(n:ℝ) := by
        rw [div_le_iff₀ (Real.exp_pos T)]
        nlinarith [hxle]
      have hexp : x * Real.exp (-T) = x / Real.exp T := by
        rw [Real.exp_neg]; ring
      rw [hexp]
      nlinarith [hstep]
    · rw [le_div_iff₀ hmpos]
      have hlex : Real.exp (-T) * ((m:ℝ)*(n:ℝ)) ≤ x := (le_div_iff₀ hmn).mp hlo
      have hmul := mul_le_mul_of_nonneg_left hlex (le_of_lt (Real.exp_pos T))
      have hmnle : ((m:ℝ)*(n:ℝ)) ≤ Real.exp T * x := by
        rw [show Real.exp T * (Real.exp (-T) * ((m:ℝ)*(n:ℝ))) = (m:ℝ)*(n:ℝ) by
              rw [← mul_assoc, ← Real.exp_add,
                show T + -T = 0 by ring, Real.exp_zero, one_mul]] at hmul
        exact hmul
      nlinarith [hmnle]
  have hab : x * Real.exp (-T) / (m:ℝ) ≤ x * Real.exp T / (m:ℝ) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hmpos)
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hxpos)
    exact Real.exp_le_exp.mpr (by linarith)
  have hmain := card_le_of_forall_mem_Icc_real hab hmem
  rw [show x * Real.exp T / (m:ℝ) - x * Real.exp (-T) / (m:ℝ)
      = (x / (m:ℝ)) * (Real.exp T - Real.exp (-T)) by ring] at hmain
  linarith [hmain]

/-- `∑_{j<n} (1/2)^j ≤ 2`. -/
lemma sum_range_half_le_two (n : ℕ) : (∑ j ∈ Finset.range n, (1/2:ℝ)^j) ≤ 2 := by
  rw [geom_sum_eq (by norm_num : ((1:ℝ)/2) ≠ 1)]
  have hpow : ((1:ℝ)/2)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hnn : 0 ≤ ((1:ℝ)/2)^n := by positivity
  rw [div_le_iff_of_neg (by norm_num : ((1:ℝ)/2 - 1) < 0)]
  nlinarith [hpow, hnn]

/-- **Main lemma**: the `min(1, 1/((|log|)·K))` sum over `n ≤ N` is `O(log K)`. -/
theorem min_log_ratio_sum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (M N : ℕ) (x : ℝ) (m : ℕ),
      1 ≤ M → 1 ≤ N → 1 ≤ m → 3 / 2 ≤ x → x ≤ (M : ℝ) * (N : ℝ) + 1 →
      ∑ n ∈ Finset.Icc 1 N,
        min 1 (1 / (((M : ℝ) * (N : ℝ)) * |Real.log (x / ((m : ℝ) * (n : ℝ)))|))
      ≤ C * Real.log (2 * (M : ℝ) * (N : ℝ) + 2) := by
  refine ⟨100, by norm_num, ?_⟩
  intro M N x m hM hN hm hx hxK
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

end Commons.Analysis.Sum