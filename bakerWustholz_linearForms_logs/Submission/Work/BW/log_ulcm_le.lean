import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.ulcm_le_three_pow
import Submission.Work.BW.log_ulcm_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Hanson's bound for `lcm(1,…,k)` in logarithmic form

The target of this file is

`theorem log_ulcm_le (k : ℕ) (hk : 19 ≤ k) : Real.log (ulcm k) ≤ 1.1 * k`,

the form in which BW (13) consumes Hanson's bound `lcm(1,…,k) ≤ 3^k`.
The proof is Hanson's (Canad. Math. Bull. **15** (1972)):

* Hanson's divisibility `ulcm n * ∏_{i ≤ n} ⌊n/syl i⌋! ∣ n!` (`Work.BW.syl_divisibility`)
  turns the problem into bounding the logarithm of `C(n) = n!/∏_{i ≤ n}⌊n/syl i⌋!`.
* `log C(n) ≤ n * Lw n + (sylK n + 1) log n + log (n+1)`, where
  `Lw n = ∑_{i : syl i ≤ n} log (syl i)/syl i` and `sylK n = #{i : syl i ≤ n}`
  (the entropy bound below).
* `Lw n ≤ 1.083` (decreasing doubly-exponentially tail of the Sylvester weights) and
  `sylK n ≤ log n / log 2 + 1`; the explicit small logarithmic estimates finish the job
  (`6 log n + log (n+1) ≤ 0.017 n` etc.).
* `k < 4096` is a kernel-checked finite computation (`Work.BW.ulcm_le_three_pow_small`).
-/

namespace Work.BW

open Finset

/-! ## The active Sylvester index set -/

lemma mem_sylAct {n i : ℕ} : i ∈ sylAct n ↔ i ≤ n ∧ syl i ≤ n := by
  simp [sylAct]

lemma sylAct_downclosed {n i j : ℕ} (hi : i ∈ sylAct n) (hj : j ≤ i) : j ∈ sylAct n := by
  rw [mem_sylAct] at hi ⊢
  exact ⟨le_trans hj hi.1, le_trans (syl_mono hj) hi.2⟩

lemma range_sylK_subset_sylAct (n : ℕ) : Finset.range (sylK n) ⊆ sylAct n := by
  intro i hi
  by_contra hcon
  have hsub : sylAct n ⊆ Finset.range i := by
    intro j hj
    rw [Finset.mem_range]
    by_contra hji
    push_neg at hji
    exact hcon (sylAct_downclosed hj hji)
  have hcard : sylK n ≤ i := by
    have := Finset.card_le_card hsub
    simpa [sylK, Finset.card_range] using this
  have := Finset.mem_range.mp hi
  omega

lemma sylAct_subset_range_sylK (n : ℕ) : sylAct n ⊆ Finset.range (sylK n) := by
  intro j hj
  rw [Finset.mem_range]
  have hsub : Finset.range (j + 1) ⊆ sylAct n := by
    intro i hi
    rw [Finset.mem_range] at hi
    exact sylAct_downclosed hj (by omega)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard
  simp only [sylK]
  omega

lemma sylAct_eq_range_sylK (n : ℕ) : sylAct n = Finset.range (sylK n) :=
  Finset.Subset.antisymm (sylAct_subset_range_sylK n) (range_sylK_subset_sylAct n)

lemma Lw_eq_sum_sylAct (n : ℕ) :
    Lw n = ∑ i ∈ sylAct n, Real.log (syl i) / (syl i : ℝ) := rfl

lemma sylAct_card_cast (n : ℕ) : (((sylAct n).card : ℕ) : ℝ) = (sylK n : ℝ) := rfl

lemma one_le_sylK {n : ℕ} (hn : 2 ≤ n) : 1 ≤ sylK n := by
  have h0 : 0 ∈ sylAct n := by
    rw [mem_sylAct]
    exact ⟨by omega, by simpa using hn⟩
  have := Finset.card_pos.mpr ⟨0, h0⟩
  simpa [sylK] using this

lemma syl_sylK_gt (n : ℕ) : n < syl (sylK n) := by
  by_contra h
  push_neg at h
  have hKmem : sylK n ∈ sylAct n := by
    rw [mem_sylAct]
    refine ⟨?_, h⟩
    have := syl_ge (sylK n)
    omega
  have := sylAct_subset_range_sylK n hKmem
  exact absurd (Finset.mem_range.mp this) (lt_irrefl _)

lemma sum_sylAct_inv_ge {n : ℕ} (hn : 2 ≤ n) :
    1 - 1 / (n : ℝ) ≤ ∑ i ∈ sylAct n, 1 / (syl i : ℝ) := by
  have hsub : Finset.range (sylK n) ⊆ sylAct n := range_sylK_subset_sylAct n
  have hmono : (∑ i ∈ Finset.range (sylK n), 1 / (syl i : ℝ)) ≤
      ∑ i ∈ sylAct n, 1 / (syl i : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
  have hsum : (∑ i ∈ Finset.range (sylK n), 1 / (syl i : ℝ)) =
      1 - 1 / ((syl (sylK n) : ℝ) - 1) := by
    set K := sylK n with hK
    induction K with
    | zero => norm_num
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        have hsk : (syl k : ℝ) ≠ 0 := by
          have := syl_two_le k
          exact_mod_cast (by omega : syl k ≠ 0)
        have hsk1 : (syl k : ℝ) - 1 ≠ 0 := by
          have h2 : (1:ℝ) < (syl k : ℝ) := by
            have := syl_two_le k
            exact_mod_cast (by omega : (1:ℕ) < syl k)
          linarith
        have hsub : ((syl (k+1) : ℕ) : ℝ) - 1 = (syl k : ℝ) * ((syl k : ℝ) - 1) := by
          rw [show syl (k+1) = syl k * (syl k - 1) + 1 from rfl, Nat.cast_add, Nat.cast_mul,
            Nat.cast_one, Nat.cast_sub (by have := syl_two_le k; omega : 1 ≤ syl k)]
          ring
        rw [hsub]
        field_simp
        ring
  have hcast : (n : ℝ) ≤ (syl (sylK n) : ℝ) - 1 := by
    have h1 : ((n + 1 : ℕ) : ℝ) ≤ (syl (sylK n) : ℝ) := by
      exact_mod_cast (show (n + 1 : ℕ) ≤ syl (sylK n) by have := syl_sylK_gt n; omega)
    push_cast at h1
    linarith
  have hnpos : (0 : ℝ) < n := by positivity
  rw [hsum] at hmono
  have hle : 1 / ((syl (sylK n) : ℝ) - 1) ≤ 1 / (n : ℝ) :=
    one_div_le_one_div_of_le hnpos hcast
  linarith

/-! ## `sylK n` versus `log n` -/

lemma two_pow_le_syl : ∀ i : ℕ, 2 ^ i ≤ syl i := by
  intro i
  induction i with
  | zero => decide
  | succ i ih =>
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0
        decide
      · have hstep : 2 * syl i ≤ syl i * (syl i - 1) + 1 := by
          have h2 : 2 ≤ syl i - 1 := by have := syl_ge i; omega
          calc 2 * syl i = syl i * 2 := by ring
            _ ≤ syl i * (syl i - 1) := Nat.mul_le_mul_left _ h2
            _ ≤ syl i * (syl i - 1) + 1 := Nat.le_succ _
        calc 2 ^ (i + 1) = 2 ^ i * 2 := by rw [pow_succ]
          _ = 2 * 2 ^ i := by ring
          _ ≤ 2 * syl i := Nat.mul_le_mul_left 2 ih
          _ ≤ syl i * (syl i - 1) + 1 := hstep

lemma sylK_le_log (n : ℕ) (hn : 1 ≤ n) :
    (sylK n : ℝ) ≤ Real.log n / Real.log 2 + 1 := by
  rcases Nat.eq_zero_or_pos (sylK n) with h0 | hpos
  · rw [h0]
    push_cast
    have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hnpos : (0:ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    have : 0 ≤ Real.log n / Real.log 2 := div_nonneg hnpos (le_of_lt h2)
    linarith
  · have hmem : sylK n - 1 ∈ sylAct n :=
      range_sylK_subset_sylAct n (Finset.mem_range.mpr (by omega))
    have hsyl : syl (sylK n - 1) ≤ n := (mem_sylAct.mp hmem).2
    have h2 : 2 ^ (sylK n - 1) ≤ syl (sylK n - 1) := two_pow_le_syl _
    have h3 : (2:ℝ) ^ (sylK n - 1) ≤ (n:ℝ) := by
      have h4 : ((2 ^ (sylK n - 1) : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast le_trans h2 hsyl
      simpa using h4
    have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have h5 : ((sylK n - 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log n := by
      have h6 := Real.log_le_log (by positivity : (0:ℝ) < (2:ℝ) ^ (sylK n - 1)) h3
      rwa [Real.log_pow] at h6
    have h7 : ((sylK n - 1 : ℕ) : ℝ) ≤ Real.log n / Real.log 2 := by
      rw [le_div_iff₀ hlog2]
      linarith
    have h8 : ((sylK n - 1 : ℕ) : ℝ) = (sylK n : ℝ) - 1 := by
      rw [Nat.cast_sub hpos]
      norm_num
    linarith

/-! ## The Sylvester log-weight is at most `1.083` -/

private noncomputable def aw (i : ℕ) : ℝ := Real.log (syl i) / (syl i : ℝ)

private lemma aw_nonneg (i : ℕ) : 0 ≤ aw i := by
  have h1 : (1:ℝ) ≤ (syl i : ℝ) := by
    have := syl_two_le i
    exact_mod_cast (show (1:ℕ) ≤ syl i by omega)
  rw [aw]
  exact div_nonneg (Real.log_nonneg h1) (by linarith)

private lemma syl_zero_val : syl 0 = 2 := rfl
private lemma syl_one_val : syl 1 = 3 := rfl
private lemma syl_two_val : syl 2 = 7 := rfl
private lemma syl_three_val : syl 3 = 43 := rfl
private lemma syl_four_val : syl 4 = 1807 := rfl
private lemma syl_five_val : syl 5 = 3263443 := rfl
private lemma syl_six_val : syl 6 = 10650056950807 := rfl

private lemma log7_le : Real.log 7 ≤ (73/26 : ℝ) * 0.6931471808 := by
  have hp : (7:ℝ)^26 ≤ (2:ℝ)^73 := by norm_num
  have h := Real.log_le_log (by norm_num : (0:ℝ) < (7:ℝ)^26) hp
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  nlinarith [h, Real.log_two_lt_d9]

private lemma log43_le : Real.log 43 ≤ (38/7 : ℝ) * 0.6931471808 := by
  have hp : (43:ℝ)^7 ≤ (2:ℝ)^38 := by norm_num
  have h := Real.log_le_log (by norm_num : (0:ℝ) < (43:ℝ)^7) hp
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  nlinarith [h, Real.log_two_lt_d9]

private lemma log1807_le : Real.log 1807 ≤ (65/6 : ℝ) * 0.6931471808 := by
  have hp : (1807:ℝ)^6 ≤ (2:ℝ)^65 := by norm_num
  have h := Real.log_le_log (by norm_num : (0:ℝ) < (1807:ℝ)^6) hp
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  nlinarith [h, Real.log_two_lt_d9]

private lemma log3263443_le : Real.log 3263443 ≤ (65/3 : ℝ) * 0.6931471808 := by
  have hp : (3263443:ℝ)^3 ≤ (2:ℝ)^65 := by norm_num
  have h := Real.log_le_log (by norm_num : (0:ℝ) < (3263443:ℝ)^3) hp
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  nlinarith [h, Real.log_two_lt_d9]

private lemma aw_zero_le : aw 0 ≤ 0.6931471808 / 2 := by
  have h : Real.log (2:ℝ) ≤ 0.6931471808 := le_of_lt Real.log_two_lt_d9
  rw [aw, syl_zero_val]
  linarith

private lemma aw_one_le : aw 1 ≤ 1.0986122888 / 3 := by
  have h : Real.log (3:ℝ) ≤ 1.0986122888 := le_of_lt Real.log_three_lt_d9
  rw [aw, syl_one_val]
  linarith

private lemma aw_two_le : aw 2 ≤ ((73/26 : ℝ) * 0.6931471808) / 7 := by
  have h := log7_le
  rw [aw, syl_two_val]
  linarith

private lemma aw_three_le : aw 3 ≤ ((38/7 : ℝ) * 0.6931471808) / 43 := by
  have h := log43_le
  rw [aw, syl_three_val]
  linarith

private lemma aw_four_le : aw 4 ≤ ((65/6 : ℝ) * 0.6931471808) / 1807 := by
  have h := log1807_le
  rw [aw, syl_four_val]
  linarith

private lemma aw_five_le : aw 5 ≤ ((65/3 : ℝ) * 0.6931471808) / 3263443 := by
  have h := log3263443_le
  rw [aw, syl_five_val]
  linarith

private lemma syl_succ_sq_le (i : ℕ) : (syl i : ℝ) ^ 2 ≤ 2 * (syl (i + 1) : ℝ) := by
  have h1 : 1 ≤ syl i := by have := syl_two_le i; omega
  have hcast : (syl (i+1) : ℝ) = (syl i : ℝ) * ((syl i : ℝ) - 1) + 1 := by
    rw [show syl (i+1) = syl i * (syl i - 1) + 1 from rfl, Nat.cast_add, Nat.cast_mul,
      Nat.cast_one, Nat.cast_sub h1]
    ring
  rw [hcast]
  have h2 : (2:ℝ) ≤ (syl i : ℝ) := by exact_mod_cast syl_two_le i
  nlinarith [sq_nonneg ((syl i : ℝ) - 1)]

private lemma syl_succ_le_sq (i : ℕ) : (syl (i + 1) : ℝ) ≤ (syl i : ℝ) ^ 2 := by
  have h1 : 1 ≤ syl i := by have := syl_two_le i; omega
  have hcast : (syl (i+1) : ℝ) = (syl i : ℝ) * ((syl i : ℝ) - 1) + 1 := by
    rw [show syl (i+1) = syl i * (syl i - 1) + 1 from rfl, Nat.cast_add, Nat.cast_mul,
      Nat.cast_one, Nat.cast_sub h1]
    ring
  rw [hcast]
  have h2 : (1:ℝ) ≤ (syl i : ℝ) := by exact_mod_cast h1
  nlinarith [sq_nonneg ((syl i : ℝ) - 1)]

private lemma aw_succ_le_half {i : ℕ} (hi : 4 ≤ i) : aw (i + 1) ≤ (1/2) * aw i := by
  have hsyl4 : (1807:ℝ) ≤ (syl i : ℝ) := by
    have h := syl_mono hi
    rw [syl_four_val] at h
    exact_mod_cast h
  have hsi0 : (0:ℝ) < (syl i : ℝ) := by have := syl_two_le i; exact_mod_cast (by omega : 0 < syl i)
  have hlogi : 0 ≤ Real.log (syl i) := by
    refine Real.log_nonneg ?_
    exact_mod_cast (show (1:ℕ) ≤ syl i by have := syl_two_le i; omega)
  have hspos : (0:ℝ) < (syl (i+1) : ℝ) := by
    have := syl_two_le (i+1)
    exact_mod_cast (by omega : 0 < syl (i+1))
  have hlog : Real.log (syl (i+1)) ≤ 2 * Real.log (syl i) := by
    have h := Real.log_le_log hspos (syl_succ_le_sq i)
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hden : (syl i : ℝ) ^ 2 / 2 ≤ (syl (i+1) : ℝ) := by
    have := syl_succ_sq_le i
    linarith
  have hcore : Real.log (syl (i+1)) * (syl i : ℝ)^2 ≤ 4 * Real.log (syl i) * (syl (i+1) : ℝ) := by
    nlinarith [hlog, hden, hlogi]
  have hgoal : Real.log (syl (i+1)) / (syl (i+1) : ℝ) ≤
      (4 / (syl i : ℝ)) * (Real.log (syl i) / (syl i : ℝ)) := by
    have hspos2 : (0:ℝ) < (syl i : ℝ)^2 := by nlinarith [hsi0]
    rw [div_le_iff₀ hspos]
    rw [show (4 / (syl i : ℝ) * (Real.log (syl i) / (syl i : ℝ))) * (syl (i+1) : ℝ) =
        4 * Real.log (syl i) * (syl (i+1) : ℝ) / (syl i : ℝ)^2 by
      field_simp]
    rw [le_div_iff₀ hspos2]
    linarith [hcore]
  have h4 : 4 / (syl i : ℝ) ≤ 1/2 := by
    rw [div_le_iff₀ hsi0]
    linarith
  calc aw (i+1) = Real.log (syl (i+1)) / (syl (i+1) : ℝ) := rfl
    _ ≤ (4 / (syl i : ℝ)) * (Real.log (syl i) / (syl i : ℝ)) := hgoal
    _ = (4 / (syl i : ℝ)) * aw i := rfl
    _ ≤ (1/2) * aw i := mul_le_mul_of_nonneg_right h4 (aw_nonneg i)

private lemma aw_geo (j : ℕ) : aw (5 + j) ≤ (1/2:ℝ)^j * aw 5 := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hstep : aw (5 + j + 1) ≤ (1/2) * aw (5 + j) := by
        have := aw_succ_le_half (i := 5 + j) (by omega)
        simpa [show 5 + j + 1 = (5 + j) + 1 from rfl] using this
      calc aw (5 + (j + 1)) = aw (5 + j + 1) := by ring_nf
        _ ≤ (1/2) * aw (5 + j) := hstep
        _ ≤ (1/2) * ((1/2:ℝ)^j * aw 5) := by
            have := aw_nonneg (5 + j)
            nlinarith [ih]
        _ = (1/2:ℝ)^(j+1) * aw 5 := by rw [pow_succ]; ring

private lemma geom_half (m : ℕ) : (∑ j ∈ Finset.range m, (1/2:ℝ)^j) = 2 - 2*(1/2)^m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

private lemma geom_half_le (m : ℕ) : (∑ j ∈ Finset.range m, (1/2:ℝ)^j) ≤ 2 := by
  rw [geom_half m]
  have h1 : (0:ℝ) ≤ 2*(1/2:ℝ)^m := by positivity
  linarith

private lemma tail_le (m : ℕ) : (∑ j ∈ Finset.range m, aw (5 + j)) ≤ 2 * aw 5 := by
  have h1 : (∑ j ∈ Finset.range m, aw (5+j)) ≤ ∑ j ∈ Finset.range m, (1/2:ℝ)^j * aw 5 :=
    Finset.sum_le_sum fun j _ => aw_geo j
  have h2 : (∑ j ∈ Finset.range m, (1/2:ℝ)^j * aw 5) =
      (∑ j ∈ Finset.range m, (1/2:ℝ)^j) * aw 5 := by
    rw [Finset.sum_mul]
  have h3 := geom_half_le m
  have h4 := aw_nonneg 5
  rw [h2] at h1
  nlinarith [h1, h3, h4]

private lemma five_le : (∑ i ∈ Finset.range 5, aw i) ≤ 1.0825 := by
  have h0 := aw_zero_le
  have h1 := aw_one_le
  have h2 := aw_two_le
  have h3 := aw_three_le
  have h4 := aw_four_le
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith

private lemma aw5_small : 2 * aw 5 ≤ 0.00001 := by
  have h := aw_five_le
  linarith

theorem Lw_le (n : ℕ) : Lw n ≤ 1.083 := by
  have hle : Lw n ≤ ∑ i ∈ Finset.range (n + 1), aw i := by
    unfold Lw aw
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro i _ _
    exact aw_nonneg i
  rcases Nat.lt_or_ge n 5 with hn | hn
  · have h2 : (∑ i ∈ Finset.range (n+1), aw i) ≤ ∑ i ∈ Finset.range 5, aw i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun i _ _ => aw_nonneg i)
    linarith [hle, h2, five_le]
  · obtain ⟨m, hm⟩ : ∃ m, n + 1 = 5 + m := ⟨n + 1 - 5, by omega⟩
    rw [hm, Finset.sum_range_add] at hle
    have h3 := tail_le m
    have h5 := aw5_small
    linarith [hle, five_le, h3, h5]


/-! ## The entropy bound (Hanson's `log C(n)`) -/

private lemma per_term_le {n i : ℕ} (hi : i ∈ sylAct n) :
    ((n / syl i : ℕ) : ℝ) * Real.log ((n : ℝ) / ((n / syl i : ℕ) : ℝ))
      ≤ ((n / syl i : ℕ) : ℝ) * Real.log (syl i) + 1 := by
  have hsi : syl i ≤ n := (mem_sylAct.mp hi).2
  have hsinat : 0 < syl i := by have := syl_two_le i; omega
  have hsiR : (0:ℝ) < (syl i : ℝ) := by exact_mod_cast hsinat
  have hqposnat : 1 ≤ n / syl i := (Nat.le_div_iff_mul_le hsinat).mpr (by simpa using hsi)
  have hqR : (0:ℝ) < ((n / syl i : ℕ) : ℝ) := by
    have h2 : ((1:ℕ) : ℝ) ≤ ((n / syl i : ℕ) : ℝ) := by exact_mod_cast hqposnat
    linarith
  have hxlt : (n : ℝ) / (syl i : ℝ) < ((n / syl i : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hsiR]
    have h1 : n < (n / syl i + 1) * syl i :=
      (Nat.div_lt_iff_lt_mul hsinat).mp (Nat.lt_succ_self _)
    exact_mod_cast h1
  have hxq : ((n : ℝ) / (syl i : ℝ)) / ((n / syl i : ℕ) : ℝ) ≤
      1 + 1 / ((n / syl i : ℕ) : ℝ) := by
    rw [div_le_iff₀ hqR]
    have heq : (1 + 1 / ((n / syl i : ℕ) : ℝ)) * ((n / syl i : ℕ) : ℝ) =
        ((n / syl i : ℕ) : ℝ) + 1 := by
      field_simp
    rw [heq]
    exact le_of_lt hxlt
  have hnpos : (0:ℝ) < (n:ℝ) := by
    have h2 := syl_two_le i
    exact_mod_cast (by omega : 0 < n)
  have hdivpos : (0:ℝ) < ((n : ℝ) / (syl i : ℝ)) / ((n / syl i : ℕ) : ℝ) :=
    div_pos (div_pos hnpos hsiR) hqR
  have hlog : Real.log (((n : ℝ) / (syl i : ℝ)) / ((n / syl i : ℕ) : ℝ)) ≤
      1 / ((n / syl i : ℕ) : ℝ) := by
    refine le_trans (Real.log_le_log hdivpos hxq) ?_
    exact log_one_add_le _ (one_div_pos.mpr hqR)
  have hdecomp : (n : ℝ) / ((n / syl i : ℕ) : ℝ) =
      (syl i : ℝ) * (((n : ℝ) / (syl i : ℝ)) / ((n / syl i : ℕ) : ℝ)) := by
    field_simp
  have hsplit : Real.log ((n : ℝ) / ((n / syl i : ℕ) : ℝ)) =
      Real.log (syl i) + Real.log (((n : ℝ) / (syl i : ℝ)) / ((n / syl i : ℕ) : ℝ)) := by
    rw [hdecomp, Real.log_mul (ne_of_gt hsiR) (ne_of_gt hdivpos)]
  calc ((n / syl i : ℕ) : ℝ) * Real.log ((n : ℝ) / ((n / syl i : ℕ) : ℝ))
      = ((n / syl i : ℕ) : ℝ) * Real.log (syl i)
        + ((n / syl i : ℕ) : ℝ) *
          Real.log (((n : ℝ) / (syl i : ℝ)) / ((n / syl i : ℕ) : ℝ)) := by
        rw [hsplit]; ring
    _ ≤ ((n / syl i : ℕ) : ℝ) * Real.log (syl i) +
        ((n / syl i : ℕ) : ℝ) * (1 / ((n / syl i : ℕ) : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hlog (le_of_lt hqR)
        linarith
    _ = ((n / syl i : ℕ) : ℝ) * Real.log (syl i) + 1 := by
        rw [mul_one_div, div_self (ne_of_gt hqR)]

theorem log_sylBlocks_le (n : ℕ) (hn : 3 ≤ n) :
    Real.log ((n.factorial : ℝ) / (sylBlocks n : ℝ))
      ≤ (n : ℝ) * Lw n + ((sylK n : ℝ) + 1) * Real.log n + Real.log ((n : ℝ) + 1) := by
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hnpos : (0:ℝ) < (n:ℝ) := by positivity
  have hlogk_nonneg : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hnum := log_factorial_le' n hn1
  have hden : Real.log ((sylBlocks n : ℕ) : ℝ) =
      ∑ i ∈ sylAct n, Real.log (((n / syl i).factorial : ℕ) : ℝ) := by
    rw [sylBlocks, Nat.cast_prod]
    rw [Real.log_prod (fun i hi => by exact_mod_cast Nat.factorial_ne_zero (n / syl i))]
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1)) (fun i => syl i ≤ n)
      (fun i => Real.log (((n / syl i).factorial : ℕ) : ℝ))]
    have hzero : (∑ i ∈ (Finset.range (n + 1)).filter (fun i => ¬ syl i ≤ n),
        Real.log (((n / syl i).factorial : ℕ) : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_filter] at hi
      have hlt : n < syl i := not_le.mp hi.2
      have hz : n / syl i = 0 := Nat.div_eq_of_lt hlt
      simp [hz]
    rw [hzero, add_zero]
    rfl
  have hterm : ∀ i ∈ sylAct n, ((n / syl i : ℕ) : ℝ) * Real.log ((n / syl i : ℕ) : ℝ)
      - ((n / syl i : ℕ) : ℝ) + 1 ≤ Real.log (((n / syl i).factorial : ℕ) : ℝ) := by
    intro i hi
    have hsi : syl i ≤ n := (mem_sylAct.mp hi).2
    have hsinat : 0 < syl i := by have := syl_two_le i; omega
    have h1 : 1 ≤ n / syl i := (Nat.le_div_iff_mul_le hsinat).mpr (by simpa using hsi)
    exact log_factorial_ge (n / syl i) h1
  have hblocks_ge : (∑ i ∈ sylAct n, (((n / syl i : ℕ) : ℝ) * Real.log ((n / syl i : ℕ) : ℝ)
      - ((n / syl i : ℕ) : ℝ) + 1)) ≤ Real.log ((sylBlocks n : ℕ) : ℝ) := by
    rw [hden]
    exact Finset.sum_le_sum hterm
  have hsplit_sum : (∑ i ∈ sylAct n, (((n / syl i : ℕ) : ℝ) * Real.log ((n / syl i : ℕ) : ℝ)
      - ((n / syl i : ℕ) : ℝ) + 1))
      = (∑ i ∈ sylAct n, ((n / syl i : ℕ) : ℝ) * Real.log ((n / syl i : ℕ) : ℝ))
        - (∑ i ∈ sylAct n, ((n / syl i : ℕ) : ℝ)) + (sylK n : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
      sylAct_card_cast]
  have hS_le : (∑ i ∈ sylAct n, ((n / syl i : ℕ) : ℝ)) ≤ (n:ℝ) - 1 := by
    have h1 : (∑ i ∈ sylAct n, n / syl i) + 1 ≤ n := by
      have h2 : (∑ i ∈ sylAct n, n / syl i) = ∑ i ∈ Finset.range (n + 1), n / syl i := by
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (n+1)) (fun i => syl i ≤ n)]
        have hz : (∑ i ∈ (Finset.range (n+1)).filter (fun i => ¬ syl i ≤ n), n / syl i) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          rw [Finset.mem_filter] at hi
          exact Nat.div_eq_of_lt (not_le.mp hi.2)
        rw [hz, add_zero]
        rfl
      rw [h2]
      exact syl_div_sum_le hn1 (le_refl n)
    have h3 : ((∑ i ∈ sylAct n, n / syl i : ℕ) : ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast h1
    have h4 : (∑ i ∈ sylAct n, ((n / syl i : ℕ) : ℝ)) = ((∑ i ∈ sylAct n, n / syl i : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
    rw [h4]
    linarith
  have hK_low : (n:ℝ) - (∑ i ∈ sylAct n, ((n / syl i : ℕ) : ℝ)) ≤ (sylK n : ℝ) + 1 := by
    have hlow : ∀ i ∈ sylAct n, (n:ℝ)/(syl i : ℝ) - 1 ≤ ((n / syl i : ℕ) : ℝ) := by
      intro i hi
      have hsinat : 0 < syl i := by have := syl_two_le i; omega
      have hsiR : (0:ℝ) < (syl i : ℝ) := by exact_mod_cast hsinat
      have h1 : n < (n / syl i + 1) * syl i :=
        (Nat.div_lt_iff_lt_mul hsinat).mp (Nat.lt_succ_self _)
      have h2 : (n:ℝ) ≤ (((n / syl i : ℕ) : ℝ) + 1) * (syl i : ℝ) := by
        exact_mod_cast h1.le
      have h3 : (n:ℝ)/(syl i:ℝ) ≤ ((n / syl i : ℕ) : ℝ) + 1 := by
        rw [div_le_iff₀ hsiR]; linarith
      linarith
    have hsumlow : (∑ i ∈ sylAct n, ((n:ℝ)/(syl i : ℝ))) - (sylK n : ℝ) ≤
        ∑ i ∈ sylAct n, ((n / syl i : ℕ) : ℝ) := by
      have h := Finset.sum_le_sum hlow
      rw [Finset.sum_sub_distrib] at h
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, sylAct_card_cast] at h
      linarith
    have hinv := sum_sylAct_inv_ge hn2
    have hnR : (0:ℝ) < (n:ℝ) := by positivity
    have hbig : (n:ℝ) - 1 ≤ ∑ i ∈ sylAct n, ((n:ℝ)/(syl i : ℝ)) := by
      have h6 : (n:ℝ) * (1 - 1/(n:ℝ)) ≤ (n:ℝ) * ∑ i ∈ sylAct n, 1/(syl i : ℝ) :=
        mul_le_mul_of_nonneg_left hinv (le_of_lt hnR)
      have h7 : (n:ℝ) * (1 - 1/(n:ℝ)) = (n:ℝ) - 1 := by field_simp
      have h8 : (n:ℝ) * ∑ i ∈ sylAct n, 1/(syl i : ℝ) = ∑ i ∈ sylAct n, (n:ℝ)/(syl i : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [mul_one_div]
      linarith
    linarith
  have hper_sum : (∑ i ∈ sylAct n, ((n / syl i : ℕ) : ℝ) *
        Real.log ((n:ℝ)/((n / syl i : ℕ) : ℝ)))
      ≤ (∑ i ∈ sylAct n, ((n / syl i : ℕ) : ℝ) * Real.log (syl i)) + (sylK n : ℝ) := by
    have h := Finset.sum_le_sum (fun i hi => per_term_le (n := n) hi)
    rw [Finset.sum_add_distrib] at h
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, sylAct_card_cast] at h
    exact h
  have hQid : (n:ℝ) * Real.log n -
        (∑ i ∈ sylAct n, ((n / syl i : ℕ) : ℝ) * Real.log ((n / syl i : ℕ) : ℝ))
      = (∑ i ∈ sylAct n, ((n / syl i : ℕ) : ℝ) * Real.log ((n:ℝ)/((n / syl i : ℕ) : ℝ)))
        + ((n:ℝ) - ∑ i ∈ sylAct n, ((n / syl i : ℕ) : ℝ)) * Real.log n := by
    have hper : ∀ i ∈ sylAct n, ((n / syl i : ℕ) : ℝ) * Real.log ((n:ℝ)/((n / syl i : ℕ) : ℝ))
        = ((n / syl i : ℕ) : ℝ) * Real.log n
          - ((n / syl i : ℕ) : ℝ) * Real.log ((n / syl i : ℕ) : ℝ) := by
      intro i hi
      have hq : (0:ℝ) < ((n / syl i : ℕ) : ℝ) := by
        have hsi : syl i ≤ n := (mem_sylAct.mp hi).2
        have hsinat : 0 < syl i := by have := syl_two_le i; omega
        have h1 : 1 ≤ n / syl i := (Nat.le_div_iff_mul_le hsinat).mpr (by simpa using hsi)
        have h2 : ((1:ℕ) : ℝ) ≤ ((n / syl i : ℕ) : ℝ) := by exact_mod_cast h1
        linarith
      rw [Real.log_div (by positivity) (ne_of_gt hq)]
      ring
    rw [Finset.sum_congr rfl hper, Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  have hW : (∑ i ∈ sylAct n, ((n / syl i : ℕ) : ℝ) * Real.log (syl i)) ≤ (n:ℝ) * Lw n := by
    have h1 : (∑ i ∈ sylAct n, ((n / syl i : ℕ) : ℝ) * Real.log (syl i))
        ≤ ∑ i ∈ sylAct n, ((n:ℝ)/(syl i : ℝ)) * Real.log (syl i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hlogi : 0 ≤ Real.log (syl i) := by
        refine Real.log_nonneg ?_
        exact_mod_cast (show (1:ℕ) ≤ syl i by have := syl_two_le i; omega)
      have hq : ((n / syl i : ℕ) : ℝ) ≤ (n:ℝ)/(syl i : ℝ) := Nat.cast_div_le
      exact mul_le_mul_of_nonneg_right hq hlogi
    have h2 : (∑ i ∈ sylAct n, ((n:ℝ)/(syl i : ℝ)) * Real.log (syl i)) = (n:ℝ) * Lw n := by
      rw [Lw_eq_sum_sylAct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    linarith
  have hblockspos : (0:ℝ) < ((sylBlocks n : ℕ) : ℝ) := by
    rw [sylBlocks, Nat.cast_prod]
    exact Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos _
  have hlogC : Real.log ((n.factorial : ℝ) / (sylBlocks n : ℝ)) =
      Real.log ((n.factorial:ℕ):ℝ) - Real.log ((sylBlocks n:ℕ):ℝ) := by
    rw [Real.log_div (by exact_mod_cast Nat.factorial_ne_zero n) (ne_of_gt hblockspos)]
  have hprod : ((n:ℝ) - ∑ i ∈ sylAct n, ((n / syl i : ℕ) : ℝ)) * Real.log n ≤
      ((sylK n : ℝ) + 1) * Real.log n := mul_le_mul_of_nonneg_right hK_low hlogk_nonneg
  have hZA : Real.log ((n.factorial : ℝ) / (sylBlocks n : ℝ)) ≤
      ((n:ℝ) * Real.log n
        - (∑ i ∈ sylAct n, ((n / syl i : ℕ) : ℝ) * Real.log ((n / syl i : ℕ) : ℝ)))
      + Real.log ((n:ℝ) + 1) - (sylK n : ℝ) := by
    rw [hlogC]
    linarith [hnum, hblocks_ge, hsplit_sum, hS_le]
  have hZB : ((n:ℝ) * Real.log n
        - (∑ i ∈ sylAct n, ((n / syl i : ℕ) : ℝ) * Real.log ((n / syl i : ℕ) : ℝ)))
      ≤ (∑ i ∈ sylAct n, ((n / syl i : ℕ) : ℝ) * Real.log (syl i))
        + (sylK n : ℝ) + ((sylK n : ℝ) + 1) * Real.log n := by
    linarith [hQid, hper_sum, hprod]
  linarith [hZA, hZB, hW]


/-! ## Explicit logarithmic estimates -/

private lemma log_le_div_490 : ∀ n : ℕ, 4096 ≤ n → Real.log n ≤ (n : ℝ) / 490 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      have h : Real.log ((4096 : ℕ) : ℝ) = 12 * Real.log 2 := by
        rw [show ((4096 : ℕ) : ℝ) = (2:ℝ)^12 by norm_num, Real.log_pow]
        norm_num
      have h2 := Real.log_two_lt_d9
      rw [h]
      norm_num
      linarith
  | succ n hn ih =>
      have hn0 : (0:ℝ) < (n:ℝ) := by positivity
      have h1 : Real.log ((n:ℝ) + 1) ≤ Real.log n + 1/(n:ℝ) := by
        have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < ((n:ℝ)+1)/(n:ℝ) by positivity)
        rw [Real.log_div (by positivity) (by positivity)] at h
        have h2 : ((n:ℝ)+1)/(n:ℝ) - 1 = 1/(n:ℝ) := by field_simp; ring
        linarith
      have h2 : (1:ℝ)/(n:ℝ) ≤ 1/490 := by
        apply one_div_le_one_div_of_le (by norm_num)
        exact_mod_cast (show 490 ≤ n by omega)
      have hcast : ((n+1 : ℕ) : ℝ) = (n:ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith

private lemma log_le_sqrt_div : ∀ n : ℕ, 10^13 ≤ n → Real.log n ≤ Real.sqrt n / 100 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      have hlog : Real.log (((10:ℕ)^13 : ℕ) : ℝ) ≤ 30 := by
        rw [Real.log_le_iff_le_exp (by positivity)]
        have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 30 by norm_num) 60
        have hsum : (((10:ℕ)^13 : ℕ) : ℝ) <
            ∑ i ∈ Finset.range 60, (30:ℝ)^i / ((i.factorial:ℕ):ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
        exact le_of_lt (lt_of_lt_of_le hsum h)
      have hs : (30:ℝ) ≤ Real.sqrt (((10:ℕ)^13 : ℕ) : ℝ) / 100 := by
        rw [le_div_iff₀ (by norm_num)]
        rw [Real.le_sqrt (by norm_num) (by norm_num)]
        norm_num
      exact le_trans hlog hs
  | succ n hn ih =>
      have hn0 : (0:ℝ) < (n:ℝ) := by positivity
      have hcast : ((n+1 : ℕ) : ℝ) = (n:ℝ) + 1 := by push_cast; ring
      have h1 : Real.log ((n:ℝ) + 1) ≤ Real.log n + 1/(n:ℝ) := by
        have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < ((n:ℝ)+1)/(n:ℝ) by positivity)
        rw [Real.log_div (by positivity) (by positivity)] at h
        have h2 : ((n:ℝ)+1)/(n:ℝ) - 1 = 1/(n:ℝ) := by field_simp; ring
        linarith
      have hbig : Real.sqrt ((n:ℝ) + 1) ≤ (n:ℝ)/1000000 := by
        rw [Real.sqrt_le_iff]
        refine ⟨by positivity, ?_⟩
        rw [div_pow, le_div_iff₀ (by norm_num : (0:ℝ) < (1000000:ℝ)^2)]
        have h13 : (10:ℕ)^13 ≤ n := by
          have : (4096:ℕ) ≤ n := by omega
          omega
        have h13' : ((10:ℝ)^13) ≤ (n:ℝ) := by exact_mod_cast h13
        nlinarith [h13']
      have hxle : Real.sqrt ((n:ℝ)+1) + Real.sqrt (n:ℝ) ≤ 2 * (n:ℝ)/1000000 := by
        have hs := Real.sqrt_le_sqrt (show (n:ℝ) ≤ (n:ℝ)+1 by linarith)
        linarith
      have hdiff : Real.sqrt ((n:ℝ)+1) - Real.sqrt (n:ℝ) =
          1/(Real.sqrt ((n:ℝ)+1) + Real.sqrt (n:ℝ)) := by
        have h1 : Real.sqrt ((n:ℝ)+1)^2 = (n:ℝ)+1 := Real.sq_sqrt (by positivity)
        have h2 : Real.sqrt (n:ℝ)^2 = (n:ℝ) := Real.sq_sqrt (by positivity)
        have hpos : 0 < Real.sqrt ((n:ℝ)+1) + Real.sqrt (n:ℝ) := by
          have h3 := Real.sqrt_pos.mpr (show (0:ℝ) < (n:ℝ)+1 by positivity)
          have h4 := Real.sqrt_nonneg (n:ℝ)
          linarith
        rw [eq_div_iff (ne_of_gt hpos)]
        nlinarith
      have hx100 : (Real.sqrt ((n:ℝ)+1) + Real.sqrt (n:ℝ)) * 100 ≤ (n:ℝ) := by
        have h1 : (Real.sqrt ((n:ℝ)+1) + Real.sqrt (n:ℝ)) * 100 ≤ (2 * (n:ℝ)/1000000) * 100 := by
          nlinarith [hxle]
        have h2 : (2 * (n:ℝ)/1000000) * 100 ≤ (n:ℝ) := by nlinarith
        linarith
      have hstep : (Real.sqrt ((n:ℝ)+1) - Real.sqrt (n:ℝ))/100 ≥ 1/(n:ℝ) := by
        have hxpos : (0:ℝ) < (Real.sqrt ((n:ℝ)+1) + Real.sqrt (n:ℝ)) * 100 := by
          have h3 := Real.sqrt_pos.mpr (show (0:ℝ) < (n:ℝ)+1 by linarith)
          have h4 := Real.sqrt_nonneg (n:ℝ)
          nlinarith
        have hfin : (1:ℝ)/(n:ℝ) ≤ 1/((Real.sqrt ((n:ℝ)+1) + Real.sqrt (n:ℝ)) * 100) :=
          one_div_le_one_div_of_le hxpos hx100
        rw [hdiff, div_div]
        exact hfin
      rw [hcast]
      linarith [h1, ih, hstep]

/-! ## The endgame -/

private lemma sylK_le_five (n : ℕ) (h : n < syl 5) : sylK n ≤ 5 := by
  have hsub : sylAct n ⊆ Finset.range 5 := by
    intro i hi
    rw [Finset.mem_range]
    by_contra h5
    push_neg at h5
    have hs : syl 5 ≤ syl i := syl_mono h5
    have hi' := (mem_sylAct.mp hi).2
    rw [syl_five_val] at h hs
    omega
  have := Finset.card_le_card hsub
  simpa [sylK, Finset.card_range] using this

private lemma sylK_le_six (n : ℕ) (h : n < syl 6) : sylK n ≤ 6 := by
  have hsub : sylAct n ⊆ Finset.range 6 := by
    intro i hi
    rw [Finset.mem_range]
    by_contra h5
    push_neg at h5
    have hs : syl 6 ≤ syl i := syl_mono h5
    have hi' := (mem_sylAct.mp hi).2
    rw [syl_six_val] at h hs
    omega
  have := Finset.card_le_card hsub
  simpa [sylK, Finset.card_range] using this

private lemma caseA (k : ℕ) (hk : 4096 ≤ k) (hK : (sylK k : ℝ) ≤ 5) :
    (k:ℝ) * Lw k + ((sylK k : ℝ) + 1) * Real.log k + Real.log ((k:ℝ)+1) ≤ 1.1 * (k:ℝ) := by
  have hLw := Lw_le k
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hkR : (4096:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hlogk := log_le_div_490 k hk
  have hlogk1 := log_le_div_490 (k+1) (by omega)
  have hcast : ((k+1 : ℕ) : ℝ) = (k:ℝ) + 1 := by push_cast; ring
  rw [hcast] at hlogk1
  have h1 : (k:ℝ) * Lw k ≤ (k:ℝ) * 1.083 := mul_le_mul_of_nonneg_left hLw (le_of_lt hk0)
  have h2 : ((sylK k : ℝ) + 1) * Real.log k ≤ 6 * Real.log k := by
    have hlogknn : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast (show (1:ℕ) ≤ k by omega))
    nlinarith
  have h3 : 6 * Real.log k ≤ 6 * ((k:ℝ)/490) := by linarith
  have h4 : Real.log ((k:ℝ)+1) ≤ ((k:ℝ)+1)/490 := hlogk1
  have h5 : 6 * ((k:ℝ)/490) + ((k:ℝ)+1)/490 ≤ 0.017 * (k:ℝ) := by linarith
  linarith [h1, h2, h3, h4, h5]

private lemma caseB (k : ℕ) (hk : 3263443 ≤ k) (hK : (sylK k : ℝ) ≤ 6) :
    (k:ℝ) * Lw k + ((sylK k : ℝ) + 1) * Real.log k + Real.log ((k:ℝ)+1) ≤ 1.1 * (k:ℝ) := by
  have hLw := Lw_le k
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hkR : (3263443:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hlogk := log_le_div_490 k (by omega)
  have hlogk1 := log_le_div_490 (k+1) (by omega)
  have hcast : ((k+1 : ℕ) : ℝ) = (k:ℝ) + 1 := by push_cast; ring
  rw [hcast] at hlogk1
  have h1 : (k:ℝ) * Lw k ≤ (k:ℝ) * 1.083 := mul_le_mul_of_nonneg_left hLw (le_of_lt hk0)
  have h2 : ((sylK k : ℝ) + 1) * Real.log k ≤ 7 * Real.log k := by
    have hlogknn : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast (show (1:ℕ) ≤ k by omega))
    nlinarith
  have h3 : 7 * Real.log k ≤ 7 * ((k:ℝ)/490) := by linarith
  have h4 : Real.log ((k:ℝ)+1) ≤ ((k:ℝ)+1)/490 := hlogk1
  have h5 : 7 * ((k:ℝ)/490) + ((k:ℝ)+1)/490 ≤ 0.017 * (k:ℝ) := by linarith
  linarith [h1, h2, h3, h4, h5]

private lemma caseC (k : ℕ) (hk : 10650056950807 ≤ k)
    (hKlog : (sylK k : ℝ) ≤ Real.log k / Real.log 2 + 1) :
    (k:ℝ) * Lw k + ((sylK k : ℝ) + 1) * Real.log k + Real.log ((k:ℝ)+1) ≤ 1.1 * (k:ℝ) := by
  have hLw := Lw_le k
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hkbig : (10650056950807:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hinv2 : 1 / Real.log 2 ≤ 1.4428 := by
    rw [div_le_iff₀ hlog2pos]
    nlinarith [Real.log_two_gt_d9]
  have hlogknn : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast (show (1:ℕ) ≤ k by omega))
  have hK1 : (sylK k : ℝ) + 1 ≤ 1.4428 * Real.log k + 2 := by
    have h : Real.log k / Real.log 2 ≤ 1.4428 * Real.log k := by
      calc Real.log k / Real.log 2 = (1 / Real.log 2) * Real.log k := by ring
        _ ≤ 1.4428 * Real.log k := mul_le_mul_of_nonneg_right hinv2 hlogknn
    linarith
  have hk13 : 10^13 ≤ k := by
    have : (10:ℕ)^13 ≤ 10650056950807 := by norm_num
    omega
  have hlogk := log_le_sqrt_div k hk13
  have hsk : (0:ℝ) ≤ Real.sqrt k := Real.sqrt_nonneg k
  have hsq : Real.sqrt k * Real.sqrt k = (k:ℝ) := by
    rw [← sq]
    exact Real.sq_sqrt (by exact_mod_cast Nat.zero_le k)
  have hsk1 : (1:ℝ) ≤ Real.sqrt k := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    exact_mod_cast (by omega : 1 ≤ k)
  have hsk1000 : (1000:ℝ) ≤ Real.sqrt k := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    have : (1000000:ℕ) ≤ k := by
      have : (10:ℕ)^13 ≤ k := hk13
      omega
    exact_mod_cast this
  have hskdiv : Real.sqrt k ≤ (k:ℝ)/1000 := by nlinarith [hsk1000, hsk, hsq]
  have h1 : (k:ℝ) * Lw k ≤ (k:ℝ) * 1.083 := mul_le_mul_of_nonneg_left hLw (le_of_lt hk0)
  have h2 : ((sylK k : ℝ) + 1) * Real.log k ≤ (1.4428 * Real.log k + 2) * Real.log k :=
    mul_le_mul_of_nonneg_right hK1 hlogknn
  have h3 : (1.4428 * Real.log k + 2) * Real.log k ≤
      (1.4428 * (Real.sqrt k/100) + 2) * (Real.sqrt k/100) := by
    apply mul_le_mul
    · linarith [hlogk]
    · exact hlogk
    · exact Real.log_nonneg (by exact_mod_cast (show (1:ℕ) ≤ k by omega))
    · positivity
  have hmid : (1.4428 * (Real.sqrt k/100) + 2) * (Real.sqrt k/100) ≤ 0.00017428 * (k:ℝ) := by
    nlinarith [hsq, hsk, hskdiv]
  have hcast : ((k+1 : ℕ) : ℝ) = (k:ℝ) + 1 := by push_cast; ring
  have h4 : Real.log ((k:ℝ)+1) ≤ Real.sqrt ((k:ℝ)+1)/100 := by
    have h := log_le_sqrt_div (k+1) (by omega)
    rwa [hcast] at h
  have hsqrt1 : Real.sqrt ((k:ℝ)+1) ≤ Real.sqrt k + 1 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have h := Real.sq_sqrt (show (0:ℝ) ≤ (k:ℝ) by positivity)
    nlinarith [hsk]
  have h6 : Real.sqrt ((k:ℝ)+1)/100 ≤ 0.00001 * (k:ℝ) + 0.01 := by
    nlinarith [hsqrt1, hskdiv]
  linarith [h1, h2, h3, hmid, h4, h6, hkbig]

theorem log_ulcm_le (k : ℕ) (hk : 19 ≤ k) : Real.log (ulcm k) ≤ 1.1 * k := by
  rcases lt_or_ge k 4096 with hk' | hk'
  · have h := ulcm_le_three_pow_small k hk'
    have hpos : (0:ℝ) < (ulcm k : ℝ) := by exact_mod_cast ulcm_pos k
    have hcast : (ulcm k : ℝ) ≤ (3:ℝ)^k := by
      have h2 : ((ulcm k : ℕ):ℝ) ≤ ((3^k : ℕ):ℝ) := by exact_mod_cast h
      simpa using h2
    have hlog : Real.log (ulcm k) ≤ (k:ℝ) * Real.log 3 := by
      have := Real.log_le_log hpos hcast
      rwa [Real.log_pow] at this
    have h3 : Real.log 3 ≤ 1.1 := by
      have := Real.log_three_lt_d9
      linarith
    have hk0 : (0:ℝ) ≤ (k:ℝ) := by positivity
    nlinarith
  · have hk3 : 3 ≤ k := by omega
    have hdvd := syl_divisibility k
    have hMpos : 0 < sylBlocks k := by
      rw [sylBlocks]
      exact Finset.prod_pos fun i _ => Nat.factorial_pos _
    have hle : (ulcm k : ℝ) ≤ (k.factorial : ℝ) / (sylBlocks k : ℝ) := by
      have h1 : ulcm k * sylBlocks k ≤ k.factorial := Nat.le_of_dvd (Nat.factorial_pos k) hdvd
      have h2 : (ulcm k : ℝ) * (sylBlocks k : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast h1
      rw [le_div_iff₀ (by exact_mod_cast hMpos)]
      exact h2
    have hlog1 : Real.log (ulcm k) ≤
        Real.log ((k.factorial : ℝ) / (sylBlocks k : ℝ)) :=
      Real.log_le_log (by exact_mod_cast ulcm_pos k) hle
    have hlog2 := le_trans hlog1 (log_sylBlocks_le k hk3)
    rcases lt_or_ge k 3263443 with hA | hB
    · exact le_trans hlog2 (caseA k hk' (by exact_mod_cast sylK_le_five k hA))
    · rcases lt_or_ge k 10650056950807 with hB1 | hB2
      · exact le_trans hlog2 (caseB k hB (by exact_mod_cast sylK_le_six k hB1))
      · exact le_trans hlog2 (caseC k hB2 (sylK_le_log k (by omega)))

end Work.BW
