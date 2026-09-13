import Mathlib
import Submission.Commons.Combinatorics.QBinomial.gb_pow_sum_le
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_mul_prod

namespace Commons.Combinatorics.QBinomial

open Finset

/-- Elementary rational arithmetic step. -/
private lemma arith_step (a : ℚ) (ha : 2 ≤ a) :
    (2*a/(2*a-1)) * (4*(a-1)/a) ≤ 4*(2*a-1)/(2*a) := by
  have h1 : (0:ℚ) < 2*a - 1 := by linarith
  have h2 : (0:ℚ) < a := by linarith
  rw [show (2*a/(2*a-1)) * (4*(a-1)/a) = (8*a*(a-1))/((2*a-1)*a) by
        field_simp; ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Key product bound: `∏_{i<k} 2^{k-i} / (2^{k-i} - 1) ≤ 4`. -/
lemma prod_pow_div_pow_sub_one_le_four (k : ℕ) :
    (∏ i ∈ Finset.range k, (2:ℚ)^(k-i) / ((2:ℚ)^(k-i) - 1)) ≤ 4 := by
  have hbase : ∀ k, 1 ≤ k →
      (∏ i ∈ Finset.range k, (2:ℚ)^(k-i) / ((2:ℚ)^(k-i) - 1))
        ≤ 4 * ((2:ℚ)^k - 1) / (2:ℚ)^k := by
    intro k
    induction k with
    | zero => intro h; omega
    | succ m ih =>
      intro hm
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · subst hm0
        norm_num
      · have hstep : (∏ i ∈ Finset.range (m+1),
            (2:ℚ)^((m+1)-i) / ((2:ℚ)^((m+1)-i) - 1))
            = ((2:ℚ)^(m+1) / ((2:ℚ)^(m+1) - 1)) *
              (∏ i ∈ Finset.range m, (2:ℚ)^(m-i) / ((2:ℚ)^(m-i) - 1)) := by
          rw [Finset.prod_range_succ']
          have hfac : (∏ k ∈ Finset.range m,
                (2:ℚ)^((m+1)-(k+1)) / ((2:ℚ)^((m+1)-(k+1)) - 1))
              = ∏ i ∈ Finset.range m, (2:ℚ)^(m-i) / ((2:ℚ)^(m-i) - 1) := by
            apply Finset.prod_congr rfl
            intro i hi
            rw [show m + 1 - (i + 1) = m - i by omega]
          rw [hfac, mul_comm]
          simp
        rw [hstep]
        have hih := ih hmpos
        have hden : (0:ℚ) < (2:ℚ)^(m+1) - 1 := by
          have h1 : (2:ℚ)^1 ≤ (2:ℚ)^(m+1) := pow_le_pow_right₀ (by norm_num) (by omega)
          simp only [pow_one] at h1; linarith
        have hstep2 : ((2:ℚ)^(m+1) / ((2:ℚ)^(m+1) - 1)) *
              (∏ i ∈ Finset.range m, (2:ℚ)^(m-i) / ((2:ℚ)^(m-i) - 1))
            ≤ ((2:ℚ)^(m+1) / ((2:ℚ)^(m+1) - 1)) *
              (4 * ((2:ℚ)^m - 1) / (2:ℚ)^m) := by
          apply mul_le_mul_of_nonneg_left hih
          exact div_nonneg (by positivity) (le_of_lt hden)
        refine le_trans hstep2 ?_
        have ha2 : (2:ℚ) ≤ (2:ℚ)^m := by
          calc (2:ℚ) = (2:ℚ)^1 := by norm_num
            _ ≤ (2:ℚ)^m := pow_le_pow_right₀ (by norm_num) (by omega)
        have h := arith_step ((2:ℚ)^m) ha2
        rw [show (2:ℚ)^(m+1) = 2 * (2:ℚ)^m by rw [pow_succ]; ring]
        exact h
  have hk := hbase k
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0; simp
  · refine le_trans (hk hkpos) ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [pow_pos (show (0:ℚ) < 2 by norm_num) k]

/-- Termwise bound behind the main estimate. -/
lemma div_pow_sub_le (n k i : ℕ) (hik : i < k) (hkn : k ≤ n) :
    ((2:ℚ)^n - (2:ℚ)^i) / ((2:ℚ)^k - (2:ℚ)^i)
      ≤ (2:ℚ)^(n-k) * ((2:ℚ)^(k-i) / ((2:ℚ)^(k-i) - 1)) := by
  have hik_le : i ≤ k := le_of_lt hik
  have hin : i ≤ n := le_trans hik_le hkn
  have hden2_pos : (0:ℚ) < (2:ℚ)^(k-i) - 1 := by
    have h1 : (2:ℚ)^1 ≤ (2:ℚ)^(k-i) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    simp only [pow_one] at h1; linarith
  have hn1 : (2:ℚ)^n = (2:ℚ)^i * (2:ℚ)^(n-i) := by
    rw [← pow_add, Nat.add_sub_cancel' hin]
  have hk1 : (2:ℚ)^k = (2:ℚ)^i * (2:ℚ)^(k-i) := by
    rw [← pow_add, Nat.add_sub_cancel' hik_le]
  have e1 : (2:ℚ)^i * (2:ℚ)^(n-i) - (2:ℚ)^i = (2:ℚ)^i * ((2:ℚ)^(n-i) - 1) := by ring
  have e2 : (2:ℚ)^i * (2:ℚ)^(k-i) - (2:ℚ)^i = (2:ℚ)^i * ((2:ℚ)^(k-i) - 1) := by ring
  have hnum : (2:ℚ)^(n-i) - 1 ≤ (2:ℚ)^(n-k) * (2:ℚ)^(k-i) := by
    have heq : (2:ℚ)^(n-k) * (2:ℚ)^(k-i) = (2:ℚ)^(n-i) := by
      rw [← pow_add]; congr 1; omega
    rw [heq]; linarith [pow_pos (show (0:ℚ) < 2 by norm_num) (n-i)]
  rw [hn1, hk1, e1, e2, mul_div_mul_left _ _ (by positivity : (2:ℚ)^i ≠ 0)]
  calc ((2:ℚ)^(n-i) - 1) / ((2:ℚ)^(k-i) - 1)
      ≤ ((2:ℚ)^(n-k) * (2:ℚ)^(k-i)) / ((2:ℚ)^(k-i) - 1) :=
        div_le_div_of_nonneg_right hnum (le_of_lt hden2_pos)
    _ = (2:ℚ)^(n-k) * ((2:ℚ)^(k-i) / ((2:ℚ)^(k-i) - 1)) := by ring

theorem gb_le_four_mul_two_pow (n k : ℕ) (hk : k ≤ n) :
    Commons.Combinatorics.QBinomial.gb n k ≤ 4 * 2 ^ (k * (n - k)) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    rw [gb_zero]
    norm_num
  have hnat : gb n k * (∏ i ∈ Finset.range k, (2^k - 2^i))
      = ∏ i ∈ Finset.range k, (2^n - 2^i) :=
    Commons.LinearAlgebra.Submodule.card_submodule_finrank_mul_prod n k
  have hAposN : 0 < ∏ i ∈ Finset.range k, (2^k - 2^i) := by
    apply Finset.prod_pos
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have hlt : 2^i < 2^k := Nat.pow_lt_pow_right (by norm_num) hik
    omega
  have hnatQ : (gb n k : ℚ) * ((∏ i ∈ Finset.range k, (2^k - 2^i) : ℕ) : ℚ)
      = ((∏ i ∈ Finset.range k, (2^n - 2^i) : ℕ) : ℚ) := by
    have h : ((gb n k * (∏ i ∈ Finset.range k, (2^k - 2^i)) : ℕ) : ℚ)
        = ((∏ i ∈ Finset.range k, (2^n - 2^i) : ℕ) : ℚ) := by
      exact_mod_cast hnat
    rwa [Nat.cast_mul] at h
  have hAcast : ((∏ i ∈ Finset.range k, (2^k - 2^i) : ℕ) : ℚ)
      = ∏ i ∈ Finset.range k, ((2:ℚ)^k - (2:ℚ)^i) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have hle : (2:ℕ)^i ≤ 2^k := Nat.pow_le_pow_right (by norm_num) (le_of_lt hik)
    rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  have hBcast : ((∏ i ∈ Finset.range k, (2^n - 2^i) : ℕ) : ℚ)
      = ∏ i ∈ Finset.range k, ((2:ℚ)^n - (2:ℚ)^i) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have hle : (2:ℕ)^i ≤ 2^n := Nat.pow_le_pow_right (by norm_num) (le_trans (le_of_lt hik) hk)
    rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  have hPpos : (0:ℚ) < ∏ i ∈ Finset.range k, ((2:ℚ)^k - (2:ℚ)^i) := by
    rw [← hAcast]
    exact_mod_cast hAposN
  have hterm : ∀ i ∈ Finset.range k,
      ((2:ℚ)^n - (2:ℚ)^i) / ((2:ℚ)^k - (2:ℚ)^i)
        ≤ (2:ℚ)^(n-k) * ((2:ℚ)^(k-i) / ((2:ℚ)^(k-i) - 1)) := by
    intro i hi
    exact div_pow_sub_le n k i (Finset.mem_range.mp hi) hk
  have hnonneg : ∀ i ∈ Finset.range k,
      (0:ℚ) ≤ ((2:ℚ)^n - (2:ℚ)^i) / ((2:ℚ)^k - (2:ℚ)^i) := by
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have hin : i ≤ n := le_trans (le_of_lt hik) hk
    have hnum : (0:ℚ) ≤ (2:ℚ)^n - (2:ℚ)^i := by
      have : (2:ℚ)^i ≤ (2:ℚ)^n := pow_le_pow_right₀ (by norm_num) hin
      linarith
    have hden : (0:ℚ) ≤ (2:ℚ)^k - (2:ℚ)^i := by
      have : (2:ℚ)^i ≤ (2:ℚ)^k := pow_le_pow_right₀ (by norm_num) (le_of_lt hik)
      linarith
    exact div_nonneg hnum hden
  have hprod_le : (∏ i ∈ Finset.range k,
        ((2:ℚ)^n - (2:ℚ)^i) / ((2:ℚ)^k - (2:ℚ)^i))
      ≤ ∏ i ∈ Finset.range k,
        ((2:ℚ)^(n-k) * ((2:ℚ)^(k-i) / ((2:ℚ)^(k-i) - 1))) :=
    Finset.prod_le_prod hnonneg hterm
  have hprod_eq : (∏ i ∈ Finset.range k,
        ((2:ℚ)^(n-k) * ((2:ℚ)^(k-i) / ((2:ℚ)^(k-i) - 1))))
      = (2:ℚ)^((n-k)*k) * (∏ i ∈ Finset.range k,
          ((2:ℚ)^(k-i) / ((2:ℚ)^(k-i) - 1))) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
  have hS := prod_pow_div_pow_sub_one_le_four k
  have hratio : (∏ i ∈ Finset.range k, ((2:ℚ)^n - (2:ℚ)^i))
        / (∏ i ∈ Finset.range k, ((2:ℚ)^k - (2:ℚ)^i)) ≤ 4 * (2:ℚ)^(k*(n-k)) := by
    rw [← Finset.prod_div_distrib]
    calc (∏ i ∈ Finset.range k, ((2:ℚ)^n - (2:ℚ)^i) / ((2:ℚ)^k - (2:ℚ)^i))
        ≤ ∏ i ∈ Finset.range k,
            ((2:ℚ)^(n-k) * ((2:ℚ)^(k-i) / ((2:ℚ)^(k-i) - 1))) := hprod_le
      _ = (2:ℚ)^((n-k)*k) * (∏ i ∈ Finset.range k,
            ((2:ℚ)^(k-i) / ((2:ℚ)^(k-i) - 1))) := hprod_eq
      _ ≤ (2:ℚ)^(k*(n-k)) * 4 := by
          rw [Nat.mul_comm (n-k) k]
          exact mul_le_mul_of_nonneg_left hS (by positivity)
      _ = 4 * (2:ℚ)^(k*(n-k)) := by ring
  have hkey : (∏ i ∈ Finset.range k, ((2:ℚ)^n - (2:ℚ)^i))
      ≤ 4 * (2:ℚ)^(k*(n-k)) * (∏ i ∈ Finset.range k, ((2:ℚ)^k - (2:ℚ)^i)) := by
    have := hratio
    rw [div_le_iff₀ hPpos] at this
    exact this
  have hb : (gb n k : ℚ) * (∏ i ∈ Finset.range k, ((2:ℚ)^k - (2:ℚ)^i))
      ≤ (4 * (2:ℚ)^(k*(n-k))) * (∏ i ∈ Finset.range k, ((2:ℚ)^k - (2:ℚ)^i)) := by
    have h1 : (gb n k : ℚ) * (∏ i ∈ Finset.range k, ((2:ℚ)^k - (2:ℚ)^i))
        = ∏ i ∈ Finset.range k, ((2:ℚ)^n - (2:ℚ)^i) := by
      rw [← hAcast, ← hBcast]
      exact hnatQ
    rw [h1]
    exact hkey
  have hmain : (gb n k : ℚ) ≤ 4 * (2:ℚ)^(k*(n-k)) :=
    le_of_mul_le_mul_right hb hPpos
  have hfinalQ : (gb n k : ℚ) ≤ ((4 * 2 ^ (k * (n - k)) : ℕ) : ℚ) := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ofNat]
    exact hmain
  exact_mod_cast hfinalQ

end Commons.Combinatorics.QBinomial
