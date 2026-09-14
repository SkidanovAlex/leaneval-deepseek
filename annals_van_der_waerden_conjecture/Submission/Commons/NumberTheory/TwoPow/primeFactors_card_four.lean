import Mathlib.Tactic.NormNum.GCD
import Submission.Commons.NumberTheory.Nat.prod_nth_prime_le_prod_of_le
import Submission.Commons.NumberTheory.Totient.totient_ratio_eq_prod_one_sub_inv
import Submission.Commons.NumberTheory.OrderModulo.order_pow_sub_one_dvd
import Submission.Commons.NumberTheory.DivisorSum.card_divisors_sq_le_mul_prod
import Submission.Commons.NumberTheory.TwoPow.primeFactors_card_three

set_option maxRecDepth 1000000
set_option linter.unnecessarySeqFocus false

namespace Commons.NumberTheory.TwoPow

open Finset

private lemma gg_nonneg' : ∀ x, 0 ≤ gg x := by
  intro x
  unfold gg
  rcases Nat.eq_zero_or_pos x with h | h
  · subst h; norm_num
  · apply div_nonneg
    · have : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast h
      linarith
    · positivity

private lemma gg_mono' : Monotone gg := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  unfold gg
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; norm_num
  · have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast, div_le_div_iff₀ hn hn1]
    nlinarith

private lemma gg_eq' (x : ℕ) (hx : 1 ≤ x) : gg x = 1 - 1 / (x : ℝ) := by
  unfold gg
  have hxr : (x : ℝ) ≠ 0 := by
    have : 0 < x := by omega
    exact_mod_cast (ne_of_gt this)
  rw [sub_div, div_self hxr]

private lemma nth_prime_val (i v : ℕ) (hv : Nat.Prime v) (hc : Nat.count Nat.Prime v = i) :
    Nat.nth Nat.Prime i = v := by
  rw [← hc]; exact Nat.nth_count hv

private lemma c5 : Nat.count Nat.Prime 5 = 2 := by decide
private lemma c7 : Nat.count Nat.Prime 7 = 3 := by decide
private lemma c11 : Nat.count Nat.Prime 11 = 4 := by decide
private lemma c13 : Nat.count Nat.Prime 13 = 5 := by decide
private lemma c17 : Nat.count Nat.Prime 17 = 6 := by decide
private lemma c19 : Nat.count Nat.Prime 19 = 7 := by decide
private lemma n2 : Nat.nth Nat.Prime 2 = 5 := nth_prime_val 2 5 (by norm_num) c5
private lemma n3 : Nat.nth Nat.Prime 3 = 7 := nth_prime_val 3 7 (by norm_num) c7
private lemma n4 : Nat.nth Nat.Prime 4 = 11 := nth_prime_val 4 11 (by norm_num) c11
private lemma n5 : Nat.nth Nat.Prime 5 = 13 := nth_prime_val 5 13 (by norm_num) c13
private lemma n6 : Nat.nth Nat.Prime 6 = 17 := nth_prime_val 6 17 (by norm_num) c17
private lemma n7 : Nat.nth Nat.Prime 7 = 19 := nth_prime_val 7 19 (by norm_num) c19

private lemma prod_gg_le (S : Finset ℕ) (hS : ∀ x ∈ S, Nat.Prime x) (m : ℕ)
    (hm : ∀ x ∈ S, m ≤ x) :
    (∏ i ∈ Finset.range S.card, gg (Nat.nth Nat.Prime (Nat.count Nat.Prime m + i)))
      ≤ ∏ x ∈ S, (1 - 1/(x:ℝ)) := by
  have h := Commons.NumberTheory.Nat.prod_nth_prime_le_prod_of_le S m hS hm gg gg_mono' gg_nonneg'
  calc (∏ i ∈ Finset.range S.card, gg (Nat.nth Nat.Prime (Nat.count Nat.Prime m + i)))
        ≤ ∏ x ∈ S, gg x := h
    _ = ∏ x ∈ S, (1 - 1/(x:ℝ)) :=
        Finset.prod_congr rfl (fun x hx => gg_eq' x (hS x hx).one_le)

private lemma bound_4_ge5 (S : Finset ℕ) (hS : ∀ x ∈ S, Nat.Prime x) (hm : ∀ x ∈ S, 5 ≤ x)
    (hc : S.card = 4) : (2880:ℝ)/5005 ≤ ∏ x ∈ S, (1-1/(x:ℝ)) := by
  have h := prod_gg_le S hS 5 hm
  rw [hc] at h
  have hval : (∏ i ∈ Finset.range 4, gg (Nat.nth Nat.Prime (Nat.count Nat.Prime 5 + i)))
      = (2880:ℝ)/5005 := by
    rw [c5]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.reduceAdd, Nat.add_zero]
    rw [n2, n3, n4, n5]
    norm_num [gg]
  rw [hval] at h
  exact h

private lemma bound_3_ge11 (S : Finset ℕ) (hS : ∀ x ∈ S, Nat.Prime x) (hm : ∀ x ∈ S, 11 ≤ x)
    (hc : S.card = 3) : (1920:ℝ)/2431 ≤ ∏ x ∈ S, (1-1/(x:ℝ)) := by
  have h := prod_gg_le S hS 11 hm
  rw [hc] at h
  have hval : (∏ i ∈ Finset.range 3, gg (Nat.nth Nat.Prime (Nat.count Nat.Prime 11 + i)))
      = (1920:ℝ)/2431 := by
    rw [c11]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.reduceAdd, Nat.add_zero]
    rw [n4, n5, n6]
    norm_num [gg]
  rw [hval] at h
  exact h

private lemma bound_2_ge17 (S : Finset ℕ) (hS : ∀ x ∈ S, Nat.Prime x) (hm : ∀ x ∈ S, 17 ≤ x)
    (hc : S.card = 2) : (288:ℝ)/323 ≤ ∏ x ∈ S, (1-1/(x:ℝ)) := by
  have h := prod_gg_le S hS 17 hm
  rw [hc] at h
  have hval : (∏ i ∈ Finset.range 2, gg (Nat.nth Nat.Prime (Nat.count Nat.Prime 17 + i)))
      = (288:ℝ)/323 := by
    rw [c17]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.reduceAdd, Nat.add_zero]
    rw [n6, n7]
    norm_num [gg]
  rw [hval] at h
  exact h

private lemma bound_2_ge11 (S : Finset ℕ) (hS : ∀ x ∈ S, Nat.Prime x) (hm : ∀ x ∈ S, 11 ≤ x)
    (hc : S.card = 2) : (120:ℝ)/143 ≤ ∏ x ∈ S, (1-1/(x:ℝ)) := by
  have h := prod_gg_le S hS 11 hm
  rw [hc] at h
  have hval : (∏ i ∈ Finset.range 2, gg (Nat.nth Nat.Prime (Nat.count Nat.Prime 11 + i)))
      = (120:ℝ)/143 := by
    rw [c11]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.reduceAdd, Nat.add_zero]
    rw [n4, n5]
    norm_num [gg]
  rw [hval] at h
  exact h

private lemma prod_U_ge (U : Finset ℕ) (hU : ∀ x ∈ U, Nat.Prime x) (hm : ∀ x ∈ U, 11 ≤ x)
    (hc : U.card = 2) : (143:ℕ) ≤ ∏ x ∈ U, x := by
  have h := Commons.NumberTheory.Nat.prod_nth_prime_le_prod_of_le U 11 hU hm
    (fun x => (x:ℝ)) (fun a b hab => Nat.cast_le.mpr hab) (fun x => by positivity)
  rw [hc] at h
  have hval : (∏ i ∈ Finset.range 2,
        ((Nat.nth Nat.Prime (Nat.count Nat.Prime 11 + i) : ℕ) : ℝ)) = 143 := by
    rw [c11]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.reduceAdd, Nat.add_zero]
    rw [n4, n5]; norm_num
  rw [hval] at h
  have hcast : (∏ x ∈ U, ((x:ℕ):ℝ)) = ((∏ x ∈ U, x : ℕ) : ℝ) := by push_cast; ring
  rw [hcast] at h
  exact_mod_cast h

private lemma prime_ge_five_of_ne_two_three {x : ℕ} (hx : Nat.Prime x) (h2 : x ≠ 2)
    (h3 : x ≠ 3) : 5 ≤ x := by
  by_contra hlt
  rw [not_le] at hlt
  have h2x := hx.two_le
  interval_cases x
  · exact h2 rfl
  · exact h3 rfl
  · norm_num at hx

private lemma prime_ge_seven_of_ne_two_three_five {x : ℕ} (hx : Nat.Prime x) (h2 : x ≠ 2)
    (h3 : x ≠ 3) (h5 : x ≠ 5) : 7 ≤ x := by
  by_contra hlt
  rw [not_le] at hlt
  have h2x := hx.two_le
  interval_cases x
  · exact h2 rfl
  · exact h3 rfl
  · norm_num at hx
  · exact h5 rfl
  · norm_num at hx

private lemma prime_ge_eleven_of_ne_two_three_five_seven {x : ℕ} (hx : Nat.Prime x)
    (h2 : x ≠ 2) (h3 : x ≠ 3) (h5 : x ≠ 5) (h7 : x ≠ 7) : 11 ≤ x := by
  by_contra hlt
  rw [not_le] at hlt
  have h2x := hx.two_le
  interval_cases x
  · exact h2 rfl
  · exact h3 rfl
  · norm_num at hx
  · exact h5 rfl
  · norm_num at hx
  · exact h7 rfl
  · norm_num at hx
  · norm_num at hx
  · norm_num at hx

private lemma prime_ge_eleven_of_ne_seven {x : ℕ} (hx : Nat.Prime x) (h7 : 7 ≤ x) (hne : x ≠ 7) :
    11 ≤ x := by
  by_contra hlt
  rw [not_le] at hlt
  interval_cases x
  · exact hne rfl
  · norm_num at hx
  · norm_num at hx
  · norm_num at hx

private lemma eq_eleven_or_thirteen_of_lt17 {x : ℕ} (hx : Nat.Prime x) (h11 : 11 ≤ x)
    (hlt : x < 17) : x = 11 ∨ x = 13 := by
  interval_cases x
  · exact Or.inl rfl
  · norm_num at hx
  · exact Or.inr rfl
  · norm_num at hx
  · norm_num at hx
  · norm_num at hx

private lemma orderOf_two_three : orderOf (2 : ZMod 3) = 2 := by
  rw [orderOf_eq_iff (by norm_num : 0 < 2)]
  exact ⟨by decide, by intro m hm hm0; interval_cases m <;> decide⟩

private lemma orderOf_two_five : orderOf (2 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num : 0 < 4)]
  exact ⟨by decide, by intro m hm hm0; interval_cases m <;> decide⟩

private lemma orderOf_two_seven : orderOf (2 : ZMod 7) = 3 := by
  rw [orderOf_eq_iff (by norm_num : 0 < 3)]
  exact ⟨by decide, by intro m hm hm0; interval_cases m <;> decide⟩

private lemma orderOf_two_eleven : orderOf (2 : ZMod 11) = 10 := by
  rw [orderOf_eq_iff (by norm_num : 0 < 10)]
  exact ⟨by decide, by intro m hm hm0; interval_cases m <;> decide⟩

private lemma orderOf_two_thirteen : orderOf (2 : ZMod 13) = 12 := by
  rw [orderOf_eq_iff (by norm_num : 0 < 12)]
  exact ⟨by decide, by intro m hm hm0; interval_cases m <;> decide⟩

private lemma order_dvd_of_dvd (q k : ℕ) (hq : Nat.Prime q) (h : q ∣ 2 ^ k - 1) :
    orderOf (2 : ZMod q) ∣ k :=
  Commons.NumberTheory.OrderModulo.order_pow_sub_one_dvd 2 q (by norm_num) hq.one_le h

private lemma two_not_mem_pow (k : ℕ) (hk : 1 ≤ k) : 2 ∉ (2^k-1).primeFactors := by
  intro h2m
  have h2dvd : 2 ∣ 2^k - 1 := (Nat.mem_primeFactors.mp h2m).2.1
  have hpow : 2 ∣ 2^k := ⟨2^(k-1), by rw [mul_comm, ← pow_succ]; congr 1; omega⟩
  have h1e : (2^k - 1) + 1 = 2^k := by have := Nat.one_le_two_pow (n:=k); omega
  have hone : 2 ∣ 1 := (Nat.dvd_add_iff_right h2dvd).mpr (by rw [h1e]; exact hpow)
  norm_num at hone

private lemma euler_real (n : ℕ) (hn0 : n ≠ 0) :
    (Nat.totient n : ℝ)/(n:ℝ) = ∏ p ∈ n.primeFactors, (1 - 1/(p:ℝ)) := by
  have hh := Commons.NumberTheory.Totient.totient_ratio_eq_prod_one_sub_inv n hn0
  have h2 := congrArg (fun x : ℚ => (x:ℝ)) hh
  simpa using h2

private lemma totient_two_mul_lt (k : ℕ) (hk : 2 ≤ k)
    (h1 : Nat.totient (2^k-1) ≤ 2^(k-1)-1) :
    2 * Nat.totient (2^k-1) < 2^k - 1 := by
  have h2k : 2 ≤ 2^k := by
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2e : 2 * (2^(k-1) - 1) = (2^k - 1) - 1 := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    have hp : 2 * 2^(k-1) = 2^k := by rw [← pow_succ']; congr 1; omega
    rw [hp]; omega
  calc 2 * Nat.totient (2^k-1) ≤ 2 * (2^(k-1)-1) := Nat.mul_le_mul_left 2 h1
    _ = (2^k-1) - 1 := h2e
    _ < 2^k - 1 := by omega

private lemma nat_sqrt_pow_le (k : ℕ) :
    ((Nat.sqrt (2^k) : ℕ) : ℝ) ≤ Real.sqrt ((2^k : ℕ) : ℝ) := by
  have h := Nat.sqrt_le (2^k)
  have hmm : (((Nat.sqrt (2^k) : ℕ) : ℝ))^2 ≤ ((2^k:ℕ):ℝ) := by
    have : ((Nat.sqrt (2^k) : ℕ):ℝ) * ((Nat.sqrt (2^k) : ℕ):ℝ) ≤ ((2^k:ℕ):ℝ) := by
      exact_mod_cast h
    simpa [sq] using this
  exact (Real.le_sqrt (by positivity) (by positivity)).mpr hmm

private lemma sqrt_pow_add_one_le (k : ℕ) (_hk : 1 ≤ k) :
    ((Nat.sqrt (2^k) + 1 : ℕ) : ℝ) ≤ Real.sqrt ((2^k - 1 : ℕ) : ℝ) + 2 := by
  have h1 := nat_sqrt_pow_le k
  have h2 : Real.sqrt ((2^k:ℕ):ℝ) ≤ Real.sqrt (((2^k - 1:ℕ)):ℝ) + 1 := by
    have heqN : 2^k - 1 + 1 = 2^k := by have := Nat.one_le_two_pow (n:=k); omega
    have heq : ((2^k:ℕ):ℝ) = (((2^k-1:ℕ)):ℝ) + 1 := by
      rw [← heqN]; push_cast; ring
    rw [heq, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [add_sq, Real.sq_sqrt (by positivity)]
    nlinarith [Real.sqrt_nonneg (((2^k-1:ℕ)):ℝ)]
  push_cast
  linarith

private lemma key45 (n : ℕ) (hn : 2145 ≤ n) :
    (16/45 * Real.sqrt (n:ℝ)) * (Real.sqrt (n:ℝ) + 2) < (64/143) * (n:ℝ) := by
  have hn45 : (45:ℝ) < Real.sqrt (n:ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]; exact_mod_cast (by omega : 2025 < n)
  have hstep2 : (Real.sqrt (n:ℝ) + 2) ≤ (47/45)*Real.sqrt (n:ℝ) := by nlinarith [hn45]
  have hsq : Real.sqrt (n:ℝ)*Real.sqrt (n:ℝ) = (n:ℝ) := by
    rw [← sq, Real.sq_sqrt (by positivity)]
  calc (16/45 * Real.sqrt (n:ℝ)) * (Real.sqrt (n:ℝ) + 2)
      ≤ (16/45 * Real.sqrt (n:ℝ)) * ((47/45)*Real.sqrt (n:ℝ)) :=
        mul_le_mul_of_nonneg_left hstep2 (by positivity)
    _ = (752/2025)*(n:ℝ) := by
        rw [show (16/45 * Real.sqrt (n:ℝ)) * ((47/45)*Real.sqrt (n:ℝ))
            = (752/2025)*(Real.sqrt (n:ℝ)*Real.sqrt (n:ℝ)) by ring, hsq]
    _ < (64/143)*(n:ℝ) := by
        apply mul_lt_mul_of_pos_right (by norm_num : (752:ℝ)/2025 < 64/143)
        exact_mod_cast (by omega : 0 < n)

private lemma card_divisors_le_of_rad (n : ℕ) (hn0 : n ≠ 0)
    (hcard : n.primeFactors.card = 4) (h2not : 2 ∉ n.primeFactors)
    (hrad : (2025:ℝ) ≤ ∏ q ∈ n.primeFactors, (q:ℝ)) :
    ((Nat.divisors n).card : ℝ) ≤ 16/45 * Real.sqrt (n:ℝ) := by
  have hd2 := Commons.NumberTheory.DivisorSum.card_divisors_sq_le_mul_prod n hn0
  have hprod_eq : (∏ q ∈ n.primeFactors, (if q = 2 then (9:ℝ)/4 else 4/(q:ℝ)))
      = 256 / (∏ q ∈ n.primeFactors, (q:ℝ)) := by
    have hc : (∏ q ∈ n.primeFactors, (if q = 2 then (9:ℝ)/4 else 4/(q:ℝ)))
        = ∏ q ∈ n.primeFactors, (4/(q:ℝ)) := by
      apply Finset.prod_congr rfl; intro q hq
      rw [if_neg]; intro h; exact h2not (h ▸ hq)
    rw [hc, Finset.prod_div_distrib, Finset.prod_const, hcard]
    norm_num
  have hsq : ((Nat.divisors n).card : ℝ)^2 ≤ (16/45)^2 * (n:ℝ) := by
    rw [hprod_eq] at hd2
    have hle : 256 / (∏ q ∈ n.primeFactors, (q:ℝ)) ≤ 256/2025 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hrad
    calc ((Nat.divisors n).card : ℝ)^2 ≤ (n:ℝ) * (256 / ∏ q ∈ n.primeFactors, (q:ℝ)) := hd2
      _ ≤ (n:ℝ) * (256/2025) := by apply mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (16/45)^2 * (n:ℝ) := by norm_num; ring
  have hnn : (0:ℝ) ≤ ((Nat.divisors n).card : ℝ) := by positivity
  calc ((Nat.divisors n).card : ℝ) ≤ Real.sqrt ((16/45)^2 * (n:ℝ)) :=
        (Real.le_sqrt hnn (by positivity)).mpr hsq
    _ = 16/45 * Real.sqrt (n:ℝ) := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ (16/45)^2), Real.sqrt_sq (by norm_num)]

private lemma three_mem (k : ℕ) (hk : 2 ≤ k) (h : (2 ^ k - 1).primeFactors.card = 4)
    (h1 : Nat.totient (2 ^ k - 1) ≤ 2 ^ (k - 1) - 1) :
    3 ∈ (2 ^ k - 1).primeFactors := by
  by_contra h3
  set n := 2^k - 1 with hn_def
  have h2k : 2 ≤ 2^k := by
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hn0 : n ≠ 0 := by rw [hn_def]; omega
  have hcardS : n.primeFactors.card = 4 := by rw [hn_def]; exact h
  have hphi2n : 2 * Nat.totient n < n := by rw [hn_def]; exact totient_two_mul_lt k hk h1
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hratio : ∏ p ∈ n.primeFactors, (1 - 1/(p:ℝ)) < 1/2 := by
    rw [← euler_real n hn0, div_lt_iff₀ hnpos]
    have : 2 * (Nat.totient n : ℝ) < (n:ℝ) := by exact_mod_cast hphi2n
    linarith
  have hSprime : ∀ p ∈ n.primeFactors, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors hp
  have h2not : 2 ∉ n.primeFactors := by rw [hn_def]; exact two_not_mem_pow k (by omega)
  have hge5 : ∀ x ∈ n.primeFactors, 5 ≤ x := by
    intro x hx
    have hx2 : x ≠ 2 := by intro hh; exact h2not (hh ▸ hx)
    have hx3 : x ≠ 3 := by intro hh; exact h3 (by rw [hn_def]; exact hh ▸ hx)
    exact prime_ge_five_of_ne_two_three (hSprime x hx) hx2 hx3
  have hb := bound_4_ge5 n.primeFactors hSprime hge5 hcardS
  have hgt : (1/2:ℝ) < (2880:ℝ)/5005 := by norm_num
  linarith [hb, hratio, hgt]

private lemma five_mem (k : ℕ) (hk : 2 ≤ k) (h : (2 ^ k - 1).primeFactors.card = 4)
    (h1 : Nat.totient (2 ^ k - 1) ≤ 2 ^ (k - 1) - 1) (h3 : 3 ∈ (2 ^ k - 1).primeFactors) :
    5 ∈ (2 ^ k - 1).primeFactors := by
  by_contra h5
  set n := 2^k - 1 with hn_def
  have h2k : 2 ≤ 2^k := by
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hn0 : n ≠ 0 := by rw [hn_def]; omega
  have hcardS : n.primeFactors.card = 4 := by rw [hn_def]; exact h
  have h3n : 3 ∈ n.primeFactors := by rw [hn_def]; exact h3
  have h5n : 5 ∉ n.primeFactors := by intro hh; exact h5 (by rwa [hn_def] at hh)
  have h2not : 2 ∉ n.primeFactors := by rw [hn_def]; exact two_not_mem_pow k (by omega)
  have hSprime : ∀ p ∈ n.primeFactors, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hphi2n : 2 * Nat.totient n < n := by rw [hn_def]; exact totient_two_mul_lt k hk h1
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hratio : ∏ p ∈ n.primeFactors, (1 - 1/(p:ℝ)) < 1/2 := by
    rw [← euler_real n hn0, div_lt_iff₀ hnpos]
    have : 2 * (Nat.totient n : ℝ) < (n:ℝ) := by exact_mod_cast hphi2n
    linarith
  set T := n.primeFactors.erase 3 with hT
  have hcardT : T.card = 3 := by
    rw [hT, Finset.card_erase_of_mem h3n, hcardS]
  have hTprime : ∀ x ∈ T, Nat.Prime x := fun x hx => hSprime x (Finset.mem_of_mem_erase hx)
  have hTge7 : ∀ x ∈ T, 7 ≤ x := by
    intro x hx
    have hxS : x ∈ n.primeFactors := Finset.mem_of_mem_erase hx
    have hx3 : x ≠ 3 := (Finset.mem_erase.mp hx).1
    have hx2 : x ≠ 2 := by intro hh; exact h2not (hh ▸ hxS)
    have hx5 : x ≠ 5 := by intro hh; exact h5n (hh ▸ hxS)
    exact prime_ge_seven_of_ne_two_three_five (hSprime x hxS) hx2 hx3 hx5
  have hsplit3 : ∏ p ∈ n.primeFactors, (1-1/(p:ℝ)) = (2/3) * ∏ p ∈ T, (1-1/(p:ℝ)) := by
    rw [hT]
    rw [← Finset.prod_erase_mul n.primeFactors (fun p => 1 - 1/(p:ℝ)) h3n]
    rw [show (1 - 1/((3:ℕ):ℝ)) = (2:ℝ)/3 by norm_num]; ring
  rw [hsplit3] at hratio
  by_cases h7T : 7 ∈ T
  · set U := T.erase 7 with hU
    have hcardU : U.card = 2 := by
      rw [hU, Finset.card_erase_of_mem h7T, hcardT]
    have hUprime : ∀ x ∈ U, Nat.Prime x := fun x hx => hTprime x (Finset.mem_of_mem_erase hx)
    have hUge11 : ∀ x ∈ U, 11 ≤ x := by
      intro x hx
      have hxT : x ∈ T := Finset.mem_of_mem_erase hx
      have hx7 : x ≠ 7 := (Finset.mem_erase.mp hx).1
      exact prime_ge_eleven_of_ne_seven (hTprime x hxT) (hTge7 x hxT) hx7
    have hsplit7 : ∏ p ∈ T, (1-1/(p:ℝ)) = (6/7) * ∏ p ∈ U, (1-1/(p:ℝ)) := by
      rw [hU]
      rw [← Finset.prod_erase_mul T (fun p => 1 - 1/(p:ℝ)) h7T]
      rw [show (1 - 1/((7:ℕ):ℝ)) = (6:ℝ)/7 by norm_num]; ring
    by_cases hU17 : ∃ x ∈ U, x < 17
    · obtain ⟨x, hxU, hxlt⟩ := hU17
      have hxS : x ∈ n.primeFactors :=
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hxU)
      rcases eq_eleven_or_thirteen_of_lt17 (hUprime x hxU) (hUge11 x hxU) hxlt with hx11 | hx13
      · subst hx11
        have h11 : 11 ∈ n.primeFactors := hxS
        have d11 : 10 ∣ k := by
          have := order_dvd_of_dvd 11 k (by norm_num) ((Nat.mem_primeFactors.mp h11).2.1)
          rwa [orderOf_two_eleven] at this
        have h7S : 7 ∈ n.primeFactors := Finset.mem_of_mem_erase h7T
        have d3k : 3 ∣ k := by
          have := order_dvd_of_dvd 7 k (by norm_num) ((Nat.mem_primeFactors.mp h7S).2.1)
          rwa [orderOf_two_seven] at this
        have h30 : 30 ∣ k := by
          have h103 : Nat.Coprime 10 3 := by decide
          have h30' : 10 * 3 ∣ k := Nat.Coprime.mul_dvd_of_dvd_of_dvd h103 d11 d3k
          norm_num at h30'; exact h30'
        have h31 : 31 ∈ n.primeFactors := by
          refine Nat.mem_primeFactors.mpr ⟨by norm_num, ?_, hn0⟩
          exact dvd_trans (by norm_num : (31:ℕ) ∣ 2^30-1) (Nat.pow_sub_one_dvd_pow_sub_one 2 h30)
        have h151 : 151 ∈ n.primeFactors := by
          refine Nat.mem_primeFactors.mpr ⟨by norm_num, ?_, hn0⟩
          exact dvd_trans (by norm_num : (151:ℕ) ∣ 2^30-1) (Nat.pow_sub_one_dvd_pow_sub_one 2 h30)
        have hsub : ({3,7,11,31,151} : Finset ℕ) ⊆ n.primeFactors := by
          intro y hy
          fin_cases hy <;> assumption
        have h5le : 5 ≤ n.primeFactors.card := by
          calc 5 = ({3,7,11,31,151}:Finset ℕ).card := by norm_num
            _ ≤ n.primeFactors.card := Finset.card_le_card hsub
        omega
      · subst hx13
        have d13 : 12 ∣ k := by
          have := order_dvd_of_dvd 13 k (by norm_num) ((Nat.mem_primeFactors.mp hxS).2.1)
          rwa [orderOf_two_thirteen] at this
        have h5in : 5 ∈ n.primeFactors := by
          refine Nat.mem_primeFactors.mpr ⟨by norm_num, ?_, hn0⟩
          exact dvd_trans (by norm_num : (5:ℕ) ∣ 2^12-1) (Nat.pow_sub_one_dvd_pow_sub_one 2 d13)
        exact h5n h5in
    · have hUge17 : ∀ x ∈ U, 17 ≤ x := by
        intro x hx
        by_contra hcon
        rw [not_le] at hcon
        exact hU17 ⟨x, hx, hcon⟩
      have hb := bound_2_ge17 U hUprime hUge17 hcardU
      rw [hsplit7] at hratio
      nlinarith [hb, hratio]
  · have hTge11 : ∀ x ∈ T, 11 ≤ x := by
      intro x hx
      have hx7 : x ≠ 7 := by intro hh; exact h7T (hh ▸ hx)
      exact prime_ge_eleven_of_ne_seven (hTprime x hx) (hTge7 x hx) hx7
    have hb := bound_3_ge11 T hTprime hTge11 hcardT
    nlinarith [hb, hratio]

private lemma case_seven (k : ℕ) (hk : 2 ≤ k) (h : (2 ^ k - 1).primeFactors.card = 4)
    (h3 : 3 ∈ (2 ^ k - 1).primeFactors) (h5 : 5 ∈ (2 ^ k - 1).primeFactors)
    (h7 : 7 ∈ (2 ^ k - 1).primeFactors) :
    (Nat.divisors (2 ^ k - 1)).card * (Nat.sqrt (2 ^ k) + 1) < Nat.totient (2 ^ k - 1) := by
  have h2k : 2 ≤ 2^k := by
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hn0 : (2^k-1:ℕ) ≠ 0 := by omega
  have pr (q : ℕ) (hq : Nat.Prime q) (hd : q ∣ 2^k-1) : q ∈ (2^k-1).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, hd, hn0⟩
  have d3 : 2 ∣ k := by
    have := order_dvd_of_dvd 3 k (by norm_num) ((Nat.mem_primeFactors.mp h3).2.1)
    rwa [orderOf_two_three] at this
  have d5 : 4 ∣ k := by
    have := order_dvd_of_dvd 5 k (by norm_num) ((Nat.mem_primeFactors.mp h5).2.1)
    rwa [orderOf_two_five] at this
  have d7 : 3 ∣ k := by
    have := order_dvd_of_dvd 7 k (by norm_num) ((Nat.mem_primeFactors.mp h7).2.1)
    rwa [orderOf_two_seven] at this
  have d12 : 12 ∣ k := by
    have h43 : Nat.Coprime 4 3 := by decide
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd h43 d5 d7
    norm_num at this ⊢
    exact this
  have h13 : 13 ∈ (2^k-1).primeFactors :=
    pr 13 (by norm_num) (dvd_trans (by norm_num : (13:ℕ) ∣ 2^12-1)
      (Nat.pow_sub_one_dvd_pow_sub_one 2 d12))
  have hSeq : (2^k-1).primeFactors = {3,5,7,13} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    · rw [h]; norm_num
  have hk12 : k = 12 := by
    by_contra hne
    obtain ⟨m, hm⟩ := d12
    have hm2 : 2 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · omega
      · have : m ≠ 1 := by rintro rfl; omega
        omega
    obtain ⟨l, hlprime, hldvd⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
    have hl3 : l = 2 ∨ l = 3 ∨ 5 ≤ l := by
      by_contra hcon
      simp only [not_or, not_le] at hcon
      obtain ⟨h2,h3',hlt⟩ := hcon
      have h2le := hlprime.two_le
      interval_cases l
      · exact h2 rfl
      · exact h3' rfl
      · exact absurd hlprime (by norm_num)
    rcases hl3 with rfl | rfl | hl5
    · have h8 : 8 ∣ k := by
        obtain ⟨m', hm'⟩ := hldvd
        exact ⟨3*m', by rw [hm, hm']; ring⟩
      have h17 : 17 ∈ (2^k-1).primeFactors :=
        pr 17 (by norm_num) (dvd_trans (by norm_num : (17:ℕ) ∣ 2^8-1)
          (Nat.pow_sub_one_dvd_pow_sub_one 2 h8))
      rw [hSeq] at h17
      norm_num at h17
    · have h9 : 9 ∣ k := by
        obtain ⟨m', hm'⟩ := hldvd
        exact ⟨4*m', by rw [hm, hm']; ring⟩
      have h73 : 73 ∈ (2^k-1).primeFactors :=
        pr 73 (by norm_num) (dvd_trans (by norm_num : (73:ℕ) ∣ 2^9-1)
          (Nat.pow_sub_one_dvd_pow_sub_one 2 h9))
      rw [hSeq] at h73
      norm_num at h73
    · have hldk : l ∣ k := by rw [hm]; exact dvd_mul_of_dvd_right hldvd 12
      have h2l : 2^l - 1 ∣ 2^k - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 hldk
      have hne1 : 2^l - 1 ≠ 1 := by
        have hlt : 2^1 < 2^l := Nat.pow_lt_pow_right (by norm_num) (by omega : 1 < l)
        omega
      obtain ⟨q, hqprime, hqdvd⟩ := Nat.exists_prime_and_dvd hne1
      have hqS : q ∈ (2^k-1).primeFactors := pr q hqprime (dvd_trans hqdvd h2l)
      rw [hSeq] at hqS
      have hord : orderOf (2 : ZMod q) ∣ l := order_dvd_of_dvd q l hqprime hqdvd
      have h23 : 2 ∣ l ∨ 3 ∣ l := by
        fin_cases hqS
        · left; rw [orderOf_two_three] at hord; exact hord
        · left; rw [orderOf_two_five] at hord; exact dvd_trans (by norm_num : (2:ℕ) ∣ 4) hord
        · right; rw [orderOf_two_seven] at hord; exact hord
        · left; rw [orderOf_two_thirteen] at hord
          exact dvd_trans (by norm_num : (2:ℕ) ∣ 12) hord
      rcases h23 with h2l' | h3l'
      · have : l = 2 := (hlprime.dvd_iff_eq (by norm_num : (2:ℕ) ≠ 1)).mp h2l'
        omega
      · have : l = 3 := (hlprime.dvd_iff_eq (by norm_num : (3:ℕ) ≠ 1)).mp h3l'
        omega
  subst hk12
  have hcarddiv : (Nat.divisors (2^12-1)).card = 24 := by
    rw [Nat.card_divisors (by norm_num : (2^12-1:ℕ) ≠ 0)]
    rw [hSeq]
    rw [Finset.prod_insert (by decide : (3:ℕ) ∉ ({5,7,13}:Finset ℕ)),
        Finset.prod_insert (by decide : (5:ℕ) ∉ ({7,13}:Finset ℕ)),
        Finset.prod_insert (by decide : (7:ℕ) ∉ ({13}:Finset ℕ)),
        Finset.prod_singleton]
    rw [show (2^12-1:ℕ).factorization 3 = 2 by
          rw [show (2^12-1:ℕ) = 3^2 * 455 by norm_num,
              Nat.factorization_mul_apply_of_coprime (by norm_num : Nat.Coprime (3^2) 455),
              Nat.factorization_pow_self (by norm_num : Nat.Prime 3),
              Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (3:ℕ) ∣ 455)]]
    rw [show (2^12-1:ℕ).factorization 5 = 1 by
          rw [show (2^12-1:ℕ) = 5 * 819 by norm_num,
              Nat.factorization_mul_apply_of_coprime (by norm_num : Nat.Coprime 5 819),
              Nat.Prime.factorization_self (by norm_num : Nat.Prime 5),
              Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (5:ℕ) ∣ 819)]]
    rw [show (2^12-1:ℕ).factorization 7 = 1 by
          rw [show (2^12-1:ℕ) = 7 * 585 by norm_num,
              Nat.factorization_mul_apply_of_coprime (by norm_num : Nat.Coprime 7 585),
              Nat.Prime.factorization_self (by norm_num : Nat.Prime 7),
              Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (7:ℕ) ∣ 585)]]
    rw [show (2^12-1:ℕ).factorization 13 = 1 by
          rw [show (2^12-1:ℕ) = 13 * 315 by norm_num,
              Nat.factorization_mul_apply_of_coprime (by norm_num : Nat.Coprime 13 315),
              Nat.Prime.factorization_self (by norm_num : Nat.Prime 13),
              Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ (13:ℕ) ∣ 315)]]
    norm_num
  have hsqrt : Nat.sqrt (2^12) = 64 := by
    rw [show (2:ℕ)^12 = 64^2 by norm_num, Nat.sqrt_eq']
  have htot : Nat.totient (2^12-1) = 1728 := by decide
  rw [hcarddiv, hsqrt, htot]; norm_num

private lemma case_no_seven (k : ℕ) (hk : 2 ≤ k) (h : (2 ^ k - 1).primeFactors.card = 4)
    (h3 : 3 ∈ (2 ^ k - 1).primeFactors) (h5 : 5 ∈ (2 ^ k - 1).primeFactors)
    (h7 : 7 ∉ (2 ^ k - 1).primeFactors) :
    (Nat.divisors (2 ^ k - 1)).card * (Nat.sqrt (2 ^ k) + 1) < Nat.totient (2 ^ k - 1) := by
  have hk1 : 1 ≤ k := by omega
  have h2k : 2 ≤ 2^k := by
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) (by omega)
  set n := 2^k - 1 with hn_def
  have hn0 : n ≠ 0 := by rw [hn_def]; omega
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hcardS : n.primeFactors.card = 4 := by rw [hn_def]; exact h
  have h3n : 3 ∈ n.primeFactors := by rw [hn_def]; exact h3
  have h5n : 5 ∈ n.primeFactors := by rw [hn_def]; exact h5
  have h7n : 7 ∉ n.primeFactors := by intro hh; exact h7 (by rwa [hn_def] at hh)
  have h2not : 2 ∉ n.primeFactors := by rw [hn_def]; exact two_not_mem_pow k hk1
  have hSprime : ∀ p ∈ n.primeFactors, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors hp
  have h5er : 5 ∈ n.primeFactors.erase 3 := Finset.mem_erase.mpr ⟨by norm_num, h5n⟩
  set U := (n.primeFactors.erase 3).erase 5 with hU
  have hcardU : U.card = 2 := by
    rw [hU, Finset.card_erase_of_mem h5er, Finset.card_erase_of_mem h3n, hcardS]
  have hUprime : ∀ x ∈ U, Nat.Prime x := fun x hx =>
    hSprime x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
  have hUge11 : ∀ x ∈ U, 11 ≤ x := by
    intro x hx
    have hxS : x ∈ n.primeFactors := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
    have hx5 : x ≠ 5 := (Finset.mem_erase.mp hx).1
    have hx3 : x ≠ 3 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
    have hx2 : x ≠ 2 := by intro hh; exact h2not (hh ▸ hxS)
    have hx7 : x ≠ 7 := by intro hh; exact h7n (hh ▸ hxS)
    exact prime_ge_eleven_of_ne_two_three_five_seven (hSprime x hxS) hx2 hx3 hx5 hx7
  have hprodU := bound_2_ge11 U hUprime hUge11 hcardU
  have hprodUN := prod_U_ge U hUprime hUge11 hcardU
  have hsplit1 : ∏ p ∈ n.primeFactors, (1 - 1/(p:ℝ))
      = (2/3) * ∏ p ∈ n.primeFactors.erase 3, (1-1/(p:ℝ)) := by
    rw [← Finset.prod_erase_mul n.primeFactors (fun p => 1 - 1/(p:ℝ)) h3n]
    rw [show (1 - 1/((3:ℕ):ℝ)) = (2:ℝ)/3 by norm_num]; ring
  have hsplit2 : ∏ p ∈ n.primeFactors.erase 3, (1 - 1/(p:ℝ))
      = (4/5) * ∏ p ∈ U, (1-1/(p:ℝ)) := by
    rw [hU]
    rw [← Finset.prod_erase_mul (n.primeFactors.erase 3) (fun p => 1 - 1/(p:ℝ)) h5er]
    rw [show (1 - 1/((5:ℕ):ℝ)) = (4:ℝ)/5 by norm_num]; ring
  have hphi : (64/143) * (n:ℝ) ≤ (Nat.totient n : ℝ) := by
    have hlb : (64/143:ℝ) ≤ ∏ p ∈ n.primeFactors, (1 - 1/(p:ℝ)) := by
      rw [hsplit1, hsplit2]; nlinarith [hprodU]
    rw [← euler_real n hn0] at hlb
    rw [le_div_iff₀ hnpos] at hlb
    linarith
  have hsplitP1 : ∏ p ∈ n.primeFactors, p = 3 * ∏ p ∈ n.primeFactors.erase 3, p := by
    rw [← Finset.prod_erase_mul n.primeFactors (fun p => p) h3n]; ring
  have hsplitP2 : ∏ p ∈ n.primeFactors.erase 3, p = 5 * ∏ p ∈ U, p := by
    rw [hU]
    rw [← Finset.prod_erase_mul (n.primeFactors.erase 3) (fun p => p) h5er]; ring
  have hradN : 2145 ≤ ∏ p ∈ n.primeFactors, p := by
    rw [hsplitP1, hsplitP2]; nlinarith [hprodUN]
  have hrad : (2025:ℝ) ≤ ∏ p ∈ n.primeFactors, (p:ℝ) := by
    have h2145 : (2145:ℝ) ≤ ((∏ p ∈ n.primeFactors, p : ℕ):ℝ) := by exact_mod_cast hradN
    have hcast : ((∏ p ∈ n.primeFactors, p : ℕ):ℝ) = ∏ p ∈ n.primeFactors, (p:ℝ) := by
      push_cast; ring
    rw [hcast] at h2145; linarith
  have hn2145 : 2145 ≤ n := by
    have hdvd : ∏ p ∈ n.primeFactors, p ≤ n :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.prod_primeFactors_dvd n)
    omega
  have hcard_le : ((Nat.divisors n).card : ℝ) ≤ 16/45 * Real.sqrt (n:ℝ) :=
    card_divisors_le_of_rad n hn0 hcardS h2not hrad
  rw [hn_def] at hcard_le hphi
  have hsqrt := sqrt_pow_add_one_le k hk1
  have hkey := key45 n hn2145
  rw [hn_def] at hkey
  have : ((Nat.divisors (2^k-1)).card : ℝ) * ((Nat.sqrt (2^k) + 1 : ℕ) : ℝ)
      < (Nat.totient (2^k-1) : ℝ) := by
    calc ((Nat.divisors (2^k-1)).card : ℝ) * ((Nat.sqrt (2^k)+1:ℕ):ℝ)
        ≤ (16/45 * Real.sqrt ((2^k-1:ℕ):ℝ)) * (Real.sqrt ((2^k-1:ℕ):ℝ) + 2) :=
          mul_le_mul hcard_le hsqrt (by positivity) (by positivity)
      _ < (64/143) * ((2^k-1:ℕ):ℝ) := hkey
      _ ≤ (Nat.totient (2^k-1) : ℝ) := hphi
  exact_mod_cast this

theorem primeFactors_card_four (k : ℕ) (hk : 2 ≤ k)
    (h : (2 ^ k - 1).primeFactors.card = 4)
    (h1 : Nat.totient (2 ^ k - 1) ≤ 2 ^ (k - 1) - 1) :
    (Nat.divisors (2 ^ k - 1)).card * (Nat.sqrt (2 ^ k) + 1) < Nat.totient (2 ^ k - 1) := by
  have h3 := three_mem k hk h h1
  have h5 := five_mem k hk h h1 h3
  by_cases h7 : 7 ∈ (2 ^ k - 1).primeFactors
  · exact case_seven k hk h h3 h5 h7
  · exact case_no_seven k hk h h3 h5 h7

end Commons.NumberTheory.TwoPow