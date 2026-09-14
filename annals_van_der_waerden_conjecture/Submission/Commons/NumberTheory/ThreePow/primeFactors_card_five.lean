import Mathlib
import Submission.Commons.NumberTheory.OrderModulo.order_pow_sub_one_dvd
import Submission.Commons.NumberTheory.ThreePow.primeFactors_card_four
import Submission.Commons.NumberTheory.Nat.prod_nth_prime_le_prod_of_le
import Submission.Commons.NumberTheory.Totient.totient_sq_ge_divisors_sq_mul_kmin

namespace Commons.NumberTheory.ThreePow

open Finset

set_option maxHeartbeats 1600000

/-! ## Orders of `3` modulo the small primes `5, 7, 11` -/

lemma orderOf_three_mod_eleven : orderOf (((3:ℕ)) : ZMod 11) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  apply orderOf_eq_prime <;> decide

lemma five_dvd_of_eleven_dvd (k : ℕ) (h : 11 ∣ 3^k - 1) : 5 ∣ k := by
  have h1 := Commons.NumberTheory.OrderModulo.order_pow_sub_one_dvd 3 11 (by norm_num) (by norm_num) h
  rwa [orderOf_three_mod_eleven] at h1

/-! ## `5, 7, 11` cannot all divide `3 ^ k - 1` -/

/-- If `5, 7, 11` all divide `3 ^ k - 1`, then `60 ∣ k`, whence `3 ^ 60 - 1 ∣ 3 ^ k - 1`
and `3 ^ 60 - 1` has at least the six distinct prime factors `2, 5, 7, 11, 13, 73`. -/
lemma not_all_5_7_11 (k : ℕ) (hk : 2 ≤ k) (hcard : (3 ^ k - 1).primeFactors.card = 5) :
    ¬ (5 ∈ (3 ^ k - 1).primeFactors ∧ 7 ∈ (3 ^ k - 1).primeFactors ∧
       11 ∈ (3 ^ k - 1).primeFactors) := by
  rintro ⟨h5, h7, h11⟩
  have hn0 : 3 ^ k - 1 ≠ 0 := by
    have : 1 < 3 ^ k := one_lt_pow₀ (by norm_num : (1:ℕ) < 3) (by omega)
    omega
  have d5 : 5 ∣ 3 ^ k - 1 := Nat.dvd_of_mem_primeFactors h5
  have d7 : 7 ∣ 3 ^ k - 1 := Nat.dvd_of_mem_primeFactors h7
  have d11 : 11 ∣ 3 ^ k - 1 := Nat.dvd_of_mem_primeFactors h11
  have h4 : 4 ∣ k := four_dvd_of_five_dvd k d5
  have h6 : 6 ∣ k := six_dvd_of_seven_dvd k d7
  have h5k : 5 ∣ k := five_dvd_of_eleven_dvd k d11
  have h12 : 12 ∣ k := by
    have := Nat.lcm_dvd h4 h6
    rwa [show Nat.lcm 4 6 = 12 from by decide] at this
  have h2dvd : 2 ∣ 3 ^ k - 1 := by
    rw [← ZMod.natCast_eq_zero_iff (3 ^ k - 1) 2]
    rw [Nat.cast_sub (Nat.one_le_pow k 3 (by norm_num)), Nat.cast_pow]
    have h3 : (((3:ℕ)) : ZMod 2) = 1 := by decide
    rw [h3, one_pow]; simp
  have h13dvd : 13 ∣ 3 ^ k - 1 :=
    dvd_trans (by norm_num : 13 ∣ 3 ^ 12 - 1) (Nat.pow_sub_one_dvd_pow_sub_one 3 h12)
  have h73dvd : 73 ∣ 3 ^ k - 1 :=
    dvd_trans (by norm_num : 73 ∣ 3 ^ 12 - 1) (Nat.pow_sub_one_dvd_pow_sub_one 3 h12)
  have h2mem : 2 ∈ (3 ^ k - 1).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨by norm_num, h2dvd, hn0⟩
  have h13mem : 13 ∈ (3 ^ k - 1).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨by norm_num, h13dvd, hn0⟩
  have h73mem : 73 ∈ (3 ^ k - 1).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨by norm_num, h73dvd, hn0⟩
  have hsub : ({2,5,7,11,13,73} : Finset ℕ) ⊆ (3 ^ k - 1).primeFactors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h2mem
    · exact h5
    · exact h7
    · exact h11
    · exact h13mem
    · exact h73mem
  have h6le : 6 ≤ (3 ^ k - 1).primeFactors.card := by
    have := Finset.card_le_card hsub
    simpa using this
  exact absurd h6le (by rw [hcard]; norm_num)

noncomputable def KM : ℕ → ℝ := fun q => ((q:ℝ) - 1)^2 / (4*(q:ℝ))

lemma KM_nonneg (q : ℕ) : 0 ≤ KM q := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · norm_num [KM]
  · rw [KM]; positivity

lemma KM_le_succ (n : ℕ) : KM n ≤ KM (n+1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num [KM]
  · have hnR : (0:ℝ) < n := by exact_mod_cast hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    rw [KM, KM]
    have hcast : (((n+1:ℕ)):ℝ) = (n:ℝ)+1 := by push_cast; ring
    rw [hcast]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ((n:ℝ)-1), hn1]

lemma KM_mono : Monotone KM := monotone_nat_of_le_succ KM_le_succ

lemma KM5 : KM 5 = 4/5 := by norm_num [KM]
lemma KM7 : KM 7 = 9/7 := by norm_num [KM]
lemma KM11 : KM 11 = 25/11 := by norm_num [KM]
lemma KM13 : KM 13 = 36/13 := by norm_num [KM]
lemma KM17 : KM 17 = 64/17 := by norm_num [KM]

lemma five_le_of_prime {x : ℕ} (hx : Nat.Prime x) (h2 : x ≠ 2) (h3 : x ≠ 3) : 5 ≤ x := by
  by_contra h; push_neg at h
  have hx2 : 2 ≤ x := hx.two_le
  interval_cases x
  · exact h2 rfl
  · exact h3 rfl
  · norm_num at hx

lemma thirteen_le_of_prime {x : ℕ} (hx : Nat.Prime x) (h2 : x ≠ 2) (h3 : x ≠ 3)
    (h5 : x ≠ 5) (h7 : x ≠ 7) (h11 : x ≠ 11) : 13 ≤ x := by
  by_contra h; push_neg at h
  have hx2 : 2 ≤ x := hx.two_le
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
  · exact h11 rfl
  · norm_num at hx

lemma nth_prime_3 : Nat.nth Nat.Prime 3 = 7 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 7) (by norm_num)
  have hc : Nat.count Nat.Prime 7 = 3 := by decide
  rwa [hc] at h
lemma nth_prime_4 : Nat.nth Nat.Prime 4 = 11 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 11) (by norm_num)
  have hc : Nat.count Nat.Prime 11 = 4 := by decide
  rwa [hc] at h
lemma nth_prime_5 : Nat.nth Nat.Prime 5 = 13 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 13) (by norm_num)
  have hc : Nat.count Nat.Prime 13 = 5 := by decide
  rwa [hc] at h
lemma nth_prime_6 : Nat.nth Nat.Prime 6 = 17 := by
  have h := Nat.nth_count (p := Nat.Prime) (n := 17) (by norm_num)
  have hc : Nat.count Nat.Prime 17 = 6 := by decide
  rwa [hc] at h

private lemma KM_nth_le (S : Finset ℕ) (m : ℕ) (hS : ∀ x ∈ S, Nat.Prime x) (hm : ∀ x ∈ S, m ≤ x) :
    (∏ i ∈ Finset.range S.card, KM (Nat.nth Nat.Prime (Nat.count Nat.Prime m + i))) ≤ ∏ x ∈ S, KM x :=
  Commons.NumberTheory.Nat.prod_nth_prime_le_prod_of_le S m hS hm KM KM_mono KM_nonneg

private lemma nat_nth_le (S : Finset ℕ) (m : ℕ) (hS : ∀ x ∈ S, Nat.Prime x) (hm : ∀ x ∈ S, m ≤ x) :
    (∏ i ∈ Finset.range S.card, Nat.nth Nat.Prime (Nat.count Nat.Prime m + i)) ≤ ∏ x ∈ S, x := by
  have h := Commons.NumberTheory.Nat.prod_nth_prime_le_prod_of_le S m hS hm
      (fun q : ℕ => ((q:ℕ):ℝ)) (fun a b hab => Nat.cast_le.mpr hab) (fun q => Nat.cast_nonneg q)
  have hL : (∏ i ∈ Finset.range S.card, ((Nat.nth Nat.Prime (Nat.count Nat.Prime m + i) : ℕ):ℝ))
      = ((∏ i ∈ Finset.range S.card, Nat.nth Nat.Prime (Nat.count Nat.Prime m + i) : ℕ) : ℝ) := by
    push_cast; ring
  have hR : (∏ x ∈ S, ((x:ℕ):ℝ)) = ((∏ x ∈ S, x : ℕ) : ℝ) := by push_cast; ring
  rw [hL, hR] at h
  exact_mod_cast h

-- numeric product bounds
lemma KMb13 (S : Finset ℕ) (hS : ∀ x ∈ S, Nat.Prime x) (hm : ∀ x ∈ S, 13 ≤ x) (hc : S.card = 2) :
    KM 13 * KM 17 ≤ ∏ x ∈ S, KM x := by
  have h := KM_nth_le S 13 hS hm
  rw [hc] at h
  rw [show Nat.count Nat.Prime 13 = 5 from by decide] at h
  simp only [Finset.prod_range_succ, Finset.prod_range_zero] at h
  rw [nth_prime_5, nth_prime_6] at h
  simpa using h

lemma natb13 (S : Finset ℕ) (hS : ∀ x ∈ S, Nat.Prime x) (hm : ∀ x ∈ S, 13 ≤ x) (hc : S.card = 2) :
    13 * 17 ≤ ∏ x ∈ S, x := by
  have h := nat_nth_le S 13 hS hm
  rw [hc] at h
  rw [show Nat.count Nat.Prime 13 = 5 from by decide] at h
  simp only [Finset.prod_range_succ, Finset.prod_range_zero] at h
  rw [nth_prime_5, nth_prime_6] at h
  simpa using h

lemma KMb11 (S : Finset ℕ) (hS : ∀ x ∈ S, Nat.Prime x) (hm : ∀ x ∈ S, 11 ≤ x) (hc : S.card = 3) :
    KM 11 * KM 13 * KM 17 ≤ ∏ x ∈ S, KM x := by
  have h := KM_nth_le S 11 hS hm
  rw [hc] at h
  rw [show Nat.count Nat.Prime 11 = 4 from by decide] at h
  simp only [Finset.prod_range_succ, Finset.prod_range_zero] at h
  rw [nth_prime_4, nth_prime_5, nth_prime_6] at h
  simpa using h

lemma natb11 (S : Finset ℕ) (hS : ∀ x ∈ S, Nat.Prime x) (hm : ∀ x ∈ S, 11 ≤ x) (hc : S.card = 3) :
    11 * 13 * 17 ≤ ∏ x ∈ S, x := by
  have h := nat_nth_le S 11 hS hm
  rw [hc] at h
  rw [show Nat.count Nat.Prime 11 = 4 from by decide] at h
  simp only [Finset.prod_range_succ, Finset.prod_range_zero] at h
  rw [nth_prime_4, nth_prime_5, nth_prime_6] at h
  simpa using h

lemma KMb7 (S : Finset ℕ) (hS : ∀ x ∈ S, Nat.Prime x) (hm : ∀ x ∈ S, 7 ≤ x) (hc : S.card = 4) :
    KM 7 * KM 11 * KM 13 * KM 17 ≤ ∏ x ∈ S, KM x := by
  have h := KM_nth_le S 7 hS hm
  rw [hc] at h
  rw [show Nat.count Nat.Prime 7 = 3 from by decide] at h
  simp only [Finset.prod_range_succ, Finset.prod_range_zero] at h
  rw [nth_prime_3, nth_prime_4, nth_prime_5, nth_prime_6] at h
  simpa using h

lemma natb7 (S : Finset ℕ) (hS : ∀ x ∈ S, Nat.Prime x) (hm : ∀ x ∈ S, 7 ≤ x) (hc : S.card = 4) :
    7 * 11 * 13 * 17 ≤ ∏ x ∈ S, x := by
  have h := nat_nth_le S 7 hS hm
  rw [hc] at h
  rw [show Nat.count Nat.Prime 7 = 3 from by decide] at h
  simp only [Finset.prod_range_succ, Finset.prod_range_zero] at h
  rw [nth_prime_3, nth_prime_4, nth_prime_5, nth_prime_6] at h
  simpa using h

-- now the main case analysis
lemma odd_lower_bounds (T : Finset ℕ) (hprime : ∀ q ∈ T, Nat.Prime q)
    (h5le : ∀ q ∈ T, 5 ≤ q) (hcard : T.card = 4)
    (hex : ¬ (5 ∈ T ∧ 7 ∈ T ∧ 11 ∈ T)) :
    (KM 5 * KM 7 * KM 13 * KM 17 ≤ ∏ q ∈ T, KM q) ∧
    (7735 ≤ ∏ q ∈ T, q) := by
  have hKm11 : KM 7 ≤ KM 11 := KM_mono (by norm_num)
  by_cases h5 : 5 ∈ T
  · by_cases h7 : 7 ∈ T
    · -- T = {5,7} ∪ S, S primes >= 13, card 2
      have h11not : 11 ∉ T := fun h => hex ⟨h5, h7, h⟩
      have h7e : 7 ∈ T.erase 5 := by rw [Finset.mem_erase]; exact ⟨by norm_num, h7⟩
      set S := (T.erase 5).erase 7 with hSdef
      have hcardS : S.card = 2 := by
        rw [hSdef, Finset.card_erase_of_mem h7e, Finset.card_erase_of_mem h5]; omega
      have hSprime : ∀ x ∈ S, Nat.Prime x := by
        intro x hx
        rw [hSdef, Finset.mem_erase, Finset.mem_erase] at hx
        exact hprime x hx.2.2
      have hS13 : ∀ x ∈ S, 13 ≤ x := by
        intro x hx
        rw [hSdef, Finset.mem_erase, Finset.mem_erase] at hx
        obtain ⟨hxne7, hxne5, hxT⟩ := hx
        have hx5 : 5 ≤ x := h5le x hxT
        exact thirteen_le_of_prime (hprime x hxT) (by omega) (by omega) hxne5 hxne7
          (by rintro rfl; exact h11not hxT)
      have hkm := KMb13 S hSprime hS13 hcardS
      have hnat := natb13 S hSprime hS13 hcardS
      have hsplitKM : ∏ q ∈ T, KM q = KM 5 * (KM 7 * ∏ q ∈ S, KM q) := by
        rw [hSdef, ← Finset.mul_prod_erase T KM h5, ← Finset.mul_prod_erase (T.erase 5) KM h7e]
      have hsplitQ : ∏ q ∈ T, q = 5 * (7 * ∏ q ∈ S, q) := by
        rw [hSdef, ← Finset.mul_prod_erase T (fun q => q) h5,
            ← Finset.mul_prod_erase (T.erase 5) (fun q => q) h7e]
      constructor
      · rw [hsplitKM]
        calc KM 5 * KM 7 * KM 13 * KM 17 = (KM 5 * KM 7) * (KM 13 * KM 17) := by ring
          _ ≤ (KM 5 * KM 7) * ∏ q ∈ S, KM q :=
              mul_le_mul_of_nonneg_left hkm (mul_nonneg (KM_nonneg 5) (KM_nonneg 7))
          _ = KM 5 * (KM 7 * ∏ q ∈ S, KM q) := by ring
      · rw [hsplitQ]
        have h := Nat.mul_le_mul_left 5 (Nat.mul_le_mul_left 7 hnat)
        simpa using h
    · -- T = {5} ∪ S, S primes >= 11, card 3
      have h5e : 5 ∈ T := h5
      set S := T.erase 5 with hSdef
      have hcardS : S.card = 3 := by rw [hSdef, Finset.card_erase_of_mem h5]; omega
      have hSprime : ∀ x ∈ S, Nat.Prime x := by
        intro x hx; rw [hSdef, Finset.mem_erase] at hx; exact hprime x hx.2
      have hS11 : ∀ x ∈ S, 11 ≤ x := by
        intro x hx
        rw [hSdef, Finset.mem_erase] at hx
        obtain ⟨hxne5, hxT⟩ := hx
        have hx5 : 5 ≤ x := h5le x hxT
        exact eleven_le_of_prime (hprime x hxT) (by omega) (by omega) hxne5
          (by rintro rfl; exact h7 hxT)
      have hkm := KMb11 S hSprime hS11 hcardS
      have hnat := natb11 S hSprime hS11 hcardS
      have hsplitKM : ∏ q ∈ T, KM q = KM 5 * ∏ q ∈ S, KM q := by
        rw [hSdef, ← Finset.mul_prod_erase T KM h5]
      have hsplitQ : ∏ q ∈ T, q = 5 * ∏ q ∈ S, q := by
        rw [hSdef, ← Finset.mul_prod_erase T (fun q => q) h5]
      constructor
      · rw [hsplitKM]
        calc KM 5 * KM 7 * KM 13 * KM 17 = KM 5 * (KM 7 * (KM 13 * KM 17)) := by ring
          _ ≤ KM 5 * (KM 11 * (KM 13 * KM 17)) := by
              apply mul_le_mul_of_nonneg_left _ (KM_nonneg 5)
              apply mul_le_mul_of_nonneg_right hKm11
              exact mul_nonneg (KM_nonneg 13) (KM_nonneg 17)
          _ = KM 5 * (KM 11 * KM 13 * KM 17) := by ring
          _ ≤ KM 5 * ∏ q ∈ S, KM q :=
              mul_le_mul_of_nonneg_left hkm (KM_nonneg 5)
      · rw [hsplitQ]
        have h := Nat.mul_le_mul_left 5 hnat
        have h2 : 7735 ≤ 5 * (11 * 13 * 17) := by norm_num
        exact le_trans h2 h
  · -- 5 not in T; T primes >= 7
    have hS7 : ∀ x ∈ T, 7 ≤ x := by
      intro x hx
      have hx5 : 5 ≤ x := h5le x hx
      exact seven_le_of_prime (hprime x hx) (by omega) (by omega)
        (by rintro rfl; exact h5 hx)
    have hkm := KMb7 T hprime hS7 hcard
    have hnat := natb7 T hprime hS7 hcard
    constructor
    · have h511 : KM 5 ≤ KM 11 := KM_mono (by norm_num)
      have hnon : (0:ℝ) ≤ KM 7 * KM 13 * KM 17 :=
        mul_nonneg (mul_nonneg (KM_nonneg 7) (KM_nonneg 13)) (KM_nonneg 17)
      calc KM 5 * KM 7 * KM 13 * KM 17 = KM 5 * (KM 7 * KM 13 * KM 17) := by ring
        _ ≤ KM 11 * (KM 7 * KM 13 * KM 17) := mul_le_mul_of_nonneg_right h511 hnon
        _ = KM 7 * KM 11 * KM 13 * KM 17 := by ring
        _ ≤ ∏ q ∈ T, KM q := hkm
    · have h2 : 7735 ≤ 7 * 11 * 13 * 17 := by norm_num
      exact le_trans h2 hnat


/-! ## The key reduction: from a lower bound on `∏ kmin` to the target inequality -/

lemma sqrt_add_one_le (x : ℝ) (hx : 0 ≤ x) : Real.sqrt (x + 1) ≤ Real.sqrt x + 1 := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [add_sq, Real.sq_sqrt hx]
  nlinarith [Real.sqrt_nonneg x]

lemma sqrt_nat_sqrt_le (m : ℕ) : ((Nat.sqrt m : ℕ) : ℝ) ≤ Real.sqrt (m : ℝ) := by
  rw [Real.le_sqrt (by positivity) (by positivity)]
  have h := Nat.sqrt_le m
  calc ((Nat.sqrt m : ℕ) : ℝ) ^ 2 = (((Nat.sqrt m) * (Nat.sqrt m) : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((m : ℕ) : ℝ) := by exact_mod_cast h

/-- Scalar core: `64 < (G-1)²·n`, `G ≥ 1`, `n > 0` force `(√n+2)² < G·n`. -/
lemma sq_sqrt_add_two_lt {G : ℝ} {n : ℕ} (hn : 0 < n) (hG : 1 ≤ G)
    (h64 : 64 < (G - 1) ^ 2 * (n : ℝ)) :
    (Real.sqrt (n : ℝ) + 2) ^ 2 < G * (n : ℝ) := by
  have hA : 0 ≤ G - 1 := by linarith
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsn : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; norm_num; exact_mod_cast hn
  have h8 : 8 < (G - 1) * Real.sqrt (n : ℝ) := by
    have hsq : ((G - 1) * Real.sqrt (n : ℝ)) ^ 2 = (G - 1) ^ 2 * (n : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hnR)]
    have hpos : 0 < ((G - 1) * Real.sqrt (n : ℝ) - 8) * ((G - 1) * Real.sqrt (n : ℝ) + 8) := by
      nlinarith [hsq, h64]
    have h2 : 0 < (G - 1) * Real.sqrt (n : ℝ) + 8 := by
      nlinarith [Real.sqrt_nonneg (n : ℝ), hA]
    have h3 : 0 < (G - 1) * Real.sqrt (n : ℝ) - 8 := by nlinarith [hpos, h2]
    linarith
  have hstep : 8 * Real.sqrt (n : ℝ) < (G - 1) * (n : ℝ) := by
    have h1 : (G - 1) * (n : ℝ) = ((G - 1) * Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) := by
      rw [mul_assoc, ← sq, Real.sq_sqrt (le_of_lt hnR)]
    rw [h1]
    exact mul_lt_mul_of_pos_right h8 (Real.sqrt_pos.mpr hnR)
  rw [add_sq, Real.sq_sqrt (le_of_lt hnR)]
  nlinarith [hstep, hsn]

/-- If `G = ∏_{q | 3^k-1} kmin q` satisfies `1 ≤ G` and `64 < (G-1)²·(3^k-1)`,
then `d(n)·(⌊√(3^k)⌋+1) < φ(n)` for `n = 3^k - 1`. -/
lemma disj2_of_kmin_bound (k : ℕ) (hk : 2 ≤ k)
    (hG : 1 ≤ ∏ q ∈ (3 ^ k - 1).primeFactors, (if q = 2 then (1:ℝ)/9 else KM q))
    (h64 : 64 < ((∏ q ∈ (3 ^ k - 1).primeFactors, (if q = 2 then (1:ℝ)/9 else KM q)) - 1) ^ 2
      * (((3 ^ k - 1 : ℕ) : ℝ))) :
    (Nat.divisors (3 ^ k - 1)).card * (Nat.sqrt (3 ^ k) + 1) < Nat.totient (3 ^ k - 1) := by
  set n : ℕ := 3 ^ k - 1 with hn_def
  set G : ℝ := ∏ q ∈ n.primeFactors, (if q = 2 then (1:ℝ)/9 else KM q) with hG_def
  have hpk : 4 ≤ 3 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      _ ≤ 3 ^ k := Nat.pow_le_pow_left (by norm_num) k
  have hn1 : 1 < n := by omega
  have hn0 : n ≠ 0 := by omega
  have hpk_eq : 3 ^ k = n + 1 := by omega
  have hd1 : 0 < (Nat.divisors n).card := by
    rw [Finset.card_pos]
    exact ⟨1, by simp [Nat.mem_divisors, hn0]⟩
  have hdpos : (0 : ℝ) < ((Nat.divisors n).card : ℝ) := by exact_mod_cast hd1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hmain : (((Nat.divisors n).card : ℝ))^2 * (n:ℝ) * G ≤ ((Nat.totient n : ℝ))^2 := by
    have hchild := Commons.NumberTheory.Totient.totient_sq_ge_divisors_sq_mul_kmin n hn0
    have hGeq : G = ∏ q ∈ n.primeFactors,
        (if q = 2 then (1 : ℝ) / 9 else (((q : ℝ) - 1) ^ 2 / (4 * (q : ℝ)))) := by
      rw [hG_def]
      apply Finset.prod_congr rfl
      intro q _
      by_cases hq : q = 2
      · simp [hq]
      · simp only [hq, if_false]; rfl
    rw [hGeq]
    exact hchild
  have hσ : (((Nat.sqrt (3 ^ k) + 1 : ℕ)) : ℝ) ≤ Real.sqrt (n : ℝ) + 2 := by
    have h1 : ((Nat.sqrt (3 ^ k) : ℕ) : ℝ) ≤ Real.sqrt ((3 ^ k : ℕ) : ℝ) := sqrt_nat_sqrt_le _
    have h2 : ((3 ^ k : ℕ) : ℝ) = (n : ℝ) + 1 := by rw [hpk_eq]; push_cast; ring
    push_cast
    rw [h2] at h1
    have := sqrt_add_one_le (n : ℝ) (le_of_lt hnpos)
    linarith
  have hkey : (Real.sqrt (n : ℝ) + 2) ^ 2 < G * (n : ℝ) :=
    sq_sqrt_add_two_lt (by omega) hG h64
  have hσ2 : ((((Nat.sqrt (3 ^ k) + 1 : ℕ)) : ℝ))^2 < G * (n : ℝ) := by
    have h := mul_self_le_mul_self (show (0:ℝ) ≤ (((Nat.sqrt (3 ^ k) + 1 : ℕ)) : ℝ) by positivity) hσ
    rw [sq] at hkey ⊢
    linarith
  have hkey2 : (((Nat.divisors n).card : ℝ) * (((Nat.sqrt (3 ^ k) + 1 : ℕ)) : ℝ))^2
      < ((Nat.totient n : ℝ))^2 := by
    rw [mul_pow]
    calc (((Nat.divisors n).card : ℝ))^2 * ((((Nat.sqrt (3 ^ k) + 1 : ℕ)) : ℝ))^2
        < (((Nat.divisors n).card : ℝ))^2 * (G * (n : ℝ)) :=
          mul_lt_mul_of_pos_left hσ2 (pow_pos hdpos 2)
      _ = (((Nat.divisors n).card : ℝ))^2 * (n:ℝ) * G := by ring
      _ ≤ ((Nat.totient n : ℝ))^2 := hmain
  have hφnn : (0:ℝ) ≤ (Nat.totient n : ℝ) := Nat.cast_nonneg _
  have hdsnn : (0:ℝ) ≤ ((Nat.divisors n).card : ℝ) * (((Nat.sqrt (3 ^ k) + 1 : ℕ)) : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hlt : ((Nat.divisors n).card : ℝ) * (((Nat.sqrt (3 ^ k) + 1 : ℕ)) : ℝ) < (Nat.totient n : ℝ) := by
    nlinarith [hkey2, hφnn, hdsnn]
  exact_mod_cast hlt

/-! ## The main theorem -/

theorem primeFactors_card_five (k : ℕ) (hk : 2 ≤ k)
    (h : (3 ^ k - 1).primeFactors.card = 5)
    (h1 : Nat.totient (3 ^ k - 1) ≤ 3 ^ (k - 1) - 1) :
    (Nat.divisors (3 ^ k - 1)).card * (Nat.sqrt (3 ^ k) + 1) < Nat.totient (3 ^ k - 1) := by
  set P := (3 ^ k - 1).primeFactors with hPdef
  have hn0 : 3 ^ k - 1 ≠ 0 := by
    have : 1 < 3 ^ k := one_lt_pow₀ (by norm_num : (1:ℕ) < 3) (by omega)
    omega
  have h3not : 3 ∉ P := by
    intro h3
    have hd : 3 ∣ 3 ^ k - 1 := Nat.dvd_of_mem_primeFactors h3
    have hp1 : 3 ∣ 3 ^ k := dvd_pow_self 3 (by omega)
    have h2 : 3 ∣ 3 ^ k - (3 ^ k - 1) := Nat.dvd_sub hp1 hd
    have heq : 3 ^ k - (3 ^ k - 1) = 1 := by
      have hle : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by norm_num)
      omega
    rw [heq] at h2; norm_num at h2
  have h2dvd : 2 ∣ 3 ^ k - 1 := by
    rw [← ZMod.natCast_eq_zero_iff (3 ^ k - 1) 2]
    rw [Nat.cast_sub (Nat.one_le_pow k 3 (by norm_num)), Nat.cast_pow]
    have h3 : (((3:ℕ)) : ZMod 2) = 1 := by decide
    rw [h3, one_pow]; simp
  have h2mem : 2 ∈ P := Nat.mem_primeFactors.mpr ⟨by norm_num, h2dvd, hn0⟩
  set T := P.erase 2 with hTdef
  have hcardT : T.card = 4 := by
    rw [hTdef, Finset.card_erase_of_mem h2mem]
    omega
  have hprime : ∀ q ∈ T, Nat.Prime q := by
    intro q hq
    exact Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq)
  have h5le : ∀ q ∈ T, 5 ≤ q := by
    intro q hq
    have hqP : q ∈ P := Finset.mem_of_mem_erase hq
    have hqne2 : q ≠ 2 := (Finset.mem_erase.mp hq).1
    exact five_le_of_prime (Nat.prime_of_mem_primeFactors hqP)
      hqne2 (fun hq3 => h3not (hq3 ▸ hqP))
  have hex : ¬ (5 ∈ T ∧ 7 ∈ T ∧ 11 ∈ T) := by
    rintro ⟨h5, h7, h11⟩
    exact not_all_5_7_11 k hk h
      ⟨Finset.mem_of_mem_erase h5, Finset.mem_of_mem_erase h7, Finset.mem_of_mem_erase h11⟩
  obtain ⟨hKMlb, hqlb⟩ := odd_lower_bounds T hprime h5le hcardT hex
  -- split the product over `P` into the factor `2` and the odd part
  have hGsplit : ∏ q ∈ P, (if q = 2 then (1:ℝ)/9 else KM q) = (1/9) * ∏ q ∈ T, KM q := by
    rw [hTdef, ← Finset.mul_prod_erase P (fun q => if q = 2 then (1:ℝ)/9 else KM q) h2mem]
    rw [if_pos rfl]
    congr 1
    apply Finset.prod_congr rfl
    intro q hq
    exact if_neg (Finset.mem_erase.mp hq).1
  have hsplitQ : ∏ q ∈ P, q = 2 * ∏ q ∈ T, q := by
    rw [hTdef, ← Finset.mul_prod_erase P (fun q => q) h2mem]
  have hGval : (9216/7735 : ℝ) ≤ ∏ q ∈ P, (if q = 2 then (1:ℝ)/9 else KM q) := by
    rw [hGsplit]
    have h1 : (9216/7735 : ℝ) ≤ (1/9) * (KM 5 * KM 7 * KM 13 * KM 17) := by
      rw [KM5, KM7, KM13, KM17]; norm_num
    have h2 : (1/9) * (KM 5 * KM 7 * KM 13 * KM 17) ≤ (1/9) * ∏ q ∈ T, KM q :=
      mul_le_mul_of_nonneg_left hKMlb (by norm_num)
    linarith [h1, h2]
  have hG : 1 ≤ ∏ q ∈ P, (if q = 2 then (1:ℝ)/9 else KM q) := by
    have h1 : (1:ℝ) ≤ 9216/7735 := by norm_num
    linarith [hGval, h1]
  have hnv : (15470 : ℝ) ≤ ((3 ^ k - 1 : ℕ) : ℝ) := by
    have hdvd : (∏ q ∈ P, q) ∣ 3 ^ k - 1 := Nat.prod_primeFactors_dvd (3 ^ k - 1)
    rw [hsplitQ] at hdvd
    have h2 : 2 * ∏ q ∈ T, q ≤ 3 ^ k - 1 := Nat.le_of_dvd (by omega) hdvd
    have h3 : 15470 ≤ 2 * ∏ q ∈ T, q := by
      simpa using Nat.mul_le_mul_left 2 hqlb
    exact_mod_cast le_trans h3 h2
  have h64 : 64 < ((∏ q ∈ P, (if q = 2 then (1:ℝ)/9 else KM q)) - 1) ^ 2
      * (((3 ^ k - 1 : ℕ) : ℝ)) := by
    have hX : (1481/7735 : ℝ) ≤ (∏ q ∈ P, (if q = 2 then (1:ℝ)/9 else KM q)) - 1 := by
      linarith [hGval]
    have hX2 : (1481/7735 : ℝ)^2 ≤ ((∏ q ∈ P, (if q = 2 then (1:ℝ)/9 else KM q)) - 1)^2 :=
      pow_le_pow_left₀ (by positivity) hX 2
    have hstep : (1481/7735 : ℝ)^2 * 15470
        ≤ ((∏ q ∈ P, (if q = 2 then (1:ℝ)/9 else KM q)) - 1)^2 * (((3 ^ k - 1 : ℕ) : ℝ)) :=
      mul_le_mul hX2 hnv (by norm_num) (sq_nonneg _)
    have hnum : (64:ℝ) < (1481/7735 : ℝ)^2 * 15470 := by norm_num
    linarith [hstep, hnum]
  exact disj2_of_kmin_bound k hk hG (by simpa [hPdef, hTdef] using h64)


end Commons.NumberTheory.ThreePow
