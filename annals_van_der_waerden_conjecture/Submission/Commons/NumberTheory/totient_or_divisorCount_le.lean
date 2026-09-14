import Mathlib
import Submission.Commons.NumberTheory.Totient.totient_eq_prod_primeFactors
import Submission.Commons.NumberTheory.Totient.totient_ratio_eq_prod_one_sub_inv
import Submission.Commons.NumberTheory.Totient.totient_ratio_ge_ithPrime_mul
import Submission.Commons.NumberTheory.Nat.prod_one_sub_inv_ge_ithPrime
import Submission.Commons.NumberTheory.Totient.totient_sq_ge_divisors_sq_mul_kmin
import Submission.Commons.NumberTheory.Nat.prod_nth_prime_le_prod_of_le
import Submission.Commons.NumberTheory.Nat.exists_prime_dvd_two_pow_sub_one_notMem_small
import Submission.Commons.NumberTheory.TwoPow.primeFactors_card_three
import Submission.Commons.NumberTheory.ThreePow.primeFactors_card_four
import Submission.Commons.NumberTheory.TwoPow.primeFactors_card_four
import Submission.Commons.NumberTheory.ThreePow.primeFactors_card_five

namespace Commons.NumberTheory

open Finset
open scoped BigOperators

/-- Auxiliary weight: `kmin 2 = 1/9`, `kmin q = (q-1)²/(4q)` otherwise. -/
noncomputable def kmin (q : ℕ) : ℝ :=
  if q ≤ 2 then (if q = 2 then (1 : ℝ) / 9 else 0) else (((q : ℝ) - 1) ^ 2 / (4 * (q : ℝ)))

lemma kmin_two : kmin 2 = 1 / 9 := by simp [kmin]

lemma kmin_of_three_le {q : ℕ} (hq : 3 ≤ q) : kmin q = ((q : ℝ) - 1) ^ 2 / (4 * (q : ℝ)) := by
  unfold kmin; rw [if_neg (by omega : ¬ q ≤ 2)]

lemma kmin_nonneg (q : ℕ) : 0 ≤ kmin q := by
  rcases lt_or_ge q 3 with h | h
  · interval_cases q <;> simp [kmin]
  · rw [kmin_of_three_le h]
    have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    positivity

lemma kmin_mono : Monotone kmin := by
  intro a b hab
  rcases lt_or_ge b 3 with hb | hb
  · interval_cases b <;> interval_cases a <;> simp [kmin]
  · rcases lt_or_ge a 3 with ha | ha
    · interval_cases a
      · rw [kmin_of_three_le hb]; positivity
      · rw [kmin_of_three_le hb]; positivity
      · rw [kmin_two, kmin_of_three_le hb]
        have hb3 : (3 : ℝ) ≤ b := by exact_mod_cast hb
        rw [le_div_iff₀ (by linarith : (0:ℝ) < 4 * (b:ℝ))]
        nlinarith
    · rw [kmin_of_three_le ha, kmin_of_three_le hb]
      have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
      have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
      have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
      rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 4 * (a:ℝ)) (by linarith : (0:ℝ) < 4 * (b:ℝ))]
      have hab1 : (1:ℝ) ≤ (a:ℝ) * (b:ℝ) :=
        one_le_mul_of_one_le_of_one_le (by exact_mod_cast (by omega : 1 ≤ a))
          (by exact_mod_cast (by omega : 1 ≤ b))
      nlinarith [mul_nonneg (sub_nonneg.mpr hab') (by linarith : (0:ℝ) ≤ (a:ℝ) * (b:ℝ) - 1)]

/-- `kmin` is `≥ 1` from the 4th prime on. -/
lemma one_le_kmin_of_four_le {q : ℕ} (hq : 7 ≤ q) : 1 ≤ kmin q := by
  rw [kmin_of_three_le (by omega : 3 ≤ q)]
  rw [le_div_iff₀ (by (show (0:ℝ) < 4 * (q:ℝ)); positivity)]
  nlinarith [show (7:ℝ) ≤ q by exact_mod_cast hq]

/-! ## Values of the first primes -/

lemma nth_prime_val (i v : ℕ) (hv : Nat.Prime v) (hc : Nat.count Nat.Prime v = i) :
    Nat.nth Nat.Prime i = v := by
  rw [← hc]; exact Nat.nth_count hv

lemma P0 : Nat.nth Nat.Prime 0 = 2 := nth_prime_val 0 2 (by norm_num) (by decide)
lemma P1 : Nat.nth Nat.Prime 1 = 3 := nth_prime_val 1 3 (by norm_num) (by decide)
lemma P2 : Nat.nth Nat.Prime 2 = 5 := nth_prime_val 2 5 (by norm_num) (by decide)
lemma P3 : Nat.nth Nat.Prime 3 = 7 := nth_prime_val 3 7 (by norm_num) (by decide)
lemma P4 : Nat.nth Nat.Prime 4 = 11 := nth_prime_val 4 11 (by norm_num) (by decide)
lemma P5 : Nat.nth Nat.Prime 5 = 13 := nth_prime_val 5 13 (by norm_num) (by decide)
lemma P6 : Nat.nth Nat.Prime 6 = 17 := nth_prime_val 6 17 (by norm_num) (by decide)
lemma P7 : Nat.nth Nat.Prime 7 = 19 := nth_prime_val 7 19 (by norm_num) (by decide)
lemma P8 : Nat.nth Nat.Prime 8 = 23 := nth_prime_val 8 23 (by norm_num) (by decide)

/-! ## Numeric bounds -/

/-- `Q(8) = ∏_{i<8}(1-1/p_i) > 4/25`. -/
lemma Q8_gt : (4:ℝ)/25 < ∏ i ∈ Finset.range 8, (1 - 1/((Nat.nth Nat.Prime i : ℕ) : ℝ)) := by
  norm_num [Finset.prod_range_succ, P0, P1, P2, P3, P4, P5, P6, P7]

/-- `Q(3) = ∏_{i<3}(1-1/p_i) > 1/4`. -/
lemma Q3_gt : (1:ℝ)/4 < ∏ i ∈ Finset.range 3, (1 - 1/((Nat.nth Nat.Prime i : ℕ) : ℝ)) := by
  norm_num [Finset.prod_range_succ, P0, P1, P2]

/-- `Q(4) = ∏_{i<4}(1-1/p_i) > 2/9`. -/
lemma Q4b_gt : (2:ℝ)/9 < ∏ i ∈ Finset.range 4, (1 - 1/((Nat.nth Nat.Prime i : ℕ) : ℝ)) := by
  norm_num [Finset.prod_range_succ, P0, P1, P2, P3]

/-- `∏_{i<8} kmin p_i > 3.84`. -/
lemma K8_gt : (3.84:ℝ) < ∏ i ∈ Finset.range 8, kmin (Nat.nth Nat.Prime i) := by
  norm_num [Finset.prod_range_succ, kmin, P0, P1, P2, P3, P4, P5, P6, P7]

/-- `∏_{2 ≤ p_i, i<6} kmin p_i = kmin 2 · kmin 5 · kmin 7 · kmin 11 · kmin 13 · kmin 17 > 2.7`. -/
lemma K3_6_gt : (2.7:ℝ) <
    kmin 2 * (kmin 5 * (kmin 7 * (kmin 11 * (kmin 13 * kmin 17)))) := by
  norm_num [kmin]

/-- `∏_{i=1}^{5} kmin p_i = kmin 3 · kmin 5 · kmin 7 · kmin 11 · kmin 13 > 2.1`. -/
lemma K2_5_gt : (2.1:ℝ) < kmin 3 * (kmin 5 * (kmin 7 * (kmin 11 * kmin 13))) := by
  norm_num [kmin]

/-- `∏_{i : p_i ∈ {3,5,11,13}} kmin p_i > 1.67`. -/
lemma K_3511_13 : (1.67:ℝ) < kmin 3 * (kmin 5 * (kmin 11 * kmin 13)) := by
  norm_num [kmin]

/-- `∏_{i : p_i ∈ {3,7,11,13}} kmin p_i > 2.69`. -/
lemma K_3711_13 : (2.69:ℝ) < kmin 3 * (kmin 7 * (kmin 11 * kmin 13)) := by
  norm_num [kmin]

/-- `∏_{i : p_i ∈ {3,5,13}} kmin p_i` and variants used in the small cases. -/
lemma Q_3_5_q3 : (1:ℝ)/2 < (1 - 1/(3:ℝ)) * (1 - 1/(5:ℝ)) * (1 - 1/(17:ℝ)) := by norm_num

/-- `(2/3)(6/7)(10/11) > 1/2`. -/
lemma Q_3_7_11 : (1:ℝ)/2 < (1 - 1/(3:ℝ)) * (1 - 1/(7:ℝ)) * (1 - 1/(11:ℝ)) := by norm_num

/-- `(4/5)(6/7)(10/11) > 1/2`. -/
lemma Q_5_7_11 : (1:ℝ)/2 < (1 - 1/(5:ℝ)) * (1 - 1/(7:ℝ)) * (1 - 1/(11:ℝ)) := by norm_num

/-- `(2/3)(4/5)(6/7)(10/11) > 2/5`. -/
lemma Q_5_7_11_13 : (2:ℝ)/5 < (1 - 1/(5:ℝ)) * (1 - 1/(7:ℝ)) * (1 - 1/(11:ℝ)) * (1 - 1/(13:ℝ)) := by
  norm_num


/-- Explicit form of `kmin` (for `q ≥ 3` it is the quadratic formula, for `q ≤ 2` the constant). -/
lemma kmin_eq (q : ℕ) :
    kmin q = if q = 2 then (1 : ℝ) / 9 else (((q : ℝ) - 1) ^ 2 / (4 * (q : ℝ))) := by
  rcases lt_or_ge q 3 with h | h
  · interval_cases q <;> simp [kmin]
  · rw [kmin_of_three_le h, if_neg (by omega : q ≠ 2)]

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

/-- **Criterion for the second disjunct.**  If `G = ∏_{q | p^k-1} kmin q` satisfies `1 ≤ G` and
`64 < (G-1)²·(p^k-1)`, then `d(n)·(⌊√(p^k)⌋+1) < φ(n)` for `n = p^k - 1`. -/
lemma disj2_of_kmin_bound {p k : ℕ} (hp : Nat.Prime p) (hk : 2 ≤ k)
    (hG : 1 ≤ ∏ q ∈ (p ^ k - 1).primeFactors, kmin q)
    (h64 : 64 < ((∏ q ∈ (p ^ k - 1).primeFactors, kmin q) - 1) ^ 2 * (((p ^ k - 1 : ℕ) : ℝ))) :
    (Nat.divisors (p ^ k - 1)).card * (Nat.sqrt (p ^ k) + 1) < Nat.totient (p ^ k - 1) := by
  set n : ℕ := p ^ k - 1 with hn_def
  set G : ℝ := ∏ q ∈ n.primeFactors, kmin q with hG_def
  have hp2 : 2 ≤ p := hp.two_le
  have hpk : 4 ≤ p ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      _ ≤ p ^ k := Nat.pow_le_pow_left hp2 k
  have hn1 : 1 < n := by omega
  have hn0 : n ≠ 0 := by omega
  have hpk_eq : p ^ k = n + 1 := by omega
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
      exact Finset.prod_congr rfl (fun q _ => kmin_eq q)
    rw [hGeq]
    exact hchild
  have hσ : (((Nat.sqrt (p ^ k) + 1 : ℕ)) : ℝ) ≤ Real.sqrt (n : ℝ) + 2 := by
    have h1 : ((Nat.sqrt (p ^ k) : ℕ) : ℝ) ≤ Real.sqrt ((p ^ k : ℕ) : ℝ) := sqrt_nat_sqrt_le _
    have h2 : ((p ^ k : ℕ) : ℝ) = (n : ℝ) + 1 := by rw [hpk_eq]; push_cast; ring
    push_cast
    rw [h2] at h1
    have := sqrt_add_one_le (n : ℝ) (le_of_lt hnpos)
    linarith
  have hkey : (Real.sqrt (n : ℝ) + 2) ^ 2 < G * (n : ℝ) :=
    sq_sqrt_add_two_lt (by omega) hG h64
  have hσ2 : ((((Nat.sqrt (p ^ k) + 1 : ℕ)) : ℝ))^2 < G * (n : ℝ) := by
    have h := mul_self_le_mul_self (show (0:ℝ) ≤ (((Nat.sqrt (p ^ k) + 1 : ℕ)) : ℝ) by positivity) hσ
    rw [sq] at hkey ⊢
    linarith
  have hkey2 : (((Nat.divisors n).card : ℝ) * (((Nat.sqrt (p ^ k) + 1 : ℕ)) : ℝ))^2
      < ((Nat.totient n : ℝ))^2 := by
    rw [mul_pow]
    calc (((Nat.divisors n).card : ℝ))^2 * ((((Nat.sqrt (p ^ k) + 1 : ℕ)) : ℝ))^2
        < (((Nat.divisors n).card : ℝ))^2 * (G * (n : ℝ)) :=
          mul_lt_mul_of_pos_left hσ2 (pow_pos hdpos 2)
      _ = (((Nat.divisors n).card : ℝ))^2 * (n:ℝ) * G := by ring
      _ ≤ ((Nat.totient n : ℝ))^2 := hmain
  have hφnn : (0:ℝ) ≤ (Nat.totient n : ℝ) := Nat.cast_nonneg _
  have hdsnn : (0:ℝ) ≤ ((Nat.divisors n).card : ℝ) * (((Nat.sqrt (p ^ k) + 1 : ℕ)) : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hlt : ((Nat.divisors n).card : ℝ) * (((Nat.sqrt (p ^ k) + 1 : ℕ)) : ℝ) < (Nat.totient n : ℝ) := by
    nlinarith [hkey2, hφnn, hdsnn]
  exact_mod_cast hlt


/-! ## The main theorem -/

/-- Real form of the Euler product for the totient ratio. -/
lemma totient_ratio_real (n : ℕ) (hn : n ≠ 0) :
    (Nat.totient n : ℝ) / (n : ℝ) = ∏ q ∈ n.primeFactors, (1 - 1 / (q : ℝ)) := by
  have h : ((Nat.totient n : ℚ) / (n : ℚ) : ℝ) =
      ((∏ q ∈ n.primeFactors, (1 - 1 / (q : ℚ))) : ℝ) := by
    exact_mod_cast (Commons.NumberTheory.Totient.totient_ratio_eq_prod_one_sub_inv n hn)
  push_cast at h
  exact h

/-- Real form of the "add `p`" lower bound for the totient ratio. -/
lemma totient_ratio_ge_ithPrime_mul_real (n p : ℕ) (hp : Nat.Prime p) (hn : n ≠ 0)
    (hpn : ¬ p ∣ n) :
    (∏ i ∈ Finset.range ((n.primeFactors).card + 1),
        (1 - 1 / ((Nat.nth Nat.Prime i : ℕ) : ℝ))) * ((p : ℝ) / ((p : ℝ) - 1))
      ≤ (Nat.totient n : ℝ) / (n : ℝ) := by
  have h : (((∏ i ∈ Finset.range ((n.primeFactors).card + 1),
        (1 - 1 / ((Nat.nth Nat.Prime i : ℕ) : ℚ))) * ((p : ℚ) / ((p : ℚ) - 1)) : ℚ) : ℝ)
      ≤ ((Nat.totient n : ℚ) / (n : ℚ) : ℝ) := by
    exact_mod_cast (Commons.NumberTheory.Totient.totient_ratio_ge_ithPrime_mul n p hp hn hpn)
  push_cast at h
  exact h

/-- `0 ≤ 1 - 1/q` for `q ≥ 1`. -/
lemma one_sub_inv_nonneg {q : ℕ} (hq : 1 ≤ q) : (0:ℝ) ≤ 1 - 1 / (q : ℝ) := by
  have hq0 : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  rw [sub_nonneg, div_le_one hq0]
  exact_mod_cast hq

lemma one_sub_inv_le_one (q : ℕ) : (1:ℝ) - 1 / (q : ℝ) ≤ 1 := by
  have h := div_nonneg (show (0:ℝ) ≤ 1 by norm_num) (Nat.cast_nonneg q)
  linarith

lemma nth_prime_prime (m : ℕ) : Nat.Prime (Nat.nth Nat.Prime m) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime m

/-- The product `∏_{i<m}(1 - 1/p_i)` is monotone decreasing in `m`. -/
lemma Q_antitone : Antitone fun m : ℕ =>
    ∏ i ∈ Finset.range m, (1 - 1 / ((Nat.nth Nat.Prime i : ℕ) : ℝ)) := by
  apply antitone_nat_of_succ_le
  intro m
  rw [Finset.prod_range_succ]
  have h1 : (0:ℝ) ≤ ∏ i ∈ Finset.range m, (1 - 1 / ((Nat.nth Nat.Prime i : ℕ) : ℝ)) :=
    Finset.prod_nonneg fun i _ => one_sub_inv_nonneg (Nat.Prime.one_le (nth_prime_prime i))
  have h2 : (1:ℝ) - 1 / ((Nat.nth Nat.Prime m : ℕ) : ℝ) ≤ 1 := one_sub_inv_le_one _
  nlinarith

/-- `(p-1)/p²` is decreasing for `p ≥ 2`. -/
lemma ratio_anti {p q : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) :
    ((q : ℝ) - 1) / (q : ℝ)^2 ≤ ((p : ℝ) - 1) / (p : ℝ)^2 := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hq0 : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hpq' : (p:ℝ) ≤ q := by exact_mod_cast hpq
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hp2' : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have h3 : (0:ℝ) ≤ ((p:ℝ) - 1) * ((q:ℝ) - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have h4 : (1:ℝ) ≤ ((p:ℝ) - 1) * ((q:ℝ) - 1) :=
    one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  nlinarith [mul_nonneg (sub_nonneg.mpr hpq') (by linarith [h4] : (0:ℝ) ≤ (p:ℝ) * (q:ℝ) - (p:ℝ) - (q:ℝ)), h3]


/-! ## Sorted-product bounds for `kmin` and for primes -/

/-- `∏_{i<c}kmin p_i ≤ ∏_{q∈S}kmin q` for any finset `S` of primes with `c ≤ |S|` (primes `≥ m`). -/
lemma kmin_prod_le_prod (S : Finset ℕ) (hS : ∀ x ∈ S, Nat.Prime x) (m : ℕ)
    (hm : ∀ x ∈ S, m ≤ x) :
    (∏ i ∈ Finset.range S.card, kmin (Nat.nth Nat.Prime (Nat.count Nat.Prime m + i)))
      ≤ ∏ q ∈ S, kmin q :=
  Commons.NumberTheory.Nat.prod_nth_prime_le_prod_of_le S m hS hm kmin kmin_mono kmin_nonneg

/-- `∏_{i<8}kmin p_i ≤ ∏_{q∈S}kmin q` when `|S| ≥ 8`. -/
lemma kmin_prod_eight_le (S : Finset ℕ) (hS : ∀ x ∈ S, Nat.Prime x) (h8 : 8 ≤ S.card) :
    (∏ i ∈ Finset.range 8, kmin (Nat.nth Nat.Prime i)) ≤ ∏ q ∈ S, kmin q := by
  have hc0 : Nat.count Nat.Prime 0 = 0 := by simp [Nat.count_eq_card_filter_range]
  refine le_trans ?_ (kmin_prod_le_prod S hS 0 (fun _ _ => Nat.zero_le _))
  simp only [hc0, zero_add]
  apply Finset.prod_le_prod_of_subset_of_one_le (Finset.range_subset_range.mpr h8)
  · intro i _
    exact kmin_nonneg (Nat.nth Nat.Prime i)
  · intro i hi hni
    rw [Finset.mem_range] at hi hni
    have h7 : 7 ≤ Nat.nth Nat.Prime i := by
      have h1 : Nat.nth Nat.Prime 4 ≤ Nat.nth Nat.Prime i :=
        (Nat.nth_le_nth Nat.infinite_setOfPred_prime).mpr (by omega)
      rw [P4] at h1
      omega
    exact one_le_kmin_of_four_le h7

/-- Monotonicity of the products in the tail: for `ω ≥ 5`, the product of the first five
`kmin`-values over the primes `≥ m` is at most the product of the first `ω` of them. -/
lemma kmin_prod_shift_le {ω : ℕ} (hω : 5 ≤ ω) {m : ℕ} (hm3 : 3 ≤ m) (hm5 : m ≤ 5) :
    (∏ i ∈ Finset.range 5, kmin (Nat.nth Nat.Prime (Nat.count Nat.Prime m + i)))
      ≤ ∏ i ∈ Finset.range ω, kmin (Nat.nth Nat.Prime (Nat.count Nat.Prime m + i)) := by
  apply Finset.prod_le_prod_of_subset_of_one_le (Finset.range_subset_range.mpr hω)
  · intro i _
    exact kmin_nonneg _
  · intro i hi hni
    rw [Finset.mem_range] at hi
    have hi5 : 5 ≤ i := by
      simp only [Finset.mem_range, not_lt] at hni
      omega
    have hcnt : 1 ≤ Nat.count Nat.Prime m := by
      rw [Nat.count_eq_card_filter_range]
      refine Finset.card_pos.mpr ⟨2, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by norm_num⟩
    have hidx : 6 ≤ Nat.count Nat.Prime m + i := by omega
    have h1 : Nat.nth Nat.Prime 6 ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime m + i) :=
      (Nat.nth_le_nth Nat.infinite_setOfPred_prime).mpr hidx
    rw [P6] at h1
    exact one_le_kmin_of_four_le (le_trans (by norm_num : 7 ≤ 17) h1)

/-- `∏_{i<ω}(p_{π(m)+i}) ≤ n` when `S = n.primeFactors` consists of primes `≥ m`. -/
lemma prod_shift_le_self (S : Finset ℕ) (hS : ∀ x ∈ S, Nat.Prime x) (m : ℕ)
    (hm : ∀ x ∈ S, m ≤ x) (n : ℕ) (hdvd : (∏ q ∈ S, q) ≤ n) :
    (∏ i ∈ Finset.range S.card, ((Nat.nth Nat.Prime (Nat.count Nat.Prime m + i) : ℕ) : ℝ))
      ≤ (n : ℝ) := by
  have h1 := Commons.NumberTheory.Nat.prod_nth_prime_le_prod_of_le S m hS hm
    (fun q : ℕ => (q : ℝ)) (fun a b h => Nat.cast_le.mpr h) (fun q => Nat.cast_nonneg q)
  have h2 : (∏ q ∈ S, (q : ℝ)) = ((∏ q ∈ S, q : ℕ) : ℝ) := by push_cast; ring
  rw [h2] at h1
  exact le_trans h1 (by exact_mod_cast hdvd)


/-! ## Numeric range-product bounds -/

lemma K25_gt : (2.1:ℝ) < ∏ i ∈ Finset.range 5, kmin (Nat.nth Nat.Prime (1 + i)) := by
  norm_num [Finset.prod_range_succ, kmin, P1, P2, P3, P4, P5]

lemma K35_gt : (24.3:ℝ) < ∏ i ∈ Finset.range 5, kmin (Nat.nth Nat.Prime (2 + i)) := by
  norm_num [Finset.prod_range_succ, kmin, P2, P3, P4, P5, P6]

lemma primorial8_eq : (∏ i ∈ Finset.range 8, ((Nat.nth Nat.Prime i : ℕ) : ℝ)) = 9699690 := by
  norm_num [Finset.prod_range_succ, P0, P1, P2, P3, P4, P5, P6, P7]

lemma primorial5_shift1_eq :
    (∏ i ∈ Finset.range 5, ((Nat.nth Nat.Prime (1 + i) : ℕ) : ℝ)) = 15015 := by
  norm_num [Finset.prod_range_succ, P1, P2, P3, P4, P5]

lemma primorial5_shift2_eq :
    (∏ i ∈ Finset.range 5, ((Nat.nth Nat.Prime (2 + i) : ℕ) : ℝ)) = 85085 := by
  norm_num [Finset.prod_range_succ, P2, P3, P4, P5, P6]


/-! ## The main theorem -/

/-- For a prime `p`, `¬ p ∣ p^k - 1`. -/
lemma not_dvd_pow_sub_one (p k : ℕ) (hp : Nat.Prime p) (hk : 1 ≤ k) :
    ¬ p ∣ p ^ k - 1 := by
  intro hd
  have hpk : p ∣ p ^ k := dvd_pow_self p (by omega)
  have hsub : p ∣ p ^ k - (p ^ k - 1) := Nat.dvd_sub hpk hd
  have h1 : p ^ k - (p ^ k - 1) = 1 := by
    have : 1 ≤ p ^ k := Nat.one_le_pow k p hp.one_le
    omega
  rw [h1] at hsub
  exact hp.not_dvd_one hsub

lemma p_dvd_pow_sub_one_of_dvd {p d k : ℕ} (h : d ∣ k) :
    p ^ d - 1 ∣ p ^ k - 1 :=
  Nat.pow_sub_one_dvd_pow_sub_one p h

theorem totient_or_divisorCount_le {p k : ℕ} (hp : Nat.Prime p) (hk : 2 ≤ k) :
    p ^ (k - 1) - 1 < Nat.totient (p ^ k - 1) ∨
      (Nat.divisors (p ^ k - 1)).card * (Nat.sqrt (p ^ k) + 1) < Nat.totient (p ^ k - 1) := by
  by_contra hconj
  push_neg at hconj
  obtain ⟨h1, h2⟩ := hconj
  set n : ℕ := p ^ k - 1 with hn_def
  have hp2 : 2 ≤ p := hp.two_le
  have hpk2 : 2 ≤ p ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 1 ≤ k)
      _ ≤ p ^ k := Nat.pow_le_pow_left hp2 k
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn0 : n ≠ 0 := by omega
  -- (1) `p * φ(n) < n`
  have hpmul : p * Nat.totient n < n := by
    have hpk : p ^ k = p * p ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    have h2' : p * (p ^ (k - 1) - 1) ≤ p ^ k - p := by
      rw [hpk, Nat.mul_sub_left_distrib, mul_one]
    have h3 : p * Nat.totient n ≤ p ^ k - p :=
      le_trans (Nat.mul_le_mul_left p h1) h2'
    have h4 : p ≤ p ^ k := by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ k := Nat.pow_le_pow_right (by omega : 0 < p) (by omega : 1 ≤ k)
    have hp1 : 1 < p := hp.one_lt
    have hpk1 : 1 ≤ p ^ k := Nat.one_le_pow k p hp.one_le
    omega
  -- (2) `φ(n)/n < 1/p`
  have hP_lt : (Nat.totient n : ℝ) / (n:ℝ) < 1/(p:ℝ) := by
    rw [div_lt_div_iff₀ hnpos (by positivity : (0:ℝ) < (p:ℝ))]
    have h : ((Nat.totient n : ℝ)) * (p:ℝ) < (n:ℝ) := by
      have hnat : Nat.totient n * p < n := by linarith [hpmul]
      exact_mod_cast hnat
    linarith
  -- (3) the "add `p`" bound
  have hpndvd : ¬ p ∣ n := by
    have := not_dvd_pow_sub_one p k hp (by omega)
    simpa [hn_def] using this
  have hadd := totient_ratio_ge_ithPrime_mul_real n p hp hn0 hpndvd
  -- (4) `Q(ω+1) < (p-1)/p²`
  have hQlt : (∏ i ∈ Finset.range ((n.primeFactors).card + 1),
        (1 - 1 / ((Nat.nth Nat.Prime i : ℕ) : ℝ))) < ((p:ℝ)-1)/(p:ℝ)^2 := by
    have hp1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast hp.one_lt
    have hpos : (0:ℝ) < (p:ℝ) := by positivity
    have h1' : (∏ i ∈ Finset.range ((n.primeFactors).card + 1),
        (1 - 1 / ((Nat.nth Nat.Prime i : ℕ) : ℝ))) * ((p:ℝ)/((p:ℝ)-1)) < 1/(p:ℝ) :=
      lt_of_le_of_lt hadd hP_lt
    have h2' : (∏ i ∈ Finset.range ((n.primeFactors).card + 1),
        (1 - 1 / ((Nat.nth Nat.Prime i : ℕ) : ℝ))) <
        (1/(p:ℝ)) * (((p:ℝ)-1)/(p:ℝ)) := by
      have hden : (0:ℝ) < (p:ℝ)/((p:ℝ)-1) := by positivity
      have h := (lt_div_iff₀ hden).mpr h1'
      have heq : (1/(p:ℝ)) / ((p:ℝ)/((p:ℝ)-1)) = (1/(p:ℝ)) * (((p:ℝ)-1)/(p:ℝ)) := by
        field_simp
      linarith [h, heq]
    have h3' : (1/(p:ℝ)) * (((p:ℝ)-1)/(p:ℝ)) = ((p:ℝ)-1)/(p:ℝ)^2 := by
      field_simp
    linarith [h2', h3']
  have hS : ∀ q ∈ n.primeFactors, Nat.Prime q := fun q hq => Nat.prime_of_mem_primeFactors hq
  have hdvd : (∏ q ∈ n.primeFactors, q) ≤ n :=
    Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)
  rcases lt_or_ge (n.primeFactors).card 8 with hlt8 | hge8
  · -- Case `ω ≤ 7`
    have hQ8le : (∏ i ∈ Finset.range 8,
        (1 - 1 / ((Nat.nth Nat.Prime i : ℕ) : ℝ))) ≤
        (∏ i ∈ Finset.range ((n.primeFactors).card + 1),
        (1 - 1 / ((Nat.nth Nat.Prime i : ℕ) : ℝ))) :=
      Q_antitone (by omega)
    have h425 : (4:ℝ)/25 < ((p:ℝ)-1)/(p:ℝ)^2 :=
      lt_trans (lt_of_lt_of_le Q8_gt hQ8le) hQlt
    have hp_le3 : p ≤ 3 := by
      by_contra h
      push_neg at h
      have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
      have h5 : 5 ≤ p := by omega
      have hra := ratio_anti (p := 5) (q := p) (by norm_num) h5
      norm_num at hra
      linarith [hra, h425]
    interval_cases p
    · -- p = 2
      have hQ_lt : (∏ i ∈ Finset.range ((n.primeFactors).card + 1),
          (1 - 1 / ((Nat.nth Nat.Prime i : ℕ) : ℝ))) < (1:ℝ)/4 := by
        have h := hQlt
        norm_num at h
        simpa [one_div] using h
      have hω3 : 3 ≤ (n.primeFactors).card := by
        by_contra h
        push_neg at h
        have hle : (n.primeFactors).card + 1 ≤ 3 := by omega
        have hmono := Q_antitone hle
        have hlt : (1:ℝ)/4 < (∏ i ∈ Finset.range ((n.primeFactors).card + 1),
            (1 - 1 / ((Nat.nth Nat.Prime i : ℕ) : ℝ))) := lt_of_lt_of_le Q3_gt hmono
        linarith [hlt, hQ_lt]
      rcases lt_or_ge (n.primeFactors).card 5 with h5 | h5
      · -- `ω ∈ {3,4}`
        have hω34 : (n.primeFactors).card = 3 ∨ (n.primeFactors).card = 4 := by omega
        rcases hω34 with h3 | h4
        · refine absurd ?_ (not_lt.mpr h1)
          have := Commons.NumberTheory.TwoPow.primeFactors_card_three k hk (by simpa [hn_def] using h3)
          simpa [hn_def] using this
        · refine absurd ?_ (not_lt.mpr h2)
          have := Commons.NumberTheory.TwoPow.primeFactors_card_four k hk
            (by simpa [hn_def] using h4) (by simpa [hn_def] using h1)
          simpa [hn_def] using this
      · -- `ω ≥ 5`
        have hodd : ∀ q ∈ n.primeFactors, 3 ≤ q := by
          intro q hq
          have hq2 : q ≠ 2 := by
            rintro rfl
            exact hpndvd ((Nat.mem_primeFactors.mp hq).2.1)
          have := Nat.Prime.two_le (hS q hq)
          omega
        have hcnt3 : Nat.count Nat.Prime 3 = 1 := by decide
        have hA := kmin_prod_le_prod n.primeFactors hS 3 hodd
        simp only [hcnt3] at hA
        have hB := kmin_prod_shift_le (m := 3) h5 (by norm_num) (by norm_num)
        simp only [hcnt3] at hB
        have hG : (2.1:ℝ) < ∏ q ∈ n.primeFactors, kmin q := by
          linarith [K25_gt, hA, hB]
        have hn15 : (15015:ℝ) ≤ (n:ℝ) := by
          have h2' := prod_shift_le_self n.primeFactors hS 3 hodd n hdvd
          simp only [hcnt3] at h2'
          have h3' : (∏ i ∈ Finset.range 5, ((Nat.nth Nat.Prime (1 + i) : ℕ) : ℝ)) ≤
              (∏ i ∈ Finset.range (n.primeFactors).card,
                ((Nat.nth Nat.Prime (1 + i) : ℕ) : ℝ)) := by
            apply Finset.prod_le_prod_of_subset_of_one_le (Finset.range_subset_range.mpr h5)
            · intro i _; exact Nat.cast_nonneg _
            · intro i _ _; exact_mod_cast (Nat.Prime.one_le (nth_prime_prime (1 + i)))
          rw [← primorial5_shift1_eq]
          exact le_trans h3' h2'
        have h64 : 64 < ((∏ q ∈ n.primeFactors, kmin q) - 1) ^ 2 * (((2 ^ k - 1 : ℕ) : ℝ)) := by
          have h11 : (1.1:ℝ) ≤ (∏ q ∈ n.primeFactors, kmin q) - 1 := by linarith
          have hsq : (1.1:ℝ)^2 ≤ ((∏ q ∈ n.primeFactors, kmin q) - 1)^2 := by nlinarith
          have hnk : ((2 ^ k - 1 : ℕ) : ℝ) = (n:ℝ) := by simp [hn_def]
          rw [hnk]
          nlinarith [hsq, hn15]
        have hd2 : (Nat.divisors (2 ^ k - 1)).card * (Nat.sqrt (2 ^ k) + 1) < Nat.totient (2 ^ k - 1) := by
          simpa [hn_def] using disj2_of_kmin_bound hp hk
            (by simpa [hn_def] using le_trans (by norm_num : (1:ℝ) ≤ 2.1) (le_of_lt hG))
            (by simpa [hn_def] using h64)
        exact absurd hd2 (by simpa [hn_def] using not_lt.mpr h2)
    · -- p = 3
      have hQ_lt : (∏ i ∈ Finset.range ((n.primeFactors).card + 1),
          (1 - 1 / ((Nat.nth Nat.Prime i : ℕ) : ℝ))) < (2:ℝ)/9 := by
        have h := hQlt
        norm_num at h
        simpa [one_div] using h
      have hω4 : 4 ≤ (n.primeFactors).card := by
        by_contra h
        push_neg at h
        have hle : (n.primeFactors).card + 1 ≤ 4 := by omega
        have hmono := Q_antitone hle
        have hlt : (2:ℝ)/9 < (∏ i ∈ Finset.range ((n.primeFactors).card + 1),
            (1 - 1 / ((Nat.nth Nat.Prime i : ℕ) : ℝ))) := lt_of_lt_of_le Q4b_gt hmono
        linarith [hlt, hQ_lt]
      rcases lt_or_ge (n.primeFactors).card 6 with h6 | h6
      · -- `ω ∈ {4,5}`
        have hω45 : (n.primeFactors).card = 4 ∨ (n.primeFactors).card = 5 := by omega
        rcases hω45 with h4 | h5
        · refine absurd ?_ (not_lt.mpr h1)
          have := Commons.NumberTheory.ThreePow.primeFactors_card_four k hk (by simpa [hn_def] using h4)
          simpa [hn_def] using this
        · refine absurd ?_ (not_lt.mpr h2)
          have := Commons.NumberTheory.ThreePow.primeFactors_card_five k hk
            (by simpa [hn_def] using h5) (by simpa [hn_def] using h1)
          simpa [hn_def] using this
      · -- `ω ≥ 6`
        have h2mem : 2 ∈ n.primeFactors := by
          have h2dvd : 2 ∣ n := by
            have h := p_dvd_pow_sub_one_of_dvd (p := 3) (d := 1) (k := k) (one_dvd k)
            norm_num at h
            simpa [hn_def] using h
          exact Nat.mem_primeFactors.mpr ⟨by norm_num, h2dvd, hn0⟩
        have hge5 : ∀ q ∈ n.primeFactors.erase 2, 5 ≤ q := by
          intro q hq
          have hqS : q ∈ n.primeFactors := Finset.mem_of_mem_erase hq
          have hqne : q ≠ 2 := (Finset.mem_erase.mp hq).1
          have hqprime := hS q hqS
          have hqdvd : q ∣ n := (Nat.mem_primeFactors.mp hqS).2.1
          have hq3 : q ≠ 3 := by
            rintro rfl
            have hd3 : 3 ∣ 3 ^ k - 1 := by simpa [hn_def] using hqdvd
            have hsub : 3 ∣ 3 ^ k - (3 ^ k - 1) := Nat.dvd_sub (dvd_pow_self 3 (by omega)) hd3
            have h1 : 3 ^ k - (3 ^ k - 1) = 1 := by
              have : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by norm_num)
              omega
            rw [h1] at hsub
            norm_num at hsub
          have hq4 : q ≠ 4 := by rintro rfl; norm_num at hqprime
          have := hqprime.two_le
          omega
        have hcnt5 : Nat.count Nat.Prime 5 = 2 := by decide
        have hcard5 : 5 ≤ (n.primeFactors.erase 2).card := by
          rw [Finset.card_erase_of_mem h2mem]
          omega
        have hA := kmin_prod_le_prod (n.primeFactors.erase 2)
          (fun q hq => hS q (Finset.mem_of_mem_erase hq)) 5 hge5
        simp only [hcnt5] at hA
        have hB := kmin_prod_shift_le (m := 5) hcard5 (by norm_num) (by norm_num)
        have hprodfact : ∏ q ∈ n.primeFactors, kmin q =
            kmin 2 * ∏ q ∈ n.primeFactors.erase 2, kmin q := by
          rw [← Finset.prod_erase_mul n.primeFactors kmin h2mem, mul_comm]
        have herase : (24.3:ℝ) < ∏ q ∈ n.primeFactors.erase 2, kmin q :=
          lt_of_lt_of_le K35_gt (le_trans hB hA)
        have hG : (2.7:ℝ) < ∏ q ∈ n.primeFactors, kmin q := by
          rw [hprodfact, kmin_two]
          linarith [herase]
        have hsplit : (∏ q ∈ n.primeFactors, ((q:ℕ):ℝ)) =
            2 * ∏ q ∈ n.primeFactors.erase 2, ((q:ℕ):ℝ) := by
          have h := Finset.prod_erase_mul n.primeFactors (fun q : ℕ => ((q:ℕ):ℝ)) h2mem
          rw [← h]; ring
        have hA2 : (∏ i ∈ Finset.range (n.primeFactors.erase 2).card,
              ((Nat.nth Nat.Prime (2 + i) : ℕ) : ℝ)) ≤
              ∏ q ∈ n.primeFactors.erase 2, ((q:ℕ):ℝ) := by
          have := Commons.NumberTheory.Nat.prod_nth_prime_le_prod_of_le (n.primeFactors.erase 2) 5
            (fun q hq => hS q (Finset.mem_of_mem_erase hq)) hge5 (fun q : ℕ => ((q:ℕ):ℝ))
            (fun a b h => Nat.cast_le.mpr h) (fun q => Nat.cast_nonneg q)
          simpa [hcnt5] using this
        have h3' : (∏ i ∈ Finset.range 5, ((Nat.nth Nat.Prime (2 + i) : ℕ) : ℝ)) ≤
            (∏ i ∈ Finset.range (n.primeFactors.erase 2).card,
              ((Nat.nth Nat.Prime (2 + i) : ℕ) : ℝ)) := by
          apply Finset.prod_le_prod_of_subset_of_one_le
            (Finset.range_subset_range.mpr hcard5)
          · intro i _; exact Nat.cast_nonneg _
          · intro i _ _; exact_mod_cast (Nat.Prime.one_le (nth_prime_prime (2 + i)))
        have herase2 : (85085:ℝ) ≤ ∏ q ∈ n.primeFactors.erase 2, ((q:ℕ):ℝ) := by
          rw [← primorial5_shift2_eq]
          exact le_trans h3' hA2
        have hn170 : (170170:ℝ) ≤ (n:ℝ) := by
          have hpq : (∏ q ∈ n.primeFactors, ((q:ℕ):ℝ)) ≤ (n:ℝ) := by
            rw [← Nat.cast_prod]
            exact_mod_cast hdvd
          rw [hsplit] at hpq
          linarith [hpq, herase2]
        have h64 : 64 < ((∏ q ∈ n.primeFactors, kmin q) - 1) ^ 2 * (((3 ^ k - 1 : ℕ) : ℝ)) := by
          have h17 : (1.7:ℝ) ≤ (∏ q ∈ n.primeFactors, kmin q) - 1 := by linarith
          have hsq : (1.7:ℝ)^2 ≤ ((∏ q ∈ n.primeFactors, kmin q) - 1)^2 := by nlinarith
          have hnk : ((3 ^ k - 1 : ℕ) : ℝ) = (n:ℝ) := by simp [hn_def]
          rw [hnk]
          nlinarith [hsq, hn170]
        have hd2 : (Nat.divisors (3 ^ k - 1)).card * (Nat.sqrt (3 ^ k) + 1) < Nat.totient (3 ^ k - 1) := by
          simpa [hn_def] using disj2_of_kmin_bound hp hk
            (by simpa [hn_def] using le_trans (by norm_num : (1:ℝ) ≤ 2.7) (le_of_lt hG))
            (by simpa [hn_def] using h64)
        exact absurd hd2 (by simpa [hn_def] using not_lt.mpr h2)
  · -- Case `ω ≥ 8`: disjunct 2 holds
    have hGle := kmin_prod_eight_le n.primeFactors hS hge8
    have hG : (3.84:ℝ) < ∏ q ∈ n.primeFactors, kmin q := lt_of_lt_of_le K8_gt hGle
    have h969 : (9699690:ℝ) ≤ (n:ℝ) := by
      have hcnt0 : Nat.count Nat.Prime 0 = 0 := by simp [Nat.count_eq_card_filter_range]
      have h2' := prod_shift_le_self n.primeFactors hS 0 (fun _ _ => Nat.zero_le _) n hdvd
      simp only [hcnt0, zero_add] at h2'
      have h3' : (∏ i ∈ Finset.range 8, ((Nat.nth Nat.Prime i : ℕ) : ℝ)) ≤
          (∏ i ∈ Finset.range (n.primeFactors).card, ((Nat.nth Nat.Prime i : ℕ) : ℝ)) := by
        apply Finset.prod_le_prod_of_subset_of_one_le (Finset.range_subset_range.mpr hge8)
        · intro i _; exact Nat.cast_nonneg _
        · intro i _ _; exact_mod_cast (Nat.Prime.one_le (nth_prime_prime i))
      rw [← primorial8_eq]
      exact le_trans h3' h2'
    have h64 : 64 < ((∏ q ∈ n.primeFactors, kmin q) - 1) ^ 2 * (((p ^ k - 1 : ℕ) : ℝ)) := by
      have h284 : (2.84:ℝ) ≤ (∏ q ∈ n.primeFactors, kmin q) - 1 := by linarith
      have hsq : (2.84:ℝ)^2 ≤ ((∏ q ∈ n.primeFactors, kmin q) - 1)^2 := by nlinarith
      have hpk1 : ((p ^ k - 1 : ℕ) : ℝ) = (n:ℝ) := by simp [hn_def]
      rw [hpk1]
      nlinarith [hsq, h969]
    have hd2 : (Nat.divisors (p ^ k - 1)).card * (Nat.sqrt (p ^ k) + 1) < Nat.totient (p ^ k - 1) := by
      simpa [hn_def] using disj2_of_kmin_bound hp hk
        (by simpa [hn_def] using le_trans (by norm_num : (1:ℝ) ≤ 3.84) (le_of_lt hG))
        (by simpa [hn_def] using h64)
    exact absurd hd2 (by simpa [hn_def] using not_lt.mpr h2)

end Commons.NumberTheory
