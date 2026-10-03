import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Submission.Commons.Analysis.Series.tsum_one_div_nat_sq_le_1647
import Submission.Commons.Analysis.Series.tail_inv_sq_le
import Submission.Commons.Analysis.Series.tail_inv_sq_summable
import Submission.Commons.Data.Nat.card_squarefree_divisors
import Submission.Commons.Analysis.ExpLog.harmonic_le_one_add_log

namespace Commons.NumberTheory.Moebius

open scoped BigOperators
open Finset

noncomputable section

private lemma moebius_sq_cast (n : ℕ) :
    ((ArithmeticFunction.moebius n : ℝ))^2 = if Squarefree n then 1 else 0 := by
  rw [← Int.cast_pow, ArithmeticFunction.moebius_sq]; split <;> simp

/-- `∑_{d | n} μ(d)² 3^{ω(d)} = 4^{ω(n)}`. -/
private lemma sum_moebius_sq_three_pow_eq (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℝ))^2 * (3:ℝ)^(d.primeFactors.card))
      = (4:ℝ)^(n.primeFactors.card) := by
  have h1 : (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℝ))^2 * (3:ℝ)^(d.primeFactors.card))
      = ∑ d ∈ n.divisors with Squarefree d, (3:ℝ)^(d.primeFactors.card) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    rw [moebius_sq_cast]
    by_cases h : Squarefree d <;> simp [h]
  rw [h1, Nat.sum_divisors_filter_squarefree hn]
  have hnf : (UniqueFactorizationMonoid.normalizedFactors n).toFinset = n.primeFactors := by
    rw [Nat.factors_eq]; rfl
  rw [hnf]
  have hterm : ∀ i ∈ n.primeFactors.powerset,
      (3:ℝ)^((i.val.prod).primeFactors.card) = (3:ℝ)^(i.card) := by
    intro i hi
    have hsub : i ⊆ n.primeFactors := Finset.mem_powerset.mp hi
    have hprime : ∀ p ∈ i, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors (hsub hp)
    have hprodeq : i.val.prod = ∏ p ∈ i, p := by
      rw [Finset.prod_eq_multiset_prod]; simp
    rw [hprodeq, Nat.primeFactors_prod hprime]
  rw [Finset.sum_congr rfl hterm]
  have h2 : (∑ i ∈ n.primeFactors.powerset, (3:ℝ)^(i.card))
      = ∑ i ∈ n.primeFactors.powerset, ∏ p ∈ i, (3:ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.prod_const]
  rw [h2, ← Finset.prod_one_add]
  rw [show (1:ℝ) + 3 = 4 by norm_num, Finset.prod_const]

private lemma two_pow_sq (k : ℕ) : (((2:ℝ)^k))^2 = (4:ℝ)^k := by
  rw [← pow_mul, show (4:ℝ) = 2^2 by norm_num, ← pow_mul, mul_comm]

/-- Pointwise: `μ(n)² τ(n)² ≤ ∑_{d | n} μ(d)² 3^{ω(d)}`. -/
private lemma tau_sq_mu_sq_le_sum (n : ℕ) :
    ((ArithmeticFunction.moebius n : ℝ))^2 * (n.divisors.card : ℝ)^2
      ≤ ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℝ))^2 * (3:ℝ)^(d.primeFactors.card) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [sum_moebius_sq_three_pow_eq n hn]
    by_cases hsf : Squarefree n
    · have hcard : n.divisors.filter Squarefree = n.divisors := by
        apply Finset.filter_true_of_mem
        intro d hd; exact hsf.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
      have h2 : n.divisors.card = 2^(n.primeFactors.card) := by
        have := Commons.Data.Nat.card_squarefree_divisors n hn
        rwa [hcard] at this
      rw [moebius_sq_cast n, if_pos hsf, one_mul, h2]
      push_cast
      exact le_of_eq (two_pow_sq _)
    · rw [moebius_sq_cast n, if_neg hsf]; simp

/-- The finite Tonelli/decomposition step: the divisor-weighted sum is bounded by
`∑_e b(e)·(inner factor)`. -/
private lemma Sigma_le_decomp (m N : ℕ) :
    (∑ n ∈ (Icc 1 N).filter (fun n => m < n),
        ((ArithmeticFunction.moebius n : ℝ))^2 * (n.divisors.card : ℝ)^2 / (n:ℝ)^2)
      ≤ ∑ e ∈ Icc 1 N,
          (((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card)) *
            (∑ n ∈ (Icc 1 N).filter (fun n => m < n ∧ e ∣ n), 1/(n:ℝ)^2) := by
  set s : Finset ℕ := (Icc 1 N).filter (fun n => m < n) with hs
  have hdiv : ∀ n ∈ s, n.divisors = (Icc 1 N).filter (fun e => e ∣ n) := by
    intro n hn
    have hnmem := Finset.mem_filter.mp (by rwa [hs] at hn)
    have hnI := Finset.mem_Icc.mp hnmem.1
    obtain ⟨hn1, hnN⟩ := hnI
    ext e
    rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdvd, hne⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
        le_trans (Nat.le_of_dvd (by omega) hdvd) hnN⟩, hdvd⟩
    · rintro ⟨⟨he1, heN⟩, hdvd⟩
      exact ⟨hdvd, by omega⟩
  calc (∑ n ∈ s, ((ArithmeticFunction.moebius n : ℝ))^2 * (n.divisors.card : ℝ)^2 / (n:ℝ)^2)
      ≤ ∑ n ∈ s, (∑ d ∈ n.divisors,
            ((ArithmeticFunction.moebius d : ℝ))^2 * (3:ℝ)^(d.primeFactors.card)) / (n:ℝ)^2 := by
        apply Finset.sum_le_sum
        intro n hn
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact tau_sq_mu_sq_le_sum n
    _ = ∑ n ∈ s, ∑ d ∈ n.divisors,
            ((ArithmeticFunction.moebius d : ℝ))^2 * (3:ℝ)^(d.primeFactors.card) / (n:ℝ)^2 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.sum_div]
    _ = ∑ n ∈ s, ∑ e ∈ (Icc 1 N).filter (fun e => e ∣ n),
            ((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card) / (n:ℝ)^2 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [hdiv n hn]
    _ = ∑ n ∈ s, ∑ e ∈ Icc 1 N,
            (if e ∣ n then ((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card)
              / (n:ℝ)^2 else 0) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.sum_filter]
    _ = ∑ e ∈ Icc 1 N, ∑ n ∈ s,
            (if e ∣ n then ((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card)
              / (n:ℝ)^2 else 0) := Finset.sum_comm
    _ = ∑ e ∈ Icc 1 N,
            (((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card)) *
            ∑ n ∈ s.filter (fun n => e ∣ n), 1/(n:ℝ)^2 := by
        apply Finset.sum_congr rfl
        intro e he
        rw [← Finset.sum_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [div_eq_mul_inv]; ring
    _ = ∑ e ∈ Icc 1 N,
            (((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card)) *
            ∑ n ∈ (Icc 1 N).filter (fun n => m < n ∧ e ∣ n), 1/(n:ℝ)^2 := by
        apply Finset.sum_congr rfl
        intro e he
        congr 1
        rw [hs, Finset.filter_filter]

/-- `∑_{d | n} μ(d)² c^{ω(d)} = (1+c)^{ω(n)}`. -/
private lemma sum_moebius_sq_pow_omega_eq (c : ℝ) (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℝ))^2 * c^(d.primeFactors.card))
      = (1 + c)^(n.primeFactors.card) := by
  have h1 : (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℝ))^2 * c^(d.primeFactors.card))
      = ∑ d ∈ n.divisors with Squarefree d, c^(d.primeFactors.card) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    rw [moebius_sq_cast]
    by_cases h : Squarefree d <;> simp [h]
  rw [h1, Nat.sum_divisors_filter_squarefree hn]
  have hnf : (UniqueFactorizationMonoid.normalizedFactors n).toFinset = n.primeFactors := by
    rw [Nat.factors_eq]; rfl
  rw [hnf]
  have hterm : ∀ i ∈ n.primeFactors.powerset,
      c^((i.val.prod).primeFactors.card) = c^(i.card) := by
    intro i hi
    have hsub : i ⊆ n.primeFactors := Finset.mem_powerset.mp hi
    have hprime : ∀ p ∈ i, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors (hsub hp)
    have hprodeq : i.val.prod = ∏ p ∈ i, p := by
      rw [Finset.prod_eq_multiset_prod]; simp
    rw [hprodeq, Nat.primeFactors_prod hprime]
  rw [Finset.sum_congr rfl hterm]
  have h2 : (∑ i ∈ n.primeFactors.powerset, c^(i.card))
      = ∑ i ∈ n.primeFactors.powerset, ∏ p ∈ i, c := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.prod_const]
  rw [h2, ← Finset.prod_one_add, Finset.prod_const]

/-- The inner divisor sum for `e > m`: bounded by `ζ(2)/e²`. -/
private lemma inner_le_large (m N e : ℕ) (he : 1 ≤ e) :
    (∑ n ∈ (Icc 1 N).filter (fun n => m < n ∧ e ∣ n), 1/(n:ℝ)^2)
      ≤ (1/(e:ℝ)^2) * (1647/1000) := by
  set Φ : Finset ℕ := (Icc 1 N).filter (fun n => m < n ∧ e ∣ n) with hΦ
  have hinj : Set.InjOn (fun n => n/e) ↑Φ := by
    intro a ha b hb hab
    have haF : a ∈ Φ := ha
    have hbF : b ∈ Φ := hb
    rw [hΦ] at haF hbF
    have ha' : e ∣ a := (Finset.mem_filter.mp haF).2.2
    have hb' : e ∣ b := (Finset.mem_filter.mp hbF).2.2
    change a / e = b / e at hab
    rw [← Nat.mul_div_cancel' ha', ← Nat.mul_div_cancel' hb', hab]
  have hstep : (∑ n ∈ Φ, 1/(n:ℝ)^2)
      = (1/(e:ℝ)^2) * ∑ j ∈ Φ.image (fun n => n/e), 1/(j:ℝ)^2 := by
    rw [Finset.sum_image hinj, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnF : n ∈ Φ := hn
    rw [hΦ] at hnF
    have hn' : e ∣ n := (Finset.mem_filter.mp hnF).2.2
    have hne : (n:ℝ) = (e:ℝ) * ((n/e:ℕ):ℝ) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hn']
    rw [hne, mul_pow]; field_simp
  have hle : (∑ j ∈ Φ.image (fun n => n/e), 1/(j:ℝ)^2) ≤ 1647/1000 := by
    have hsum : Summable (fun j : ℕ => 1/(j:ℝ)^2) :=
      (Real.summable_one_div_nat_pow).mpr (by norm_num)
    exact (hsum.sum_le_tsum (Φ.image (fun n => n/e))
      (fun j _ => by positivity)).trans Commons.Analysis.Series.tsum_one_div_nat_sq_le_1647
  rw [hstep]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- The inner divisor sum for `e ≤ m`: bounded by `(1/e²)·2/(2⌊m/e⌋+1)` (tail of `∑1/j²`). -/
private lemma inner_le_small (m N e : ℕ) (he : 1 ≤ e) (hem : e ≤ m) :
    (∑ n ∈ (Icc 1 N).filter (fun n => m < n ∧ e ∣ n), 1/(n:ℝ)^2)
      ≤ (1/(e:ℝ)^2) * (2/(2*((m/e:ℕ):ℝ)+1)) := by
  set Φ : Finset ℕ := (Icc 1 N).filter (fun n => m < n ∧ e ∣ n) with hΦ
  set K : ℕ := m/e with hK
  have hinj : Set.InjOn (fun n => n/e) ↑Φ := by
    intro a ha b hb hab
    have haF : a ∈ Φ := ha
    have hbF : b ∈ Φ := hb
    rw [hΦ] at haF hbF
    have ha' : e ∣ a := (Finset.mem_filter.mp haF).2.2
    have hb' : e ∣ b := (Finset.mem_filter.mp hbF).2.2
    change a / e = b / e at hab
    rw [← Nat.mul_div_cancel' ha', ← Nat.mul_div_cancel' hb', hab]
  have hstep : (∑ n ∈ Φ, 1/(n:ℝ)^2)
      = (1/(e:ℝ)^2) * ∑ j ∈ Φ.image (fun n => n/e), 1/(j:ℝ)^2 := by
    rw [Finset.sum_image hinj, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnF : n ∈ Φ := hn
    rw [hΦ] at hnF
    have hn' : e ∣ n := (Finset.mem_filter.mp hnF).2.2
    have hne : (n:ℝ) = (e:ℝ) * ((n/e:ℕ):ℝ) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hn']
    rw [hne, mul_pow]; field_simp
  have hKj : ∀ j ∈ Φ.image (fun n => n/e), K < j := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨n, hn, rfl⟩ := hj
    have hnF : n ∈ Φ := hn
    rw [hΦ] at hnF
    have hnm := (Finset.mem_filter.mp hnF).2.1
    have hn' : e ∣ n := (Finset.mem_filter.mp hnF).2.2
    have hlt : m < e * (n/e) := by rwa [← Nat.mul_div_cancel' hn'] at hnm
    have : m / e < n / e := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by rwa [mul_comm])
    simpa [hK] using this
  have hle : (∑ j ∈ Φ.image (fun n => n/e), 1/(j:ℝ)^2) ≤ 2/(2*(K:ℝ)+1) := by
    have hsum : Summable (fun j : ℕ => if K < j then 1/(j:ℝ)^2 else 0) := by
      refine Summable.of_nonneg_of_le (f := fun j : ℕ => 1/(j:ℝ)^2)
        (fun j => by split_ifs <;> positivity) (fun j => ?_)
        ((Real.summable_one_div_nat_pow).mpr (by norm_num))
      split_ifs with h <;> simp
    have h1 : (∑ j ∈ Φ.image (fun n => n/e), (if K < j then 1/(j:ℝ)^2 else 0))
        ≤ ∑' j : ℕ, (if K < j then 1/(j:ℝ)^2 else 0) :=
      hsum.sum_le_tsum _ (fun j _ => by split_ifs <;> positivity)
    have h2 : (∑ j ∈ Φ.image (fun n => n/e), 1/(j:ℝ)^2)
        = ∑ j ∈ Φ.image (fun n => n/e), (if K < j then 1/(j:ℝ)^2 else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [if_pos (hKj j hj)]
    have h3 : (∑' j : ℕ, (if K < j then 1/(j:ℝ)^2 else 0)) ≤ 2/(2*(K:ℝ)+1) := by
      have hc : (∑' j : ℕ, (if K + 1 ≤ j then 1/(j:ℝ)^2 else 0)) ≤ 2/(2*(K:ℝ)+1) := by
        have := Commons.Analysis.Series.tail_inv_sq_le (K+1) (by simp)
        rw [show 2 * ((K+1:ℕ):ℝ) - 1 = 2*(K:ℝ)+1 by push_cast; ring] at this
        exact this
      refine le_of_eq_of_le ?_ hc
      apply tsum_congr
      intro j
      by_cases h : K < j
      · rw [if_pos h, if_pos (Nat.lt_iff_add_one_le.mp h)]
      · rw [if_neg h, if_neg (by omega)]
    rw [h2]
    exact h1.trans h3
  rw [hstep]
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- Swapping a sum over `n` and its divisors. -/
private lemma sum_divisors_swap (x : ℕ) (hx : 1 ≤ x) (G : ℕ → ℕ → ℝ) :
    (∑ n ∈ Icc 1 x, ∑ d ∈ n.divisors, G d n)
      = ∑ d ∈ Icc 1 x, ∑ n ∈ (Icc 1 x).filter (fun n => d ∣ n), G d n := by
  have hdiv : ∀ n ∈ Icc 1 x, n.divisors = (Icc 1 x).filter (fun d => d ∣ n) := by
    intro n hn
    obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.mp hn
    ext d
    rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdvd, hne⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
        le_trans (Nat.le_of_dvd (by omega) hdvd) hnx⟩, hdvd⟩
    · rintro ⟨⟨hd1, hdx⟩, hdvd⟩
      exact ⟨hdvd, by omega⟩
  calc (∑ n ∈ Icc 1 x, ∑ d ∈ n.divisors, G d n)
      = ∑ n ∈ Icc 1 x, ∑ d ∈ (Icc 1 x).filter (fun d => d ∣ n), G d n := by
        apply Finset.sum_congr rfl; intro n hn; rw [hdiv n hn]
    _ = ∑ n ∈ Icc 1 x, ∑ d ∈ Icc 1 x, (if d ∣ n then G d n else 0) := by
        apply Finset.sum_congr rfl; intro n hn; rw [Finset.sum_filter]
    _ = ∑ d ∈ Icc 1 x, ∑ n ∈ Icc 1 x, (if d ∣ n then G d n else 0) := Finset.sum_comm
    _ = ∑ d ∈ Icc 1 x, ∑ n ∈ (Icc 1 x).filter (fun n => d ∣ n), G d n := by
        apply Finset.sum_congr rfl; intro d hd; rw [Finset.sum_filter]

/-- `∑_{n ≤ x, d | n} 1/n ≤ (1 + log(x/d))/d`. -/
private lemma sum_filter_dvd_inv_le (x d : ℕ) (hd : 1 ≤ d) (hdx : d ≤ x) :
    (∑ n ∈ (Icc 1 x).filter (fun n => d ∣ n), 1/(n:ℝ))
      ≤ (1 + Real.log ((x:ℝ)/(d:ℝ))) / (d:ℝ) := by
  have hdxpos : 0 < x/d := Nat.div_pos hdx (by omega)
  set Ψ : Finset ℕ := (Icc 1 x).filter (fun n => d ∣ n) with hΨ
  have hinj : Set.InjOn (fun n => n/d) ↑Ψ := by
    intro a ha b hb hab
    have haF : a ∈ Ψ := ha; have hbF : b ∈ Ψ := hb
    rw [hΨ] at haF hbF
    have ha' : d ∣ a := (Finset.mem_filter.mp haF).2
    have hb' : d ∣ b := (Finset.mem_filter.mp hbF).2
    change a / d = b / d at hab
    rw [← Nat.mul_div_cancel' ha', ← Nat.mul_div_cancel' hb', hab]
  have hstep : (∑ n ∈ Ψ, 1/(n:ℝ)) = (1/(d:ℝ)) * ∑ j ∈ Ψ.image (fun n => n/d), 1/(j:ℝ) := by
    rw [Finset.sum_image hinj, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnF : n ∈ Ψ := hn; rw [hΨ] at hnF
    have hn' : d ∣ n := (Finset.mem_filter.mp hnF).2
    have hne : (n:ℝ) = (d:ℝ) * ((n/d:ℕ):ℝ) := by rw [← Nat.cast_mul, Nat.mul_div_cancel' hn']
    rw [hne]; field_simp
  have hsub : Ψ.image (fun n => n/d) ⊆ Icc 1 (x/d) := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨n, hn, rfl⟩ := hj
    have hnF : n ∈ Ψ := hn; rw [hΨ] at hnF
    have hnI := Finset.mem_Icc.mp (Finset.mem_filter.mp hnF).1
    have hdvd : d ∣ n := (Finset.mem_filter.mp hnF).2
    rw [Finset.mem_Icc]
    refine ⟨?_, Nat.div_le_div_right hnI.2⟩
    have hp := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (by omega)
    omega
  have hle : (∑ j ∈ Ψ.image (fun n => n/d), 1/(j:ℝ)) ≤ 1 + Real.log ((x/d:ℕ):ℝ) := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)).trans ?_
    exact Commons.Analysis.ExpLog.harmonic_le_one_add_log (x/d) (by omega)
  calc (∑ n ∈ Ψ, 1/(n:ℝ)) = (1/(d:ℝ)) * ∑ j ∈ Ψ.image (fun n => n/d), 1/(j:ℝ) := hstep
    _ ≤ (1/(d:ℝ)) * (1 + Real.log ((x/d:ℕ):ℝ)) := mul_le_mul_of_nonneg_left hle (by positivity)
    _ ≤ (1 + Real.log ((x:ℝ)/(d:ℝ))) / (d:ℝ) := by
        have hxd : (((x/d:ℕ)):ℝ) ≤ (x:ℝ)/(d:ℝ) := Nat.cast_div_le
        have hld : Real.log ((x/d:ℕ):ℝ) ≤ Real.log ((x:ℝ)/(d:ℝ)) :=
          Real.log_le_log (by exact_mod_cast hdxpos) hxd
        have : (1 + Real.log ((x/d:ℕ):ℝ)) ≤ 1 + Real.log ((x:ℝ)/(d:ℝ)) := by linarith
        calc (1/(d:ℝ)) * (1 + Real.log ((x/d:ℕ):ℝ))
            ≤ (1/(d:ℝ)) * (1 + Real.log ((x:ℝ)/(d:ℝ))) :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = (1 + Real.log ((x:ℝ)/(d:ℝ))) / (d:ℝ) := by ring

/-- `∑_{d ≤ x} 2^{ω(d)}/d ≤ (1 + log x)²`. -/
private lemma two_pow_omega_div_le (x : ℕ) (hx : 1 ≤ x) :
    (∑ d ∈ Icc 1 x, (2:ℝ)^(d.primeFactors.card) / (d:ℝ)) ≤ (1 + Real.log (x:ℝ))^2 := by
  have hinner : ∀ d ∈ Icc 1 x,
      (∑ n ∈ (Icc 1 x).filter (fun n => d ∣ n),
          ((ArithmeticFunction.moebius d : ℝ))^2 * (1:ℝ)^(d.primeFactors.card) / (n:ℝ))
        ≤ (1 + Real.log ((x:ℝ)/(d:ℝ))) / (d:ℝ) := by
    intro d hd
    obtain ⟨hd1, hdx⟩ := Finset.mem_Icc.mp hd
    have hm : ((ArithmeticFunction.moebius d : ℝ))^2 * (1:ℝ)^(d.primeFactors.card) ≤ 1 := by
      rw [one_pow, mul_one, moebius_sq_cast]; split <;> norm_num
    calc (∑ n ∈ (Icc 1 x).filter (fun n => d ∣ n),
            ((ArithmeticFunction.moebius d : ℝ))^2 * (1:ℝ)^(d.primeFactors.card) / (n:ℝ))
        = (((ArithmeticFunction.moebius d : ℝ))^2 * (1:ℝ)^(d.primeFactors.card))
            * ∑ n ∈ (Icc 1 x).filter (fun n => d ∣ n), 1/(n:ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro n hn; rw [div_eq_mul_inv, one_div]
      _ ≤ 1 * ((1 + Real.log ((x:ℝ)/(d:ℝ))) / (d:ℝ)) :=
          mul_le_mul hm (sum_filter_dvd_inv_le x d hd1 hdx) (by positivity) (by norm_num)
      _ = (1 + Real.log ((x:ℝ)/(d:ℝ))) / (d:ℝ) := by ring
  calc (∑ d ∈ Icc 1 x, (2:ℝ)^(d.primeFactors.card) / (d:ℝ))
      = ∑ n ∈ Icc 1 x, ∑ d ∈ n.divisors,
          ((ArithmeticFunction.moebius d : ℝ))^2 * (1:ℝ)^(d.primeFactors.card) / (n:ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
        rw [show (2:ℝ) = 1 + 1 by norm_num, ← sum_moebius_sq_pow_omega_eq 1 n hn0, Finset.sum_div]
    _ = ∑ d ∈ Icc 1 x, ∑ n ∈ (Icc 1 x).filter (fun n => d ∣ n),
          ((ArithmeticFunction.moebius d : ℝ))^2 * (1:ℝ)^(d.primeFactors.card) / (n:ℝ) :=
        sum_divisors_swap x hx _
    _ ≤ ∑ d ∈ Icc 1 x, (1 + Real.log ((x:ℝ)/(d:ℝ))) / (d:ℝ) := Finset.sum_le_sum hinner
    _ ≤ (1 + Real.log (x:ℝ))^2 := by
        have h1 : ∀ d ∈ Icc 1 x, (1 + Real.log ((x:ℝ)/(d:ℝ))) / (d:ℝ)
            ≤ (1 + Real.log (x:ℝ)) / (d:ℝ) := by
          intro d hd
          obtain ⟨hd1, hdx⟩ := Finset.mem_Icc.mp hd
          apply div_le_div_of_nonneg_right _ (by positivity)
          have hxpos : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
          have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
          have : ((x:ℝ)/(d:ℝ)) ≤ (x:ℝ) := by
            rw [div_le_iff₀ hdpos]
            have hd1' : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd1
            nlinarith [hd1', (Nat.cast_nonneg x : (0:ℝ) ≤ (x:ℝ))]
          have := Real.log_le_log (by positivity : (0:ℝ) < (x:ℝ)/(d:ℝ)) this
          linarith
        calc (∑ d ∈ Icc 1 x, (1 + Real.log ((x:ℝ)/(d:ℝ))) / (d:ℝ))
            ≤ ∑ d ∈ Icc 1 x, (1 + Real.log (x:ℝ)) / (d:ℝ) := Finset.sum_le_sum h1
          _ = (1 + Real.log (x:ℝ)) * ∑ d ∈ Icc 1 x, 1/(d:ℝ) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro d hd; rw [div_eq_mul_inv, one_div]
          _ ≤ (1 + Real.log (x:ℝ)) * (1 + Real.log (x:ℝ)) := by
              have hnn : (0:ℝ) ≤ 1 + Real.log (x:ℝ) := by
                nlinarith [Real.log_nonneg (by exact_mod_cast hx : (1:ℝ) ≤ (x:ℝ))]
              exact mul_le_mul_of_nonneg_left
                (Commons.Analysis.ExpLog.harmonic_le_one_add_log x hx) hnn
          _ = (1 + Real.log (x:ℝ))^2 := by ring

/-- `∑_{e ≤ x} μ(e)² 3^{ω(e)}/e ≤ (1 + log x)³`. -/
private lemma sum_sqfree_three_pow_omega_div_le (x : ℕ) (hx : 1 ≤ x) :
    (∑ e ∈ Icc 1 x, ((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card) / (e:ℝ))
      ≤ (1 + Real.log (x:ℝ))^3 := by
  have hinner : ∀ d ∈ Icc 1 x,
      (∑ e ∈ (Icc 1 x).filter (fun e => d ∣ e),
          ((ArithmeticFunction.moebius d : ℝ))^2 * (2:ℝ)^(d.primeFactors.card) / (e:ℝ))
        ≤ (2:ℝ)^(d.primeFactors.card) * ((1 + Real.log ((x:ℝ)/(d:ℝ))) / (d:ℝ)) := by
    intro d hd
    obtain ⟨hd1, hdx⟩ := Finset.mem_Icc.mp hd
    have hμ : ((ArithmeticFunction.moebius d : ℝ))^2 ≤ 1 := by
      rw [moebius_sq_cast]; split <;> norm_num
    have h2pos : (0:ℝ) < (2:ℝ)^(d.primeFactors.card) := by positivity
    have hm : ((ArithmeticFunction.moebius d : ℝ))^2 * (2:ℝ)^(d.primeFactors.card)
        ≤ (2:ℝ)^(d.primeFactors.card) := by nlinarith [hμ, h2pos]
    calc (∑ e ∈ (Icc 1 x).filter (fun e => d ∣ e),
            ((ArithmeticFunction.moebius d : ℝ))^2 * (2:ℝ)^(d.primeFactors.card) / (e:ℝ))
        = (((ArithmeticFunction.moebius d : ℝ))^2 * (2:ℝ)^(d.primeFactors.card))
            * ∑ e ∈ (Icc 1 x).filter (fun e => d ∣ e), 1/(e:ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro e he; rw [div_eq_mul_inv, one_div]
      _ ≤ (2:ℝ)^(d.primeFactors.card) * ((1 + Real.log ((x:ℝ)/(d:ℝ))) / (d:ℝ)) :=
          mul_le_mul hm (sum_filter_dvd_inv_le x d hd1 hdx) (by positivity) h2pos.le
  calc (∑ e ∈ Icc 1 x, ((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card) / (e:ℝ))
      ≤ ∑ e ∈ Icc 1 x, (3:ℝ)^(e.primeFactors.card) / (e:ℝ) := by
        apply Finset.sum_le_sum
        intro e he
        have hμ : ((ArithmeticFunction.moebius e : ℝ))^2 ≤ 1 := by
          rw [moebius_sq_cast]; split <;> norm_num
        have h3 : (0:ℝ) ≤ (3:ℝ)^(e.primeFactors.card) := by positivity
        exact div_le_div_of_nonneg_right (mul_le_of_le_one_left h3 hμ) (by positivity)
    _ = ∑ e ∈ Icc 1 x, ∑ d ∈ e.divisors,
          ((ArithmeticFunction.moebius d : ℝ))^2 * (2:ℝ)^(d.primeFactors.card) / (e:ℝ) := by
        apply Finset.sum_congr rfl
        intro e he
        have he0 : e ≠ 0 := by have := (Finset.mem_Icc.mp he).1; omega
        rw [show (3:ℝ) = 1 + 2 by norm_num, ← sum_moebius_sq_pow_omega_eq 2 e he0, Finset.sum_div]
    _ = ∑ d ∈ Icc 1 x, ∑ e ∈ (Icc 1 x).filter (fun e => d ∣ e),
          ((ArithmeticFunction.moebius d : ℝ))^2 * (2:ℝ)^(d.primeFactors.card) / (e:ℝ) :=
        sum_divisors_swap x hx _
    _ ≤ ∑ d ∈ Icc 1 x, (2:ℝ)^(d.primeFactors.card) * ((1 + Real.log ((x:ℝ)/(d:ℝ))) / (d:ℝ)) :=
        Finset.sum_le_sum hinner
    _ ≤ (1 + Real.log (x:ℝ)) * ∑ d ∈ Icc 1 x, (2:ℝ)^(d.primeFactors.card) / (d:ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro d hd
        obtain ⟨hd1, hdx⟩ := Finset.mem_Icc.mp hd
        have h2nn : (0:ℝ) ≤ (2:ℝ)^(d.primeFactors.card) := by positivity
        have hld : Real.log ((x:ℝ)/(d:ℝ)) ≤ Real.log (x:ℝ) := by
          apply Real.log_le_log (by positivity)
          rw [div_le_iff₀ (by positivity : (0:ℝ) < (d:ℝ))]
          have hd1' : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd1
          nlinarith [hd1', (Nat.cast_nonneg x : (0:ℝ) ≤ (x:ℝ))]
        have : (1 + Real.log ((x:ℝ)/(d:ℝ))) / (d:ℝ) ≤ (1 + Real.log (x:ℝ)) / (d:ℝ) := by
          apply div_le_div_of_nonneg_right _ (by positivity); linarith
        calc (2:ℝ)^(d.primeFactors.card) * ((1 + Real.log ((x:ℝ)/(d:ℝ))) / (d:ℝ))
            ≤ (2:ℝ)^(d.primeFactors.card) * ((1 + Real.log (x:ℝ)) / (d:ℝ)) :=
              mul_le_mul_of_nonneg_left this h2nn
          _ = (1 + Real.log (x:ℝ)) * ((2:ℝ)^(d.primeFactors.card) / (d:ℝ)) := by ring
    _ ≤ (1 + Real.log (x:ℝ)) * (1 + Real.log (x:ℝ))^2 := by
        apply mul_le_mul_of_nonneg_left (two_pow_omega_div_le x hx)
        nlinarith [Real.log_nonneg (by exact_mod_cast hx : (1:ℝ) ≤ (x:ℝ))]
    _ = (1 + Real.log (x:ℝ))^3 := by ring

/-- `3^{ω(e)}/e² = ∏_{p | e} 3/p²` for squarefree `e`. -/
private lemma three_pow_omega_div_sq_eq_prod (e : ℕ) (he : Squarefree e) :
    (3:ℝ)^(e.primeFactors.card) / (e:ℝ)^2 = ∏ p ∈ e.primeFactors, (3:ℝ)/(p:ℝ)^2 := by
  rw [Finset.prod_div_distrib, Finset.prod_const]
  congr 1
  rw [Finset.prod_pow, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree he]

/-- `∑_{e ≤ N} μ(e)² 3^{ω(e)}/e² ≤ 4`. -/
private lemma sum_sqfree_three_pow_omega_div_sq_le_four (N : ℕ) :
    (∑ e ∈ Icc 1 N,
        ((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card) / (e:ℝ)^2) ≤ 4 := by
  set PP : Finset ℕ := (Icc 1 N).filter Nat.Prime with hPP
  have hsf : (∑ e ∈ Icc 1 N,
        ((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card) / (e:ℝ)^2)
      = ∑ e ∈ (Icc 1 N).filter Squarefree, (3:ℝ)^(e.primeFactors.card) / (e:ℝ)^2 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e he
    rw [moebius_sq_cast]
    by_cases h : Squarefree e <;> simp [h]
  rw [hsf]
  have hinj : Set.InjOn (fun e : ℕ => e.primeFactors) ↑((Icc 1 N).filter Squarefree) := by
    intro a ha b hb hab
    change a.primeFactors = b.primeFactors at hab
    have haF : a ∈ (Icc 1 N).filter Squarefree := ha
    have hbF : b ∈ (Icc 1 N).filter Squarefree := hb
    rw [← Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.mp haF).2,
        ← Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.mp hbF).2, hab]
  have hstep : (∑ e ∈ (Icc 1 N).filter Squarefree, (3:ℝ)^(e.primeFactors.card) / (e:ℝ)^2)
      ≤ ∏ p ∈ PP, (1 + (3:ℝ)/(p:ℝ)^2) := by
    calc (∑ e ∈ (Icc 1 N).filter Squarefree, (3:ℝ)^(e.primeFactors.card) / (e:ℝ)^2)
        = ∑ e ∈ (Icc 1 N).filter Squarefree,
            ∏ p ∈ e.primeFactors, (3:ℝ)/(p:ℝ)^2 := by
          apply Finset.sum_congr rfl
          intro e he
          exact three_pow_omega_div_sq_eq_prod e (Finset.mem_filter.mp he).2
      _ = ∑ s ∈ ((Icc 1 N).filter Squarefree).image (fun e : ℕ => e.primeFactors),
            ∏ p ∈ s, (3:ℝ)/(p:ℝ)^2 := by
          rw [Finset.sum_image hinj]
      _ ≤ ∑ s ∈ PP.powerset, ∏ p ∈ s, (3:ℝ)/(p:ℝ)^2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro s hs
            rw [Finset.mem_image] at hs
            obtain ⟨e, he, rfl⟩ := hs
            have heF : e ∈ (Icc 1 N).filter Squarefree := he
            have heI := Finset.mem_Icc.mp (Finset.mem_filter.mp heF).1
            rw [hPP, Finset.mem_powerset]
            intro p hp
            rw [Finset.mem_filter, Finset.mem_Icc]
            have hpP : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
            have hpd : p ∣ e := Nat.dvd_of_mem_primeFactors hp
            exact ⟨⟨hpP.one_le, le_trans (Nat.le_of_dvd (by omega) hpd) heI.2⟩, hpP⟩
          · intro s hs _
            exact Finset.prod_nonneg (fun p hp => by positivity)
      _ = ∏ p ∈ PP, (1 + (3:ℝ)/(p:ℝ)^2) := by
          rw [Finset.prod_one_add]
  refine hstep.trans ?_
  have hsplit : (∏ p ∈ PP, (1 + (3:ℝ)/(p:ℝ)^2))
      = (∏ p ∈ PP.filter (fun p => p ≤ 19), (1 + (3:ℝ)/(p:ℝ)^2))
        * ∏ p ∈ PP.filter (fun p => ¬ p ≤ 19), (1 + (3:ℝ)/(p:ℝ)^2) := by
    rw [Finset.prod_filter_mul_prod_filter_not]
  rw [hsplit]
  have hsmall : (∏ p ∈ PP.filter (fun p => p ≤ 19), (1 + (3:ℝ)/(p:ℝ)^2)) ≤ 3 := by
    have hsub : PP.filter (fun p => p ≤ 19) ⊆ ({2,3,5,7,11,13,17,19} : Finset ℕ) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpPP, hple⟩ := hp
      rw [hPP, Finset.mem_filter, Finset.mem_Icc] at hpPP
      have hpP : Nat.Prime p := hpPP.2
      have hp2 : 2 ≤ p := hpP.two_le
      interval_cases p <;> simp_all <;> (exact absurd hpP (by decide))
    refine (Finset.prod_le_prod_of_subset_of_one_le₀ hsub
      (fun p hp => by positivity)
      (fun p hp hps => by
        have : (0:ℝ) ≤ 3/((p:ℝ)^2) := by positivity
        linarith)).trans ?_
    norm_num
  have hbig : (∏ p ∈ PP.filter (fun p => ¬ p ≤ 19), (1 + (3:ℝ)/(p:ℝ)^2)) ≤ 25/19 := by
    have hexp319 : Real.exp (3/19) ≤ 25/19 := by
      have h := Real.exp_bound (x := (3:ℝ)/19) (by norm_num) (n := 1) (by norm_num)
      simp only [Finset.sum_range_one, Nat.factorial_one, Nat.cast_one, pow_one] at h
      rw [abs_le] at h
      nlinarith [h.2]
    have htail : (∑ p ∈ PP.filter (fun p => ¬ p ≤ 19), (3:ℝ)/(p:ℝ)^2) ≤ 3/19 := by
      have hsub2 : PP.filter (fun p => ¬ p ≤ 19) ⊆ Icc 20 N := by
        intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hpPP, hp19⟩ := hp
        rw [hPP, Finset.mem_filter, Finset.mem_Icc] at hpPP
        rw [Finset.mem_Icc]
        exact ⟨by omega, hpPP.1.2⟩
      have hb : (∑ n ∈ Icc 20 N, 1/(n:ℝ)^2) ≤ 1/19 := by
        have hsum : Summable (fun n : ℕ => if 20 ≤ n then 1/(n:ℝ)^2 else 0) :=
          Commons.Analysis.Series.tail_inv_sq_summable 20
        have hterm : (∑ n ∈ Icc 20 N, 1/(n:ℝ)^2)
            = ∑ n ∈ Icc 20 N, (if 20 ≤ n then 1/(n:ℝ)^2 else 0) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [if_pos (Finset.mem_Icc.mp hn).1]
        rw [hterm]
        exact (hsum.sum_le_tsum (Finset.Icc 20 N) (fun n _ => by split_ifs <;> positivity)).trans
          ((Commons.Analysis.Series.tail_inv_sq_le 20 (by norm_num)).trans (by norm_num))
      have h3 : (∑ p ∈ PP.filter (fun p => ¬ p ≤ 19), (3:ℝ)/(p:ℝ)^2)
          = 3 * ∑ p ∈ PP.filter (fun p => ¬ p ≤ 19), 1/(p:ℝ)^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro p hp; ring
      rw [h3]
      calc (3:ℝ) * ∑ p ∈ PP.filter (fun p => ¬ p ≤ 19), 1/(p:ℝ)^2
          ≤ 3 * ∑ n ∈ Icc 20 N, 1/(n:ℝ)^2 := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply Finset.sum_le_sum_of_subset_of_nonneg hsub2
            intro n hn _
            positivity
        _ ≤ 3 * (1/19) := by
            apply mul_le_mul_of_nonneg_left hb (by norm_num)
        _ ≤ 3/19 := by norm_num
    calc (∏ p ∈ PP.filter (fun p => ¬ p ≤ 19), (1 + (3:ℝ)/(p:ℝ)^2))
        ≤ ∏ p ∈ PP.filter (fun p => ¬ p ≤ 19), Real.exp (3/(p:ℝ)^2) := by
          apply Finset.prod_le_prod₀ (fun p hp => by positivity)
          intro p hp
          have := Real.add_one_le_exp (3/(p:ℝ)^2)
          linarith
      _ = Real.exp (∑ p ∈ PP.filter (fun p => ¬ p ≤ 19), 3/(p:ℝ)^2) := by rw [Real.exp_sum]
      _ ≤ Real.exp (3/19) := Real.exp_le_exp.mpr htail
      _ ≤ 25/19 := hexp319
  calc (∏ p ∈ PP.filter (fun p => p ≤ 19), (1 + (3:ℝ)/(p:ℝ)^2))
        * (∏ p ∈ PP.filter (fun p => ¬ p ≤ 19), (1 + (3:ℝ)/(p:ℝ)^2))
      ≤ 3 * (25/19) := mul_le_mul hsmall hbig (by positivity) (by norm_num)
    _ ≤ 4 := by norm_num

open scoped Topology
open MeasureTheory Filter intervalIntegral Set in
/-- `t ↦ (1 + log t)/t` is antitone on `[1,∞)`. -/
private lemma antitoneOn_one_add_log_div : AntitoneOn (fun t : ℝ => (1 + Real.log t)/t) (Ici 1) := by
  intro a ha b hb hab
  have ha1 : (1:ℝ) ≤ a := ha
  have hb1 : (1:ℝ) ≤ b := hb
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  set c : ℝ := b/a with hc
  have hc1 : 1 ≤ c := by rw [hc]; rw [le_div_iff₀ ha0]; linarith
  have hcpos : 0 < c := by linarith
  have hb_eq : b = a*c := by rw [hc]; field_simp
  have hlogc : Real.log c ≤ c - 1 := Real.log_le_sub_one_of_pos hcpos
  have hla : (1:ℝ) ≤ 1 + Real.log a := by have := Real.log_nonneg ha1; linarith
  have hmain : Real.log c ≤ (c-1)*(1+Real.log a) := by
    have h1 : (c-1)*1 ≤ (c-1)*(1+Real.log a) := mul_le_mul_of_nonneg_left hla (by linarith)
    linarith
  rw [div_le_div_iff₀ hb0 ha0]
  have hlogb : Real.log b = Real.log a + Real.log c := by
    rw [hb_eq, Real.log_mul (by positivity) (by positivity)]
  rw [hlogb, hb_eq]
  have := mul_le_mul_of_nonneg_left hmain ha0.le
  nlinarith [this, ha0, hcpos]

open MeasureTheory Filter intervalIntegral Set in
/-- `t ↦ (1+log t)²/t²` is antitone on `[1,∞)`. -/
private lemma antitoneOn_one_add_log_sq_div_sq :
    AntitoneOn (fun t : ℝ => (1 + Real.log t)^2/t^2) (Ici 1) := by
  intro a ha b hb hab
  have h := antitoneOn_one_add_log_div ha hb hab
  have hb1 : (1:ℝ) ≤ b := hb
  have ha1 : (1:ℝ) ≤ a := ha
  have h1 : 0 ≤ (1 + Real.log b)/b :=
    div_nonneg (by have := Real.log_nonneg hb1; linarith) (by linarith)
  have h2 : 0 ≤ (1 + Real.log a)/a :=
    div_nonneg (by have := Real.log_nonneg ha1; linarith) (by linarith)
  calc (1 + Real.log b)^2/b^2 = ((1 + Real.log b)/b)^2 := by rw [div_pow]
    _ ≤ ((1 + Real.log a)/a)^2 := pow_le_pow_left₀ h1 h 2
    _ = (1 + Real.log a)^2/a^2 := by rw [div_pow]

open MeasureTheory Filter intervalIntegral Set in
/-- The derivative of `t ↦ -(2(log t)² + 8 log t + 10)/t`. -/
private lemma hasDerivAt_antideriv (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => (-2*(Real.log t)^2 - 8*Real.log t - 10)/t)
      (2*(1+Real.log x)^2/x^2) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
  have hll : HasDerivAt (fun t : ℝ => Real.log t * Real.log t)
      (x⁻¹ * Real.log x + Real.log x * x⁻¹) x := hlog.mul hlog
  have h1 : HasDerivAt (fun t : ℝ => (Real.log t)^2) (2*(Real.log x)*x⁻¹) x := by
    have hd : x⁻¹ * Real.log x + Real.log x * x⁻¹ = 2*(Real.log x)*x⁻¹ := by ring
    rw [hd] at hll
    convert hll using 1
    ext t; rw [pow_two]
  have h2 : HasDerivAt (fun t : ℝ => -2*(Real.log t)^2 - 8*Real.log t - 10)
      (-2*(2*(Real.log x)*x⁻¹) - 8*x⁻¹) x := by
    have h3 : HasDerivAt (fun t : ℝ => -2*(Real.log t)^2) (-2*(2*(Real.log x)*x⁻¹)) x :=
      h1.const_mul (-2)
    have h4 : HasDerivAt (fun t : ℝ => 8*Real.log t) (8*x⁻¹) x := hlog.const_mul 8
    exact (h3.sub h4).sub_const 10
  have h5 := h2.div (hasDerivAt_id x) hx0
  refine h5.congr_deriv ?_
  simp only [id_eq]
  field_simp
  ring

open MeasureTheory Filter intervalIntegral Set in
private lemma tendsto_antideriv :
    Tendsto (fun t : ℝ => (-2*(Real.log t)^2 - 8*Real.log t - 10)/t) atTop (𝓝 0) := by
  have hbase : Tendsto (fun t : ℝ => Real.log t / Real.sqrt t) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).tendsto_div_nhds_zero
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    rw [Real.sqrt_eq_rpow]
  have h2 : Tendsto (fun t : ℝ => (Real.log t)^2 / t) atTop (𝓝 0) := by
    have h := hbase.pow 2
    rw [show (0:ℝ)^2 = 0 by norm_num] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    rw [div_pow, Real.sq_sqrt (le_of_lt ht)]
  have h1 : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
    have hs : Tendsto (fun t : ℝ => 1/Real.sqrt t) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
    have h := hbase.mul hs
    rw [show (0:ℝ) * 0 = 0 by norm_num] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    rw [div_mul_div_comm, mul_one, ← sq, Real.sq_sqrt (le_of_lt ht)]
  have h0 : Tendsto (fun t : ℝ => (1:ℝ)/t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hcomb := ((h2.const_mul (-2)).add (h1.const_mul (-8))).add (h0.const_mul (-10))
  rw [show (-2)*0 + (-8)*0 + (-10)*0 = (0:ℝ) by norm_num] at hcomb
  refine hcomb.congr' ?_
  filter_upwards with t
  ring

open MeasureTheory Filter intervalIntegral Set in
private lemma integral_Ioi_log_sq (m : ℕ) (hm : 1 ≤ m) :
    ∫ x in Ioi (m:ℝ), (2*(1+Real.log x)^2/x^2) = 2*((Real.log (m:ℝ))^2 + 4*Real.log (m:ℝ) + 5)/(m:ℝ) := by
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hderiv : ∀ x ∈ Ici (m:ℝ),
      HasDerivAt (fun t : ℝ => (-2*(Real.log t)^2 - 8*Real.log t - 10)/t)
        (2*(1+Real.log x)^2/x^2) x := by
    intro x hx
    exact hasDerivAt_antideriv x (by have : (m:ℝ) ≤ x := hx; linarith)
  have hpos : ∀ x ∈ Ioi (m:ℝ), 0 ≤ 2*(1+Real.log x)^2/x^2 := by
    intro x hx; apply div_nonneg _ (by positivity); positivity
  have hint := MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hderiv hpos tendsto_antideriv
  have hval := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint tendsto_antideriv
  rw [hval, zero_sub]
  have hm0 : (0:ℝ) < (m:ℝ) := by linarith
  change -((-2*(Real.log (m:ℝ))^2 - 8*Real.log (m:ℝ) - 10)/(m:ℝ))
      = 2*((Real.log (m:ℝ))^2 + 4*Real.log (m:ℝ) + 5)/(m:ℝ)
  field_simp
  ring

/-- `2/(2⌊m/d⌋+1) ≤ 2d/m` for `1 ≤ d ≤ m`. -/
private lemma two_div_floor_le (m d : ℕ) (hd : 1 ≤ d) (hdm : d ≤ m) :
    2/(2*(((m/d:ℕ)):ℝ)+1) ≤ 2*(d:ℝ)/(m:ℝ) := by
  have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega)
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega)
  have hdmR : (d:ℝ) ≤ (m:ℝ) := by exact_mod_cast hdm
  have hbased : (m:ℝ) ≤ (((m/d:ℕ)):ℝ) * (d:ℝ) + (d:ℝ) := by
    have h1 : m < d * (m / d) + d := by
      have h2 := Nat.div_add_mod m d
      have h3 := Nat.mod_lt m (by omega : 0 < d)
      omega
    have h4 : (m:ℝ) < (d:ℝ) * (((m/d:ℕ)):ℝ) + (d:ℝ) := by exact_mod_cast h1
    linarith
  rw [div_le_div_iff₀ (by positivity) hm0]
  nlinarith [hbased, hd0, hm0, hdmR]

/-- `∑_{m<d≤N} 1/d² ≤ 1/m` for `m ≥ 1`. -/
private lemma sum_Ico_inv_sq_le (m N : ℕ) (hm : 1 ≤ m) :
    (∑ d ∈ Finset.Ico (m+1) (N+1), 1/((d:ℝ))^2) ≤ 1/(m:ℝ) := by
  have hsum : Summable (fun n : ℕ => if m < n then 1/(n:ℝ)^2 else 0) := by
    have h := Commons.Analysis.Series.tail_inv_sq_summable (m+1)
    refine h.congr (fun n => ?_)
    by_cases hn : m < n
    · rw [if_pos hn, if_pos (by omega)]
    · rw [if_neg hn, if_neg (by omega)]
  have hle : (∑ n ∈ Finset.Ico (m+1) (N+1), (if m < n then 1/(n:ℝ)^2 else 0))
      ≤ ∑' n : ℕ, (if m < n then 1/(n:ℝ)^2 else 0) :=
    hsum.sum_le_tsum _ (by
      intro n hn
      by_cases h : m < n
      · rw [if_pos h]; exact div_nonneg zero_le_one (sq_nonneg _)
      · rw [if_neg h])
  have hterm : (∑ d ∈ Finset.Ico (m+1) (N+1), (if m < d then 1/(d:ℝ)^2 else 0))
      = ∑ d ∈ Finset.Ico (m+1) (N+1), 1/(d:ℝ)^2 :=
    Finset.sum_congr rfl (fun x hx => by
      rw [if_pos (by have := (Finset.mem_Ico.mp hx).1; omega)])
  have htail : (∑' n : ℕ, (if m < n then 1/(n:ℝ)^2 else 0)) ≤ 1/(m:ℝ) := by
    have h := Commons.Analysis.Series.tail_inv_sq_le (m+1) (by omega)
    have heq : (∑' n : ℕ, (if m < n then 1/(n:ℝ)^2 else 0))
        = ∑' n : ℕ, (if m+1 ≤ n then 1/(n:ℝ)^2 else 0) := by
      apply tsum_congr; intro n
      simp only [Nat.lt_iff_add_one_le]
    rw [heq]
    refine h.trans ?_
    have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hden : (0:ℝ) < 2*(((m+1:ℕ)):ℝ) - 1 := by
      have : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
      push_cast; linarith
    rw [div_le_div_iff₀ hden hm0]; push_cast; nlinarith
  calc (∑ d ∈ Finset.Ico (m+1) (N+1), 1/((d:ℝ))^2)
      = ∑ d ∈ Finset.Ico (m+1) (N+1), (if m < d then 1/(d:ℝ)^2 else 0) := hterm.symm
    _ ≤ ∑' n : ℕ, (if m < n then 1/(n:ℝ)^2 else 0) := hle
    _ ≤ 1/(m:ℝ) := htail

/-- Tail of `∑ 2^{ω(d)}/d²`. -/
private lemma two_pow_omega_tail_div_sq_le (m N : ℕ) (hm : 1 ≤ m) :
    (∑ d ∈ (Icc 1 N).filter (fun d => m < d), (2:ℝ)^(d.primeFactors.card)/(d:ℝ)^2)
      ≤ 2*(1 + Real.log (m:ℝ))/(m:ℝ) + 2/(m:ℝ) := by
  rcases Nat.lt_or_ge N 1 with hN | hN
  · have hem : Icc 1 N = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
    rw [hem, Finset.filter_empty, Finset.sum_empty]
    have : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
    positivity
  · have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hdiv : ∀ d ∈ (Icc 1 N).filter (fun d => m < d),
        d.divisors = (Icc 1 N).filter (fun e => e ∣ d) := by
      intro d hd
      obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
      ext e
      rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hdvd, hne⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
          le_trans (Nat.le_of_dvd (by omega) hdvd) hdN⟩, hdvd⟩
      · rintro ⟨⟨he1, heN⟩, hdvd⟩
        exact ⟨hdvd, by omega⟩
    have hstep : (∑ d ∈ (Icc 1 N).filter (fun d => m < d), (2:ℝ)^(d.primeFactors.card)/(d:ℝ)^2)
        ≤ ∑ d' ∈ Icc 1 N, (if d' ≤ m then (2/(m:ℝ))/(d':ℝ) else (2:ℝ)/(d':ℝ)^2) := by
      have h1 : (∑ d ∈ (Icc 1 N).filter (fun d => m < d), (2:ℝ)^(d.primeFactors.card)/(d:ℝ)^2)
          = ∑ d ∈ (Icc 1 N).filter (fun d => m < d), ∑ e ∈ d.divisors,
              ((ArithmeticFunction.moebius e : ℝ))^2 * (1:ℝ)^(e.primeFactors.card) / (d:ℝ)^2 := by
        apply Finset.sum_congr rfl
        intro d hd
        have hd0 : d ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1; omega
        rw [show (2:ℝ) = 1 + 1 by norm_num, ← sum_moebius_sq_pow_omega_eq 1 d hd0, Finset.sum_div]
      rw [h1]
      have h2 : (∑ d ∈ (Icc 1 N).filter (fun d => m < d), ∑ e ∈ d.divisors,
            ((ArithmeticFunction.moebius e : ℝ))^2 * (1:ℝ)^(e.primeFactors.card) / (d:ℝ)^2)
          = ∑ e ∈ Icc 1 N, ∑ d ∈ (Icc 1 N).filter (fun d => m < d ∧ e ∣ d),
              ((ArithmeticFunction.moebius e : ℝ))^2 * (1:ℝ)^(e.primeFactors.card) / (d:ℝ)^2 := by
        calc (∑ d ∈ (Icc 1 N).filter (fun d => m < d), ∑ e ∈ d.divisors,
              ((ArithmeticFunction.moebius e : ℝ))^2 * (1:ℝ)^(e.primeFactors.card) / (d:ℝ)^2)
            = ∑ d ∈ (Icc 1 N).filter (fun d => m < d), ∑ e ∈ (Icc 1 N).filter (fun e => e ∣ d),
                ((ArithmeticFunction.moebius e : ℝ))^2 * (1:ℝ)^(e.primeFactors.card) / (d:ℝ)^2 := by
              apply Finset.sum_congr rfl; intro d hd
              exact Finset.sum_congr (hdiv d hd) (fun x hx => rfl)
          _ = ∑ d ∈ (Icc 1 N).filter (fun d => m < d), ∑ e ∈ Icc 1 N,
                (if e ∣ d then ((ArithmeticFunction.moebius e : ℝ))^2 * (1:ℝ)^(e.primeFactors.card)
                  / (d:ℝ)^2 else 0) := by
              apply Finset.sum_congr rfl; intro d hd; rw [Finset.sum_filter]
          _ = ∑ e ∈ Icc 1 N, ∑ d ∈ (Icc 1 N).filter (fun d => m < d),
                (if e ∣ d then ((ArithmeticFunction.moebius e : ℝ))^2 * (1:ℝ)^(e.primeFactors.card)
                  / (d:ℝ)^2 else 0) := Finset.sum_comm
          _ = ∑ e ∈ Icc 1 N, ∑ d ∈ (Icc 1 N).filter (fun d => m < d ∧ e ∣ d),
                ((ArithmeticFunction.moebius e : ℝ))^2 * (1:ℝ)^(e.primeFactors.card) / (d:ℝ)^2 := by
              apply Finset.sum_congr rfl; intro e he
              rw [← Finset.sum_filter, Finset.filter_filter (fun n => m < n) (fun n => e ∣ n) (Icc 1 N)]
      rw [h2]
      apply Finset.sum_le_sum
      intro e he
      obtain ⟨he1, heN⟩ := Finset.mem_Icc.mp he
      have hμ : ((ArithmeticFunction.moebius e : ℝ))^2 ≤ 1 := by
        rw [moebius_sq_cast]; split <;> norm_num
      have hone : ((1:ℝ)^(e.primeFactors.card)) = 1 := one_pow _
      by_cases hem : e ≤ m
      · rw [if_pos hem]
        have hb := inner_le_small m N e he1 hem
        calc (∑ d ∈ (Icc 1 N).filter (fun d => m < d ∧ e ∣ d),
              ((ArithmeticFunction.moebius e : ℝ))^2 * (1:ℝ)^(e.primeFactors.card) / (d:ℝ)^2)
            ≤ ∑ d ∈ (Icc 1 N).filter (fun d => m < d ∧ e ∣ d), 1/(d:ℝ)^2 := by
              apply Finset.sum_le_sum; intro d hd
              refine div_le_div_of_nonneg_right ?_ (by positivity)
              rw [hone, mul_one]; exact hμ
          _ ≤ (1/(e:ℝ)^2) * (2/(2*(((m/e:ℕ)):ℝ)+1)) := hb
          _ ≤ (2/(m:ℝ))/(e:ℝ) := by
              calc (1/(e:ℝ)^2) * (2/(2*(((m/e:ℕ)):ℝ)+1))
                  ≤ (1/(e:ℝ)^2) * (2*(e:ℝ)/(m:ℝ)) :=
                    mul_le_mul_of_nonneg_left (two_div_floor_le m e he1 hem) (by positivity)
                _ = (2/(m:ℝ))/(e:ℝ) := by
                  have he0 : (e:ℝ) ≠ 0 := by
                    exact_mod_cast (by omega : e ≠ 0)
                  have hm0' : (m:ℝ) ≠ 0 := by
                    exact_mod_cast (by omega : m ≠ 0)
                  field_simp
      · rw [if_neg hem]
        have hb := inner_le_large m N e he1
        calc (∑ d ∈ (Icc 1 N).filter (fun d => m < d ∧ e ∣ d),
              ((ArithmeticFunction.moebius e : ℝ))^2 * (1:ℝ)^(e.primeFactors.card) / (d:ℝ)^2)
            ≤ ∑ d ∈ (Icc 1 N).filter (fun d => m < d ∧ e ∣ d), 1/(d:ℝ)^2 := by
              apply Finset.sum_le_sum; intro d hd
              refine div_le_div_of_nonneg_right ?_ (by positivity)
              rw [hone, mul_one]; exact hμ
          _ ≤ (1/(e:ℝ)^2) * (1647/1000) := hb
          _ ≤ (2:ℝ)/(e:ℝ)^2 := by
              calc (1/(e:ℝ)^2) * (1647/1000) ≤ (1/(e:ℝ)^2) * 2 :=
                    mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
                _ = (2:ℝ)/(e:ℝ)^2 := by ring
    refine hstep.trans ?_
    have hsplit : (∑ d' ∈ Icc 1 N, (if d' ≤ m then (2/(m:ℝ))/(d':ℝ) else (2:ℝ)/(d':ℝ)^2))
        = (∑ d' ∈ Icc 1 N, (if d' ≤ m then (2/(m:ℝ))/(d':ℝ) else 0))
          + ∑ d' ∈ Icc 1 N, (if d' ≤ m then 0 else (2:ℝ)/(d':ℝ)^2) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro x hx
      by_cases h : x ≤ m <;> simp [h]
    rw [hsplit]
    apply add_le_add
    · have hb : (∑ d' ∈ Icc 1 N, (if d' ≤ m then (2/(m:ℝ))/(d':ℝ) else 0))
          = ∑ d' ∈ (Icc 1 N).filter (fun d' => d' ≤ m), (2/(m:ℝ))/(d':ℝ) := by
        rw [Finset.sum_filter]
      rw [hb]
      have hsub : (Icc 1 N).filter (fun d' => d' ≤ m) ⊆ Icc 1 m := by
        intro x hx; rw [Finset.mem_filter] at hx
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hx.1).1, hx.2⟩
      have hb2 : (∑ d' ∈ (Icc 1 N).filter (fun d' => d' ≤ m), (2/(m:ℝ))/(d':ℝ))
          ≤ (2/(m:ℝ)) * (1 + Real.log (m:ℝ)) := by
        calc (∑ d' ∈ (Icc 1 N).filter (fun d' => d' ≤ m), (2/(m:ℝ))/(d':ℝ))
            ≤ ∑ d' ∈ Icc 1 m, (2/(m:ℝ))/(d':ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x hx _ => by positivity)
          _ = (2/(m:ℝ)) * ∑ d' ∈ Icc 1 m, 1/(d':ℝ) := by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x hx; ring
          _ ≤ (2/(m:ℝ)) * (1 + Real.log (m:ℝ)) :=
              mul_le_mul_of_nonneg_left
                (Commons.Analysis.ExpLog.harmonic_le_one_add_log m hm) (by positivity)
      refine hb2.trans ?_
      rw [show (2/(m:ℝ)) * (1 + Real.log (m:ℝ)) = 2*(1 + Real.log (m:ℝ))/(m:ℝ) by ring]
    · have hb : (∑ d' ∈ Icc 1 N, (if d' ≤ m then 0 else (2:ℝ)/(d':ℝ)^2))
          = ∑ d' ∈ (Icc 1 N).filter (fun d' => ¬ d' ≤ m), (2:ℝ)/(d':ℝ)^2 := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl; intro x hx
        by_cases h : x ≤ m <;> simp [h]
      rw [hb]
      have hfil : (Icc 1 N).filter (fun d' => ¬ d' ≤ m) = Finset.Ico (m+1) (N+1) := by
        ext x; rw [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc]; omega
      rw [hfil]
      have := sum_Ico_inv_sq_le m N hm
      calc (∑ d' ∈ Finset.Ico (m+1) (N+1), (2:ℝ)/(d':ℝ)^2)
          = 2 * ∑ d' ∈ Finset.Ico (m+1) (N+1), 1/(d':ℝ)^2 := by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x hx; ring
        _ ≤ 2 * (1/(m:ℝ)) := mul_le_mul_of_nonneg_left this (by norm_num)
        _ = 2/(m:ℝ) := by ring

/-- Tail bound for `∑ μ(e)² 3^{ω(e)}/e²`. -/
private lemma Q1_tail_le (m N : ℕ) (hm : 1 ≤ m) :
    (∑ e ∈ (Icc 1 N).filter (fun e => m < e),
        ((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card) / (e:ℝ)^2)
      ≤ 2*(1 + Real.log (m:ℝ))^2/(m:ℝ)
          + 1647/1000*(2*(1 + Real.log (m:ℝ))/(m:ℝ) + 2/(m:ℝ)) := by
  rcases Nat.lt_or_ge N 1 with hN | hN
  · have hem : Icc 1 N = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
    rw [hem, Finset.filter_empty, Finset.sum_empty]
    have : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
    positivity
  · have hdiv : ∀ e ∈ (Icc 1 N).filter (fun e => m < e),
        e.divisors = (Icc 1 N).filter (fun d => d ∣ e) := by
      intro e he
      obtain ⟨he1, heN⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp he).1
      ext d
      rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hdvd, hne⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
          le_trans (Nat.le_of_dvd (by omega) hdvd) heN⟩, hdvd⟩
      · rintro ⟨⟨hd1, hdN⟩, hdvd⟩
        exact ⟨hdvd, by omega⟩
    have hstep1 : (∑ e ∈ (Icc 1 N).filter (fun e => m < e),
          ((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card)/(e:ℝ)^2)
        ≤ ∑ e ∈ (Icc 1 N).filter (fun e => m < e),
            (∑ d ∈ e.divisors, (2:ℝ)^(d.primeFactors.card)) / (e:ℝ)^2 := by
      apply Finset.sum_le_sum
      intro e he
      have he0 : e ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp he).1).1; omega
      have hμ : ((ArithmeticFunction.moebius e : ℝ))^2 ≤ 1 := by
        rw [moebius_sq_cast]; split <;> norm_num
      rw [show (3:ℝ) = 1 + 2 by norm_num, ← sum_moebius_sq_pow_omega_eq 2 e he0]
      have hlnn : (0:ℝ) ≤ ∑ d ∈ e.divisors,
          ((ArithmeticFunction.moebius d : ℝ))^2 * (2:ℝ)^(d.primeFactors.card) :=
        Finset.sum_nonneg (fun d hd => by positivity)
      have hle : (∑ d ∈ e.divisors, ((ArithmeticFunction.moebius d : ℝ))^2 * (2:ℝ)^(d.primeFactors.card))
          ≤ ∑ d ∈ e.divisors, (2:ℝ)^(d.primeFactors.card) := by
        apply Finset.sum_le_sum; intro d hd
        have hμd : ((ArithmeticFunction.moebius d : ℝ))^2 ≤ 1 := by
          rw [moebius_sq_cast]; split <;> norm_num
        nlinarith [hμd, pow_pos (by norm_num : (0:ℝ) < 2) d.primeFactors.card]
      calc ((ArithmeticFunction.moebius e : ℝ))^2
            * (∑ d ∈ e.divisors, ((ArithmeticFunction.moebius d : ℝ))^2 * (2:ℝ)^(d.primeFactors.card))
            / (e:ℝ)^2
          ≤ 1 * (∑ d ∈ e.divisors, (2:ℝ)^(d.primeFactors.card)) / (e:ℝ)^2 := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul hμ hle hlnn (by norm_num)
        _ = (∑ d ∈ e.divisors, (2:ℝ)^(d.primeFactors.card)) / (e:ℝ)^2 := by ring
    have hstep2 : (∑ e ∈ (Icc 1 N).filter (fun e => m < e),
            (∑ d ∈ e.divisors, (2:ℝ)^(d.primeFactors.card)) / (e:ℝ)^2)
        = ∑ d ∈ Icc 1 N, ∑ e ∈ (Icc 1 N).filter (fun e => m < e ∧ d ∣ e),
            (2:ℝ)^(d.primeFactors.card) / (e:ℝ)^2 := by
      calc (∑ e ∈ (Icc 1 N).filter (fun e => m < e),
              (∑ d ∈ e.divisors, (2:ℝ)^(d.primeFactors.card)) / (e:ℝ)^2)
          = ∑ e ∈ (Icc 1 N).filter (fun e => m < e), ∑ d ∈ e.divisors,
              (2:ℝ)^(d.primeFactors.card) / (e:ℝ)^2 := by
            apply Finset.sum_congr rfl; intro e he; rw [Finset.sum_div]
        _ = ∑ e ∈ (Icc 1 N).filter (fun e => m < e), ∑ d ∈ (Icc 1 N).filter (fun d => d ∣ e),
              (2:ℝ)^(d.primeFactors.card) / (e:ℝ)^2 := by
            apply Finset.sum_congr rfl; intro e he
            exact Finset.sum_congr (hdiv e he) (fun x hx => rfl)
        _ = ∑ e ∈ (Icc 1 N).filter (fun e => m < e), ∑ d ∈ Icc 1 N,
              (if d ∣ e then (2:ℝ)^(d.primeFactors.card) / (e:ℝ)^2 else 0) := by
            apply Finset.sum_congr rfl; intro e he; rw [Finset.sum_filter]
        _ = ∑ d ∈ Icc 1 N, ∑ e ∈ (Icc 1 N).filter (fun e => m < e),
              (if d ∣ e then (2:ℝ)^(d.primeFactors.card) / (e:ℝ)^2 else 0) := Finset.sum_comm
        _ = ∑ d ∈ Icc 1 N, ∑ e ∈ (Icc 1 N).filter (fun e => m < e ∧ d ∣ e),
              (2:ℝ)^(d.primeFactors.card) / (e:ℝ)^2 := by
            apply Finset.sum_congr rfl; intro d hd
            rw [← Finset.sum_filter, Finset.filter_filter (fun n => m < n) (fun n => d ∣ n) (Icc 1 N)]
    have hmain : (∑ d ∈ Icc 1 N, ∑ e ∈ (Icc 1 N).filter (fun e => m < e ∧ d ∣ e),
            (2:ℝ)^(d.primeFactors.card) / (e:ℝ)^2)
        ≤ 2*(1 + Real.log (m:ℝ))^2/(m:ℝ)
            + 1647/1000*(2*(1 + Real.log (m:ℝ))/(m:ℝ) + 2/(m:ℝ)) := by
      have hinner : ∀ d ∈ Icc 1 N,
          (∑ e ∈ (Icc 1 N).filter (fun e => m < e ∧ d ∣ e), (2:ℝ)^(d.primeFactors.card) / (e:ℝ)^2)
            ≤ (if d ≤ m then (2/(m:ℝ))/(d:ℝ) * (2:ℝ)^(d.primeFactors.card)
                else (1647/1000)/(d:ℝ)^2 * (2:ℝ)^(d.primeFactors.card)) := by
        intro d hd
        obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
        have h2 : (0:ℝ) ≤ (2:ℝ)^(d.primeFactors.card) := by positivity
        by_cases hdm : d ≤ m
        · rw [if_pos hdm]
          have hb := inner_le_small m N d hd1 hdm
          calc (∑ e ∈ (Icc 1 N).filter (fun e => m < e ∧ d ∣ e), (2:ℝ)^(d.primeFactors.card) / (e:ℝ)^2)
              = (2:ℝ)^(d.primeFactors.card)
                * ∑ n ∈ (Icc 1 N).filter (fun n => m < n ∧ d ∣ n), 1/(n:ℝ)^2 := by
                have h1 : (∑ e ∈ (Icc 1 N).filter (fun e => m < e ∧ d ∣ e), (2:ℝ)^(d.primeFactors.card) / (e:ℝ)^2)
                    = ∑ e ∈ (Icc 1 N).filter (fun e => m < e ∧ d ∣ e), (2:ℝ)^(d.primeFactors.card) * (1/(e:ℝ)^2) := by
                  apply Finset.sum_congr rfl; intro n hn; rw [div_eq_mul_inv, one_div]
                rw [h1, ← Finset.mul_sum]
            _ ≤ (2:ℝ)^(d.primeFactors.card) * ((1/(d:ℝ)^2) * (2/(2*(((m/d:ℕ)):ℝ)+1))) :=
                mul_le_mul_of_nonneg_left hb h2
            _ ≤ (2/(m:ℝ))/(d:ℝ) * (2:ℝ)^(d.primeFactors.card) := by
                have hq := two_div_floor_le m d hd1 hdm
                have h1 : (2:ℝ)^(d.primeFactors.card)
                    * ((1/(d:ℝ)^2) * (2/(2*(((m/d:ℕ)):ℝ)+1)))
                    ≤ (2:ℝ)^(d.primeFactors.card) * ((1/(d:ℝ)^2) * (2*(d:ℝ)/(m:ℝ))) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left hq (by positivity)) h2
                calc (2:ℝ)^(d.primeFactors.card)
                      * ((1/(d:ℝ)^2) * (2/(2*(((m/d:ℕ)):ℝ)+1)))
                    ≤ (2:ℝ)^(d.primeFactors.card) * ((1/(d:ℝ)^2) * (2*(d:ℝ)/(m:ℝ))) := h1
                  _ = (2/(m:ℝ))/(d:ℝ) * (2:ℝ)^(d.primeFactors.card) := by
                    have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
                    have hm0' : (m:ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
                    field_simp
        · rw [if_neg hdm]
          have hb := inner_le_large m N d hd1
          calc (∑ e ∈ (Icc 1 N).filter (fun e => m < e ∧ d ∣ e), (2:ℝ)^(d.primeFactors.card) / (e:ℝ)^2)
              = (2:ℝ)^(d.primeFactors.card)
                * ∑ n ∈ (Icc 1 N).filter (fun n => m < n ∧ d ∣ n), 1/(n:ℝ)^2 := by
                have h1 : (∑ e ∈ (Icc 1 N).filter (fun e => m < e ∧ d ∣ e), (2:ℝ)^(d.primeFactors.card) / (e:ℝ)^2)
                    = ∑ e ∈ (Icc 1 N).filter (fun e => m < e ∧ d ∣ e), (2:ℝ)^(d.primeFactors.card) * (1/(e:ℝ)^2) := by
                  apply Finset.sum_congr rfl; intro n hn; rw [div_eq_mul_inv, one_div]
                rw [h1, ← Finset.mul_sum]
            _ ≤ (2:ℝ)^(d.primeFactors.card) * ((1/(d:ℝ)^2) * (1647/1000)) :=
                mul_le_mul_of_nonneg_left hb h2
            _ = (1647/1000)/(d:ℝ)^2 * (2:ℝ)^(d.primeFactors.card) := by ring
      refine (Finset.sum_le_sum hinner).trans ?_
      have hsplit : (∑ d ∈ Icc 1 N, (if d ≤ m then (2/(m:ℝ))/(d:ℝ) * (2:ℝ)^(d.primeFactors.card)
              else (1647/1000)/(d:ℝ)^2 * (2:ℝ)^(d.primeFactors.card)))
          = (∑ d ∈ Icc 1 N, (if d ≤ m then (2/(m:ℝ))/(d:ℝ) * (2:ℝ)^(d.primeFactors.card) else 0))
            + ∑ d ∈ Icc 1 N,
                (if d ≤ m then 0 else (1647/1000)/(d:ℝ)^2 * (2:ℝ)^(d.primeFactors.card)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro x hx
        by_cases h : x ≤ m <;> simp [h]
      rw [hsplit]
      apply add_le_add
      · have hb : (∑ d ∈ Icc 1 N, (if d ≤ m then (2/(m:ℝ))/(d:ℝ) * (2:ℝ)^(d.primeFactors.card) else 0))
            = ∑ d ∈ (Icc 1 N).filter (fun d => d ≤ m),
                (2/(m:ℝ))/(d:ℝ) * (2:ℝ)^(d.primeFactors.card) := by
          rw [Finset.sum_filter]
        rw [hb]
        have hsub : (Icc 1 N).filter (fun d => d ≤ m) ⊆ Icc 1 m := by
          intro x hx; rw [Finset.mem_filter] at hx
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hx.1).1, hx.2⟩
        have hb2 : (∑ d ∈ (Icc 1 N).filter (fun d => d ≤ m),
              (2/(m:ℝ))/(d:ℝ) * (2:ℝ)^(d.primeFactors.card))
            ≤ 2*(1 + Real.log (m:ℝ))^2/(m:ℝ) := by
          calc (∑ d ∈ (Icc 1 N).filter (fun d => d ≤ m),
                (2/(m:ℝ))/(d:ℝ) * (2:ℝ)^(d.primeFactors.card))
              ≤ ∑ d ∈ Icc 1 m, (2/(m:ℝ))/(d:ℝ) * (2:ℝ)^(d.primeFactors.card) :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x hx _ => by positivity)
            _ = (2/(m:ℝ)) * ∑ d ∈ Icc 1 m, (2:ℝ)^(d.primeFactors.card)/(d:ℝ) := by
                rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x hx; ring
            _ ≤ (2/(m:ℝ)) * (1 + Real.log (m:ℝ))^2 :=
                mul_le_mul_of_nonneg_left (two_pow_omega_div_le m hm) (by positivity)
            _ = 2*(1 + Real.log (m:ℝ))^2/(m:ℝ) := by ring
        exact hb2
      · have hb : (∑ d ∈ Icc 1 N, (if d ≤ m then 0 else (1647/1000)/(d:ℝ)^2 * (2:ℝ)^(d.primeFactors.card)))
            = ∑ d ∈ (Icc 1 N).filter (fun d => ¬ d ≤ m),
                (1647/1000)/(d:ℝ)^2 * (2:ℝ)^(d.primeFactors.card) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl; intro x hx
          by_cases h : x ≤ m <;> simp [h]
        rw [hb]
        have hfil : (Icc 1 N).filter (fun d => ¬ d ≤ m) = (Icc 1 N).filter (fun d => m < d) := by
          ext x; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
        rw [hfil]
        have hsel : (∑ d ∈ (Icc 1 N).filter (fun d => m < d),
              (1647/1000)/(d:ℝ)^2 * (2:ℝ)^(d.primeFactors.card))
            = (1647/1000) * ∑ d ∈ (Icc 1 N).filter (fun d => m < d), (2:ℝ)^(d.primeFactors.card)/(d:ℝ)^2 := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x hx; ring
        rw [hsel]
        have hp := two_pow_omega_tail_div_sq_le m N hm
        calc (1647/1000) * ∑ d ∈ (Icc 1 N).filter (fun d => m < d), (2:ℝ)^(d.primeFactors.card)/(d:ℝ)^2
            ≤ (1647/1000) * (2*(1 + Real.log (m:ℝ))/(m:ℝ) + 2/(m:ℝ)) :=
              mul_le_mul_of_nonneg_left hp (by norm_num)
          _ = 1647/1000*(2*(1 + Real.log (m:ℝ))/(m:ℝ) + 2/(m:ℝ)) := by ring
    exact hstep1.trans (hstep2.trans_le hmain)

open MeasureTheory Filter intervalIntegral Set in
/-- `log x ≥ 2(x-1)/(x+1)` for `x ≥ 1`. -/
private lemma two_mul_sub_div_le_log {x : ℝ} (hx : 1 ≤ x) :
    2*(x-1)/(x+1) ≤ Real.log x := by
  have hmono : MonotoneOn (fun t : ℝ => Real.log t - 2*(t-1)/(t+1)) (Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · apply ContinuousOn.sub
      · exact Real.continuousOn_log.mono (fun t ht => by
          have h1 : (1:ℝ) ≤ t := ht
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro h0
          linarith)
      · exact ((continuous_const.mul (continuous_id.sub continuous_const)).continuousOn).div
          ((continuous_id.add continuous_const).continuousOn)
          (fun t ht => by have h1 : (1:ℝ) ≤ t := ht; positivity)
    · intro t ht
      rw [interior_Ici] at ht
      have ht1 : (1:ℝ) < t := ht
      have ht0 : (0:ℝ) < t := by linarith
      have h1 : DifferentiableAt ℝ (fun t : ℝ => 2*(t-1)/(t+1)) t := by
        apply DifferentiableAt.div
        · fun_prop
        · fun_prop
        · positivity
      exact ((Real.differentiableAt_log (ne_of_gt ht0)).sub h1).differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht1 : (1:ℝ) < t := ht
      have ht0 : (0:ℝ) < t := by linarith
      have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log (ne_of_gt ht0)
      have hquo : HasDerivAt (fun t : ℝ => 2*(t-1)/(t+1)) ((2*(t+1) - 2*(t-1)*1)/(t+1)^2) t := by
        have hnum : HasDerivAt (fun t : ℝ => 2*(t-1)) 2 t := by
          simpa using ((hasDerivAt_id t).sub_const 1).const_mul 2
        have hden : HasDerivAt (fun t : ℝ => t+1) 1 t := (hasDerivAt_id t).add_const 1
        exact hnum.div hden (by positivity)
      have hF : HasDerivAt (fun t : ℝ => Real.log t - 2*(t-1)/(t+1))
          (t⁻¹ - (2*(t+1) - 2*(t-1)*1)/(t+1)^2) t := hlog.sub hquo
      rw [hF.deriv]
      have heq : t⁻¹ - (2*(t+1) - 2*(t-1)*1)/(t+1)^2 = (t-1)^2/(t*(t+1)^2) := by
        have h1 : t ≠ 0 := ne_of_gt ht0
        have h2 : t + 1 ≠ 0 := by positivity
        field_simp
        ring
      rw [heq]
      positivity
  have h := hmono (Set.mem_Ici.mpr (le_refl 1) : (1:ℝ) ∈ Set.Ici 1) hx hx
  simp only [Real.log_one] at h
  linarith

open MeasureTheory Filter intervalIntegral Set in
/-- `log (1+u) ≤ u - u²/2 + u³/3` for `u ≥ 0`. -/
private lemma log_one_add_le {u : ℝ} (hu : 0 ≤ u) :
    Real.log (1+u) ≤ u - u^2/2 + u^3/3 := by
  have hmono : MonotoneOn (fun t : ℝ => t - t^2/2 + t^3/3 - Real.log (1+t)) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · apply ContinuousOn.sub
      · fun_prop
      · refine ContinuousOn.comp Real.continuousOn_log (by fun_prop :
            ContinuousOn (fun t : ℝ => 1+t) (Ici 0)) ?_
        intro t ht
        have h1 : (0:ℝ) ≤ t := ht
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h0
        linarith
    · intro t ht
      rw [interior_Ici] at ht
      have ht' : (0:ℝ) < t := ht
      have h1 : DifferentiableAt ℝ (fun t : ℝ => t - t^2/2 + t^3/3) t := by fun_prop
      have h2 : DifferentiableAt ℝ (fun t : ℝ => Real.log (1+t)) t :=
        (Real.differentiableAt_log (by positivity : (1:ℝ) + t ≠ 0)).comp t (by fun_prop)
      exact (h1.sub h2).differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht' : (0:ℝ) < t := ht
      have h2 : HasDerivAt (fun t : ℝ => t^2/2) ((2*t^(2-1)*1)/2) t := by
        simpa using ((hasDerivAt_id t).pow 2).div_const 2
      have h3 : HasDerivAt (fun t : ℝ => t^3/3) ((3*t^(3-1)*1)/3) t := by
        simpa using ((hasDerivAt_id t).pow 3).div_const 3
      have hpoly : HasDerivAt (fun t : ℝ => t - t^2/2 + t^3/3)
          ((1 - (2*t^(2-1)*1)/2) + (3*t^(3-1)*1)/3) t := ((hasDerivAt_id t).sub h2).add h3
      have hlog : HasDerivAt (fun t : ℝ => Real.log (1+t)) ((1+t)⁻¹ * 1) t := by
        have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 t := (hasDerivAt_id t).const_add 1
        exact (Real.hasDerivAt_log (show (1:ℝ)+t ≠ 0 by positivity)).comp t h1
      have hF : HasDerivAt (fun t : ℝ => t - t^2/2 + t^3/3 - Real.log (1+t))
          (((1 - (2*t^(2-1)*1)/2) + (3*t^(3-1)*1)/3) - (1+t)⁻¹ * 1) t := hpoly.sub hlog
      rw [hF.deriv]
      have heq : ((1 - (2*t^(2-1)*1)/2) + (3*t^(3-1)*1)/3) - (1+t)⁻¹ * 1 = t^3/(1+t) := by
        have h2 : (1:ℝ) + t ≠ 0 := by positivity
        field_simp
        ring
      rw [heq]
      positivity
  have h := hmono (Set.mem_Ici.mpr (le_refl 0) : (0:ℝ) ∈ Set.Ici 0) hu hu
  have h0 : (fun t : ℝ => t - t^2/2 + t^3/3 - Real.log (1+t)) 0 = 0 := by
    norm_num
  rw [h0] at h
  linarith

open MeasureTheory Filter intervalIntegral Set in
/-- Lower bound chain: `llo n ≤ log n` for `n ≥ 2`. -/
private def llo (n : ℕ) : ℝ :=
  0.6931471803 + ∑ j ∈ Finset.Ico 3 (n+1), (2:ℝ)/(2*(j:ℝ)-1)

private lemma llo_nonneg (n : ℕ) : 0 ≤ llo n := by
  have hsum : (0:ℝ) ≤ ∑ j ∈ Finset.Ico 3 (n+1), (2:ℝ)/(2*(j:ℝ)-1) :=
    Finset.sum_nonneg (fun j hj => by
      have h1 : (1:ℝ) ≤ (j:ℝ) := by
        have h2 : 3 ≤ j := (Finset.mem_Ico.mp hj).1
        exact_mod_cast (by omega : 1 ≤ j)
      have h2 : (0:ℝ) < 2*(j:ℝ)-1 := by linarith
      exact div_nonneg (by norm_num) h2.le)
  simp only [llo]
  linarith

private lemma llo_le_log (n : ℕ) (hn : 2 ≤ n) : llo n ≤ Real.log (n:ℝ) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h2 : llo 2 = 0.6931471803 := by norm_num [llo, Finset.sum_Ico_eq_sum_range]
    rw [h2]
    exact le_of_lt Real.log_two_gt_d9
  | succ k hk ih =>
    have hsum : llo (k+1) = llo k + 2/(2*((k+1:ℕ):ℝ)-1) := by
      simp only [llo]
      rw [Finset.sum_Ico_succ_top (by omega : 3 ≤ k+1)]
      norm_num
      ring
    have hk0 : (0:ℝ) < (k:ℝ) := by
      have h2 : (2:ℕ) ≤ k := hk
      exact_mod_cast (by omega : 0 < k)
    have hx : (1:ℝ) ≤ ((k:ℝ)+1)/(k:ℝ) := by
      rw [le_div_iff₀ hk0]; linarith
    have hlog := two_mul_sub_div_le_log hx
    rw [Real.log_div (by positivity) (ne_of_gt hk0)] at hlog
    have hsimp : 2*(((k:ℝ)+1)/(k:ℝ)-1)/(((k:ℝ)+1)/(k:ℝ)+1) = 2/(2*(k:ℝ)+1) := by
      field_simp
      ring
    rw [hsimp] at hlog
    have hcast : 2/(2*((k+1:ℕ):ℝ)-1) = 2/(2*(k:ℝ)+1) := by push_cast; ring
    rw [hsum, hcast]
    push_cast at ih ⊢
    linarith

open MeasureTheory Filter intervalIntegral Set in
/-- Upper bound chain: `log n ≤ lhi n` for `n ≥ 2`. -/
private def lhi (n : ℕ) : ℝ :=
  0.6931471808 + ∑ j ∈ Finset.Ico 3 (n+1),
    ((1:ℝ)/((j:ℝ)-1) - 1/(2*((j:ℝ)-1)^2) + 1/(3*((j:ℝ)-1)^3))

private lemma log_le_lhi (n : ℕ) (hn : 2 ≤ n) : Real.log (n:ℝ) ≤ lhi n := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h2 : lhi 2 = 0.6931471808 := by norm_num [lhi, Finset.sum_Ico_eq_sum_range]
    rw [h2]
    exact le_of_lt Real.log_two_lt_d9
  | succ k hk ih =>
    have hsum : lhi (k+1) = lhi k + (1/(k:ℝ) - 1/(2*(k:ℝ)^2) + 1/(3*(k:ℝ)^3)) := by
      simp only [lhi]
      rw [Finset.sum_Ico_succ_top (by omega : 3 ≤ k+1)]
      push_cast
      ring
    have hk0 : (0:ℝ) < (k:ℝ) := by
      have h2 : (2:ℕ) ≤ k := hk
      exact_mod_cast (by omega : 0 < k)
    have hle := log_one_add_le (u := (1:ℝ)/(k:ℝ)) (by positivity)
    have h1k : (1:ℝ) + 1/(k:ℝ) = ((k:ℝ)+1)/(k:ℝ) := by
      field_simp
    rw [h1k, Real.log_div (by positivity) (ne_of_gt hk0)] at hle
    have hsimp : (1/(k:ℝ) - (1/(k:ℝ))^2/2 + (1/(k:ℝ))^3/3)
        = (1/(k:ℝ) - 1/(2*(k:ℝ)^2) + 1/(3*(k:ℝ)^3)) := by
      field_simp
      try ring
    rw [hsimp] at hle
    rw [hsum]
    push_cast at ih ⊢
    linarith [ih, hle]

/-- `log 21 ≥ 3`. -/
private lemma log_21_ge_three : (3:ℝ) ≤ Real.log 21 := by
  have h := llo_le_log 21 (by norm_num)
  norm_num [llo, Finset.sum_Ico_eq_sum_range] at h
  linarith

/-- Monotonicity of the polynomial `P`. -/
private lemma P_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    2*(1+a)^3 + (1647/1000)*(2*(1+a)^2 + (1647/1000)*(2*(1+a)+2))
      ≤ 2*(1+b)^3 + (1647/1000)*(2*(1+b)^2 + (1647/1000)*(2*(1+b)+2)) := by
  have h1 : (0:ℝ) ≤ 1 + a := by linarith
  have h3 : (1+a)^3 ≤ (1+b)^3 := pow_le_pow_left₀ h1 (by linarith) 3
  have h2 : (1+a)^2 ≤ (1+b)^2 := pow_le_pow_left₀ h1 (by linarith) 2
  have h1' : 1+a ≤ 1+b := by linarith
  nlinarith [h3, h2, h1']

/-- Pointwise bound for the `e`-th term of the divisor decomposition (large `m`). -/
private lemma inner_term_le (m N e : ℕ) (hm : 1 ≤ m) (he : 1 ≤ e) :
    (((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card)) *
        (∑ n ∈ (Icc 1 N).filter (fun n => m < n ∧ e ∣ n), 1/(n:ℝ)^2)
      ≤ (if e ≤ m
          then (2/(m:ℝ)) * ((((ArithmeticFunction.moebius e : ℝ))^2
                * (3:ℝ)^(e.primeFactors.card))/(e:ℝ))
          else (1647/1000) * ((((ArithmeticFunction.moebius e : ℝ))^2
                * (3:ℝ)^(e.primeFactors.card))/(e:ℝ)^2)) := by
  have hb : (0:ℝ) ≤ ((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card) := by
    positivity
  by_cases hem : e ≤ m
  · rw [if_pos hem]
    have hs := inner_le_small m N e he hem
    have hq := two_div_floor_le m e he hem
    calc (((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card)) *
          (∑ n ∈ (Icc 1 N).filter (fun n => m < n ∧ e ∣ n), 1/(n:ℝ)^2)
        ≤ (((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card)) *
            ((1/(e:ℝ)^2) * (2/(2*(((m/e:ℕ)):ℝ)+1))) := mul_le_mul_of_nonneg_left hs hb
      _ ≤ (((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card)) *
            ((1/(e:ℝ)^2) * (2*(e:ℝ)/(m:ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (by positivity)) hb
      _ = (2/(m:ℝ)) * ((((ArithmeticFunction.moebius e : ℝ))^2
            * (3:ℝ)^(e.primeFactors.card))/(e:ℝ)) := by
          have he0 : (e:ℝ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
          have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
          field_simp
          try ring
  · rw [if_neg hem]
    have hs := inner_le_large m N e he
    calc (((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card)) *
          (∑ n ∈ (Icc 1 N).filter (fun n => m < n ∧ e ∣ n), 1/(n:ℝ)^2)
        ≤ (((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card)) *
            ((1/(e:ℝ)^2) * (1647/1000)) := mul_le_mul_of_nonneg_left hs hb
      _ = (1647/1000) * ((((ArithmeticFunction.moebius e : ℝ))^2
            * (3:ℝ)^(e.primeFactors.card))/(e:ℝ)^2) := by ring

/-- Pointwise bound for the `e`-th term of the divisor decomposition with `m = 1`. -/
private lemma inner_term_le_one (N e : ℕ) (he : 1 ≤ e) :
    (((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card)) *
        (∑ n ∈ (Icc 1 N).filter (fun n => 1 < n ∧ e ∣ n), 1/(n:ℝ)^2)
      ≤ (if e = 1 then (2/3:ℝ)
          else (1647/1000) * ((((ArithmeticFunction.moebius e : ℝ))^2
                * (3:ℝ)^(e.primeFactors.card))/(e:ℝ)^2)) := by
  have hb : (0:ℝ) ≤ ((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card) := by
    positivity
  by_cases he1 : e = 1
  · subst he1
    rw [if_pos rfl]
    have hs := inner_le_small 1 N 1 (le_refl 1) (le_refl 1)
    have hb1 : ((ArithmeticFunction.moebius 1 : ℝ))^2 * (3:ℝ)^((1:ℕ).primeFactors.card) = 1 := by
      norm_num
    have hs' : (∑ n ∈ (Icc 1 N).filter (fun n => 1 < n ∧ 1 ∣ n), 1/(n:ℝ)^2) ≤ 2/3 := by
      refine hs.trans ?_
      norm_num
    rw [hb1, one_mul]
    exact hs'
  · rw [if_neg he1]
    have hs := inner_le_large 1 N e he
    calc (((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card)) *
          (∑ n ∈ (Icc 1 N).filter (fun n => 1 < n ∧ e ∣ n), 1/(n:ℝ)^2)
        ≤ (((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card)) *
            ((1/(e:ℝ)^2) * (1647/1000)) := mul_le_mul_of_nonneg_left hs hb
      _ = (1647/1000) * ((((ArithmeticFunction.moebius e : ℝ))^2
            * (3:ℝ)^(e.primeFactors.card))/(e:ℝ)^2) := by ring

/-- Bound of `Σ(m,N)` by the ``large `m`'' expression. -/
private lemma Sigma_le_BQ (m N : ℕ) (hm : 1 ≤ m) :
    (∑ n ∈ (Icc 1 N).filter (fun n => m < n),
        ((ArithmeticFunction.moebius n : ℝ))^2 * (n.divisors.card : ℝ)^2 / (n:ℝ)^2)
      ≤ 2*(1 + Real.log (m:ℝ))^3/(m:ℝ)
        + (1647/1000)*(2*(1 + Real.log (m:ℝ))^2/(m:ℝ)
            + 1647/1000*(2*(1 + Real.log (m:ℝ))/(m:ℝ) + 2/(m:ℝ))) := by
  refine (Sigma_le_decomp m N).trans ?_
  refine (Finset.sum_le_sum (fun e he =>
    inner_term_le m N e hm (Finset.mem_Icc.mp he).1)).trans ?_
  have hsplit : (∑ e ∈ Icc 1 N, (if e ≤ m
        then (2/(m:ℝ)) * ((((ArithmeticFunction.moebius e : ℝ))^2
              * (3:ℝ)^(e.primeFactors.card))/(e:ℝ))
        else (1647/1000) * ((((ArithmeticFunction.moebius e : ℝ))^2
              * (3:ℝ)^(e.primeFactors.card))/(e:ℝ)^2)))
      = (∑ e ∈ Icc 1 N, (if e ≤ m
            then (2/(m:ℝ)) * ((((ArithmeticFunction.moebius e : ℝ))^2
                  * (3:ℝ)^(e.primeFactors.card))/(e:ℝ)) else 0))
        + ∑ e ∈ Icc 1 N, (if e ≤ m then 0
            else (1647/1000) * ((((ArithmeticFunction.moebius e : ℝ))^2
                  * (3:ℝ)^(e.primeFactors.card))/(e:ℝ)^2)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases h : x ≤ m <;> simp [h]
  rw [hsplit]
  apply add_le_add
  · have hb : (∑ e ∈ Icc 1 N, (if e ≤ m
          then (2/(m:ℝ)) * ((((ArithmeticFunction.moebius e : ℝ))^2
                * (3:ℝ)^(e.primeFactors.card))/(e:ℝ)) else 0))
        = (2/(m:ℝ)) * ∑ e ∈ (Icc 1 N).filter (fun e => e ≤ m),
            (((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card))/(e:ℝ) := by
      rw [Finset.mul_sum, Finset.sum_filter]
    rw [hb]
    have hsub : (Icc 1 N).filter (fun e => e ≤ m) ⊆ Icc 1 m := by
      intro x hx
      rw [Finset.mem_filter] at hx
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hx.1).1, hx.2⟩
    calc (2/(m:ℝ)) * ∑ e ∈ (Icc 1 N).filter (fun e => e ≤ m),
            (((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card))/(e:ℝ)
        ≤ (2/(m:ℝ)) * ∑ e ∈ Icc 1 m,
            (((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card))/(e:ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x hx _ => by positivity)
      _ ≤ (2/(m:ℝ)) * (1 + Real.log (m:ℝ))^3 :=
          mul_le_mul_of_nonneg_left (sum_sqfree_three_pow_omega_div_le m hm) (by positivity)
      _ = 2*(1 + Real.log (m:ℝ))^3/(m:ℝ) := by ring
  · have hb : (∑ e ∈ Icc 1 N, (if e ≤ m then 0
          else (1647/1000) * ((((ArithmeticFunction.moebius e : ℝ))^2
                * (3:ℝ)^(e.primeFactors.card))/(e:ℝ)^2)))
        = (1647/1000) * ∑ e ∈ (Icc 1 N).filter (fun e => m < e),
            (((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card))/(e:ℝ)^2 := by
      have h1 : (∑ e ∈ (Icc 1 N).filter (fun e => m < e),
            (1647/1000) * ((((ArithmeticFunction.moebius e : ℝ))^2
              * (3:ℝ)^(e.primeFactors.card))/(e:ℝ)^2))
          = ∑ e ∈ Icc 1 N, (if m < e
              then (1647/1000) * ((((ArithmeticFunction.moebius e : ℝ))^2
                    * (3:ℝ)^(e.primeFactors.card))/(e:ℝ)^2) else 0) := by
        rw [Finset.sum_filter]
      rw [Finset.mul_sum, h1]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : x ≤ m
      · have h' : ¬ m < x := by omega
        simp [h, h']
      · have h' : m < x := by omega
        simp [h, h']
    rw [hb]
    calc (1647/1000) * ∑ e ∈ (Icc 1 N).filter (fun e => m < e),
            (((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card))/(e:ℝ)^2
        ≤ (1647/1000) * (2*(1 + Real.log (m:ℝ))^2/(m:ℝ)
            + 1647/1000*(2*(1 + Real.log (m:ℝ))/(m:ℝ) + 2/(m:ℝ))) :=
          mul_le_mul_of_nonneg_left (Q1_tail_le m N hm) (by norm_num)

/-- Bound of `Σ(m,N)` by the constant `2/3 + 3·(1647/1000)`. -/
private lemma Sigma_le_C0 (m N : ℕ) (hm : 1 ≤ m) :
    (∑ n ∈ (Icc 1 N).filter (fun n => m < n),
        ((ArithmeticFunction.moebius n : ℝ))^2 * (n.divisors.card : ℝ)^2 / (n:ℝ)^2)
      ≤ 2/3 + 3*(1647/1000) := by
  rcases Nat.lt_or_ge N 1 with hN | hN
  · have hem : Icc 1 N = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by omega)
    rw [hem, Finset.filter_empty, Finset.sum_empty]
    norm_num
  · have hsub : (Icc 1 N).filter (fun n => m < n) ⊆ (Icc 1 N).filter (fun n => 1 < n) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, by omega⟩
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x hx _ => by positivity)).trans ?_
    have h1mem : (1:ℕ) ∈ Icc 1 N := Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩
    have hterm : ∀ e ∈ Icc 1 N,
        (((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card)) *
            (∑ n ∈ (Icc 1 N).filter (fun n => 1 < n ∧ e ∣ n), 1/(n:ℝ)^2)
          ≤ (if e = 1 then (2/3:ℝ)
              else (1647/1000) * ((((ArithmeticFunction.moebius e : ℝ))^2
                    * (3:ℝ)^(e.primeFactors.card))/(e:ℝ)^2)) :=
      fun e he => inner_term_le_one N e (Finset.mem_Icc.mp he).1
    refine (Sigma_le_decomp 1 N).trans ((Finset.sum_le_sum hterm).trans ?_)
    have hsplit : (∑ e ∈ Icc 1 N, (if e = 1 then (2/3:ℝ)
          else (1647/1000) * ((((ArithmeticFunction.moebius e : ℝ))^2
                * (3:ℝ)^(e.primeFactors.card))/(e:ℝ)^2)))
        = 2/3 + (1647/1000) * ∑ e ∈ (Icc 1 N).erase 1,
            (((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card))/(e:ℝ)^2 := by
      have h2 : (∑ e ∈ (Icc 1 N).erase 1, (if e = 1 then (2/3:ℝ)
          else (1647/1000) * ((((ArithmeticFunction.moebius e : ℝ))^2
                * (3:ℝ)^(e.primeFactors.card))/(e:ℝ)^2)))
        = ∑ e ∈ (Icc 1 N).erase 1, (1647/1000) * ((((ArithmeticFunction.moebius e : ℝ))^2
                * (3:ℝ)^(e.primeFactors.card))/(e:ℝ)^2) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hx1 : x ≠ 1 := (Finset.mem_erase.mp hx).1
        simp [hx1]
      rw [← Finset.sum_erase_add (Icc 1 N) (fun e => if e = 1 then (2/3:ℝ)
          else (1647/1000) * ((((ArithmeticFunction.moebius e : ℝ))^2
                * (3:ℝ)^(e.primeFactors.card))/(e:ℝ)^2)) h1mem, h2, Finset.mul_sum]
      simp only [if_true]
      ring
    rw [hsplit]
    have hrest : (∑ e ∈ (Icc 1 N).erase 1,
        (((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card))/(e:ℝ)^2) ≤ 3 := by
      have hsum := sum_sqfree_three_pow_omega_div_sq_le_four N
      have hsplit2 := Finset.sum_erase_add (Icc 1 N)
        (fun e => (((ArithmeticFunction.moebius e : ℝ))^2 * (3:ℝ)^(e.primeFactors.card))/(e:ℝ)^2)
        h1mem
      have hone : (((ArithmeticFunction.moebius 1 : ℝ))^2 * (3:ℝ)^((1:ℕ).primeFactors.card))/(1:ℝ)^2 = 1 := by
        norm_num
      linarith [hsum, hsplit2, hone]
    have := mul_le_mul_of_nonneg_left hrest (by norm_num : (0:ℝ) ≤ 1647/1000)
    linarith

/-- The polynomial bound `P(M) ≤ 4M⁴` for `M ≥ 3`. -/
private lemma P_le_four_pow {M : ℝ} (hM : 3 ≤ M) :
    2*(1+M)^3 + (1647/1000)*(2*(1+M)^2 + (1647/1000)*(2*(1+M)+2)) ≤ 4*M^4 := by
  have hM0 : (0:ℝ) ≤ M := by linarith
  have h1 : 1 + M ≤ (4/3)*M := by linarith
  have h13 : (1+M)^3 ≤ ((4/3)*M)^3 := pow_le_pow_left₀ (by linarith) h1 3
  have h12 : (1+M)^2 ≤ ((4/3)*M)^2 := pow_le_pow_left₀ (by linarith) h1 2
  have hM2 : M^2 ≤ M^3/3 := by nlinarith [hM]
  have hM1 : M ≤ M^3/9 := by nlinarith [hM]
  have h1M : 1 ≤ M^3/27 := by nlinarith [hM]
  have hbound : 2*(1+M)^3 + (1647/1000)*(2*(1+M)^2 + (1647/1000)*(2*(1+M)+2)) ≤ 7.7*M^3 := by
    nlinarith [h13, h12, h1, hM2, hM1, h1M]
  have hfinal : 7.7*M^3 ≤ 4*M^4 := by nlinarith [hM, hM0]
  linarith

/-- One case of the `m ≤ 9` numerical comparison. -/
private lemma C0_case (k : ℕ) (hk : 1 ≤ k) (a : ℝ)
    (hkey : a^4 ≤ (llo (k+2))^4)
    (hnum : (2/3 + 3*(1647/1000)) * (k:ℝ) ≤ 4*a^4) :
    2/3 + 3*(1647/1000) ≤ 4*(Real.log ((k:ℝ)+2))^4/(k:ℝ) := by
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hcast : ((k+2 : ℕ) : ℝ) = (k:ℝ)+2 := by push_cast; ring
  have h4 : a^4 ≤ (Real.log ((k:ℝ)+2))^4 := by
    have h := llo_le_log (k+2) (by omega)
    rw [hcast] at h
    exact hkey.trans (pow_le_pow_left₀ (llo_nonneg (k+2)) h 4)
  rw [le_div_iff₀ hkpos]
  linarith [h4, hnum]

/-- `2/3 + 3·(1647/1000) ≤ 4 log⁴(m+2)/m` for `1 ≤ m ≤ 9`. -/
private lemma C0_le_main (m : ℕ) (hm : 1 ≤ m) (hm9 : m ≤ 9) :
    2/3 + 3*(1647/1000) ≤ 4*(Real.log ((m:ℝ)+2))^4/(m:ℝ) := by
  have hmv : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 := by
    omega
  rcases hmv with h | h | h | h | h | h | h | h | h
  · rw [h]; exact C0_case 1 (by norm_num) (1.09:ℝ)
      (by norm_num [llo, Finset.sum_Ico_eq_sum_range]) (by norm_num)
  · rw [h]; exact C0_case 2 (by norm_num) (1.35:ℝ)
      (by norm_num [llo, Finset.sum_Ico_eq_sum_range]) (by norm_num)
  · rw [h]; exact C0_case 3 (by norm_num) (1.5:ℝ)
      (by norm_num [llo, Finset.sum_Ico_eq_sum_range]) (by norm_num)
  · rw [h]; exact C0_case 4 (by norm_num) (1.6:ℝ)
      (by norm_num [llo, Finset.sum_Ico_eq_sum_range]) (by norm_num)
  · rw [h]; exact C0_case 5 (by norm_num) (1.7:ℝ)
      (by norm_num [llo, Finset.sum_Ico_eq_sum_range]) (by norm_num)
  · rw [h]; exact C0_case 6 (by norm_num) (1.8:ℝ)
      (by norm_num [llo, Finset.sum_Ico_eq_sum_range]) (by norm_num)
  · rw [h]; exact C0_case 7 (by norm_num) (1.8:ℝ)
      (by norm_num [llo, Finset.sum_Ico_eq_sum_range]) (by norm_num)
  · rw [h]; exact C0_case 8 (by norm_num) (1.85:ℝ)
      (by norm_num [llo, Finset.sum_Ico_eq_sum_range]) (by norm_num)
  · rw [h]; exact C0_case 9 (by norm_num) (1.9:ℝ)
      (by norm_num [llo, Finset.sum_Ico_eq_sum_range]) (by norm_num)

/-- One case of the `10 ≤ m ≤ 18` numerical comparison. -/
private lemma BQ_case (k : ℕ) (hk : 10 ≤ k) (a : ℝ)
    (hkey : a^4 ≤ (llo (k+2))^4)
    (hnum : 2*(1+lhi k)^3 + (1647/1000)*(2*(1+lhi k)^2 + (1647/1000)*(2*(1+lhi k)+2))
      ≤ 4*a^4) :
    2*(1 + Real.log (k:ℝ))^3/(k:ℝ)
      + (1647/1000)*(2*(1 + Real.log (k:ℝ))^2/(k:ℝ)
          + 1647/1000*(2*(1 + Real.log (k:ℝ))/(k:ℝ) + 2/(k:ℝ)))
    ≤ 4*(Real.log ((k:ℝ)+2))^4/(k:ℝ) := by
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hLnn : (0:ℝ) ≤ Real.log (k:ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  have hcast : ((k+2 : ℕ) : ℝ) = (k:ℝ)+2 := by push_cast; ring
  have hP := P_mono hLnn (log_le_lhi k (by omega))
  have h4 : a^4 ≤ (Real.log ((k:ℝ)+2))^4 := by
    have h := llo_le_log (k+2) (by omega)
    rw [hcast] at h
    exact hkey.trans (pow_le_pow_left₀ (llo_nonneg (k+2)) h 4)
  have hmul : (2*(1 + Real.log (k:ℝ))^3/(k:ℝ)
      + (1647/1000)*(2*(1 + Real.log (k:ℝ))^2/(k:ℝ)
          + 1647/1000*(2*(1 + Real.log (k:ℝ))/(k:ℝ) + 2/(k:ℝ)))) * (k:ℝ)
      = 2*(1 + Real.log (k:ℝ))^3
        + (1647/1000)*(2*(1 + Real.log (k:ℝ))^2
            + 1647/1000*(2*(1 + Real.log (k:ℝ)) + 2)) := by
    field_simp
    try ring
  rw [le_div_iff₀ hkpos, hmul]
  linarith [hP, h4, hnum]

/-- `BQ(m) ≤ 4 log⁴(m+2)/m` for `m ≥ 10`. -/
private lemma BQ_le_main (m : ℕ) (hm : 10 ≤ m) :
    2*(1 + Real.log (m:ℝ))^3/(m:ℝ)
      + (1647/1000)*(2*(1 + Real.log (m:ℝ))^2/(m:ℝ)
          + 1647/1000*(2*(1 + Real.log (m:ℝ))/(m:ℝ) + 2/(m:ℝ)))
    ≤ 4*(Real.log ((m:ℝ)+2))^4/(m:ℝ) := by
  by_cases h18 : m ≤ 18
  · have hmv : m = 10 ∨ m = 11 ∨ m = 12 ∨ m = 13 ∨ m = 14 ∨ m = 15 ∨ m = 16 ∨ m = 17
        ∨ m = 18 := by omega
    rcases hmv with h | h | h | h | h | h | h | h | h
    · rw [h]; exact BQ_case 10 (by norm_num) (2.47:ℝ)
        (by norm_num [llo, Finset.sum_Ico_eq_sum_range])
        (by norm_num [lhi, Finset.sum_Ico_eq_sum_range])
    · rw [h]; exact BQ_case 11 (by norm_num) (2.55:ℝ)
        (by norm_num [llo, Finset.sum_Ico_eq_sum_range])
        (by norm_num [lhi, Finset.sum_Ico_eq_sum_range])
    · rw [h]; exact BQ_case 12 (by norm_num) (2.62:ℝ)
        (by norm_num [llo, Finset.sum_Ico_eq_sum_range])
        (by norm_num [lhi, Finset.sum_Ico_eq_sum_range])
    · rw [h]; exact BQ_case 13 (by norm_num) (2.69:ℝ)
        (by norm_num [llo, Finset.sum_Ico_eq_sum_range])
        (by norm_num [lhi, Finset.sum_Ico_eq_sum_range])
    · rw [h]; exact BQ_case 14 (by norm_num) (2.76:ℝ)
        (by norm_num [llo, Finset.sum_Ico_eq_sum_range])
        (by norm_num [lhi, Finset.sum_Ico_eq_sum_range])
    · rw [h]; exact BQ_case 15 (by norm_num) (2.82:ℝ)
        (by norm_num [llo, Finset.sum_Ico_eq_sum_range])
        (by norm_num [lhi, Finset.sum_Ico_eq_sum_range])
    · rw [h]; exact BQ_case 16 (by norm_num) (2.87:ℝ)
        (by norm_num [llo, Finset.sum_Ico_eq_sum_range])
        (by norm_num [lhi, Finset.sum_Ico_eq_sum_range])
    · rw [h]; exact BQ_case 17 (by norm_num) (2.93:ℝ)
        (by norm_num [llo, Finset.sum_Ico_eq_sum_range])
        (by norm_num [lhi, Finset.sum_Ico_eq_sum_range])
    · rw [h]; exact BQ_case 18 (by norm_num) (2.98:ℝ)
        (by norm_num [llo, Finset.sum_Ico_eq_sum_range])
        (by norm_num [lhi, Finset.sum_Ico_eq_sum_range])
  · have hm19 : 19 ≤ m := by omega
    have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
    have hLnn : (0:ℝ) ≤ Real.log (m:ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
    have hcast : ((m+2 : ℕ) : ℝ) = (m:ℝ)+2 := by push_cast; ring
    have hM3 : (3:ℝ) ≤ Real.log ((m:ℝ)+2) := by
      rw [← hcast]
      have h1 : (21:ℝ) ≤ ((m+2 : ℕ) : ℝ) := by
        have h2 : 21 ≤ m + 2 := by omega
        exact_mod_cast h2
      exact le_trans log_21_ge_three (Real.log_le_log (by norm_num) h1)
    have hLle : Real.log (m:ℝ) ≤ Real.log ((m:ℝ)+2) := by
      rw [← hcast]
      exact Real.log_le_log (by positivity) (by linarith)
    have hP := P_mono hLnn hLle
    have hp := P_le_four_pow hM3
    have hmul : (2*(1 + Real.log (m:ℝ))^3/(m:ℝ)
        + (1647/1000)*(2*(1 + Real.log (m:ℝ))^2/(m:ℝ)
            + 1647/1000*(2*(1 + Real.log (m:ℝ))/(m:ℝ) + 2/(m:ℝ)))) * (m:ℝ)
        = 2*(1 + Real.log (m:ℝ))^3
          + (1647/1000)*(2*(1 + Real.log (m:ℝ))^2
              + 1647/1000*(2*(1 + Real.log (m:ℝ)) + 2)) := by
      field_simp
      try ring
    rw [le_div_iff₀ hmpos, hmul]
    linarith [hP, hp]
/-- `|μ(n)| = μ(n)²` over `ℝ`. -/
private lemma abs_moebius_cast (n : ℕ) :
    |((ArithmeticFunction.moebius n : ℝ))| = ((ArithmeticFunction.moebius n : ℝ))^2 := by
  have h1 : ((|ArithmeticFunction.moebius n| : ℤ) : ℝ) = ((ArithmeticFunction.moebius n : ℝ))^2 := by
    rw [ArithmeticFunction.abs_moebius, moebius_sq_cast]
    by_cases h : Squarefree n <;> simp [h]
  rw [← Int.cast_abs]
  exact h1

/-- The tail of the series `∑ μ(n) f(n)` is bounded by `C·B` whenever every partial
sum `Σ(m,N)` of the `μ²τ²/n²`-series is bounded by `B`. -/
private lemma tsum_tail_bound {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n : ℕ, 1 ≤ n → |f n| ≤ C * (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ 2)
    (hsum : Summable fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) * f n)
    (m : ℕ) (hm : 1 ≤ m) (B : ℝ)
    (hB : ∀ N : ℕ, (∑ n ∈ (Icc 1 N).filter (fun n => m < n),
        ((ArithmeticFunction.moebius n : ℝ))^2 * (n.divisors.card : ℝ)^2 / (n:ℝ)^2) ≤ B) :
    |(∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) * f n)
      - ∑ n ∈ Finset.range (m + 1), (ArithmeticFunction.moebius n : ℝ) * f n| ≤ C * B := by
  have hF : Summable (fun n : ℕ => if n ≤ m then (ArithmeticFunction.moebius n : ℝ) * f n else 0) := by
    refine summable_of_ne_finset_zero (s := Finset.range (m+1)) (fun b hb => ?_)
    have hb' : ¬ b < m + 1 := fun h => hb (Finset.mem_range.mpr h)
    simp only [if_neg (by omega : ¬ b ≤ m)]
  have hFsum : ∑' n : ℕ, (if n ≤ m then (ArithmeticFunction.moebius n : ℝ) * f n else 0)
      = ∑ n ∈ Finset.range (m + 1), (ArithmeticFunction.moebius n : ℝ) * f n := by
    have h1 : ∑' n : ℕ, (if n ≤ m then (ArithmeticFunction.moebius n : ℝ) * f n else 0)
        = ∑ n ∈ Finset.range (m+1),
            (if n ≤ m then (ArithmeticFunction.moebius n : ℝ) * f n else 0) :=
      tsum_eq_sum (s := Finset.range (m+1)) (fun b hb => by
        have hb' : ¬ b < m + 1 := fun h => hb (Finset.mem_range.mpr h)
        simp only [if_neg (by omega : ¬ b ≤ m)])
    rw [h1]
    apply Finset.sum_congr rfl
    intro n hn
    rw [if_pos (by have h := Finset.mem_range.mp hn; omega)]
  have hTsum : Summable (fun n : ℕ => if m < n then (ArithmeticFunction.moebius n : ℝ) * f n else 0) := by
    have h := hsum.sub hF
    refine h.congr (fun n => ?_)
    by_cases hn : m < n
    · rw [if_pos hn, if_neg (by omega : ¬ n ≤ m)]
      ring
    · rw [if_neg hn, if_pos (by omega : n ≤ m)]
      ring
  have hkey : ∑' n : ℕ, (if m < n then (ArithmeticFunction.moebius n : ℝ) * f n else 0)
      = (∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) * f n)
        - ∑ n ∈ Finset.range (m + 1), (ArithmeticFunction.moebius n : ℝ) * f n := by
    have h1 := hsum.tsum_sub hF
    rw [hFsum] at h1
    rw [← h1]
    apply tsum_congr
    intro n
    by_cases hn : m < n
    · rw [if_pos hn, if_neg (by omega : ¬ n ≤ m)]
      ring
    · rw [if_neg hn, if_pos (by omega : n ≤ m)]
      ring
  rw [← hkey]
  have hpartial : ∀ N : ℕ,
      |∑ n ∈ Finset.range N, (if m < n then (ArithmeticFunction.moebius n : ℝ) * f n else 0)|
        ≤ C * B := by
    intro N
    have h1 : (∑ n ∈ Finset.range N,
          (if m < n then (ArithmeticFunction.moebius n : ℝ) * f n else 0))
        = ∑ n ∈ (Finset.range N).filter (fun n => m < n),
            (ArithmeticFunction.moebius n : ℝ) * f n := by
      rw [Finset.sum_filter]
    rw [h1]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h2 : (∑ n ∈ (Finset.range N).filter (fun n => m < n),
          |(ArithmeticFunction.moebius n : ℝ) * f n|)
        ≤ ∑ n ∈ (Finset.range N).filter (fun n => m < n),
            C * (((ArithmeticFunction.moebius n : ℝ))^2 * (n.divisors.card : ℝ)^2 / (n:ℝ)^2) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn2 : m < n := (Finset.mem_filter.mp hn).2
      have hn1 : 1 ≤ n := by omega
      have hstep : |(ArithmeticFunction.moebius n : ℝ) * f n|
          ≤ ((ArithmeticFunction.moebius n : ℝ))^2
              * (C * (n.divisors.card : ℝ)^2 / (n:ℝ)^2) := by
        rw [abs_mul, abs_moebius_cast n]
        exact mul_le_mul_of_nonneg_left (hf n hn1) (by positivity)
      calc |(ArithmeticFunction.moebius n : ℝ) * f n|
          ≤ ((ArithmeticFunction.moebius n : ℝ))^2
              * (C * (n.divisors.card : ℝ)^2 / (n:ℝ)^2) := hstep
        _ = C * (((ArithmeticFunction.moebius n : ℝ))^2
              * (n.divisors.card : ℝ)^2 / (n:ℝ)^2) := by ring
    refine h2.trans ?_
    have hsub : (Finset.range N).filter (fun n => m < n) ⊆ (Icc 1 N).filter (fun n => m < n) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      have hxN : x < N := Finset.mem_range.mp hx.1
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hx.2⟩
    have h3 : (∑ n ∈ (Finset.range N).filter (fun n => m < n),
          (((ArithmeticFunction.moebius n : ℝ))^2 * (n.divisors.card : ℝ)^2 / (n:ℝ)^2))
        ≤ ∑ n ∈ (Icc 1 N).filter (fun n => m < n),
          (((ArithmeticFunction.moebius n : ℝ))^2 * (n.divisors.card : ℝ)^2 / (n:ℝ)^2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x hx _ => by positivity)
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (h3.trans (hB N)) hC
  have htend : Filter.Tendsto (fun N : ℕ =>
        |∑ n ∈ Finset.range N, (if m < n then (ArithmeticFunction.moebius n : ℝ) * f n else 0)|)
      Filter.atTop
      (𝓝 |∑' n : ℕ, (if m < n then (ArithmeticFunction.moebius n : ℝ) * f n else 0)|) :=
    hTsum.hasSum.tendsto_sum_nat.abs
  exact le_of_tendsto_of_tendsto' htend tendsto_const_nhds hpartial

theorem abs_tsum_moebius_mul_sub_sum_range_tau_sq_le {f : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ n : ℕ, 1 ≤ n → |f n| ≤ C * (n.divisors.card : ℝ) ^ 2 / (n : ℝ) ^ 2)
    (hsum : Summable fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) * f n)
    (m : ℕ) (hm : 1 ≤ m) :
    |(∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) * f n)
      - ∑ n ∈ Finset.range (m + 1), (ArithmeticFunction.moebius n : ℝ) * f n|
      ≤ 4 * C * (Real.log ((m : ℝ) + 2)) ^ 4 / (m : ℝ) := by
  have hSle : ∀ N : ℕ, (∑ n ∈ (Icc 1 N).filter (fun n => m < n),
      ((ArithmeticFunction.moebius n : ℝ))^2 * (n.divisors.card : ℝ)^2 / (n:ℝ)^2)
        ≤ 4*(Real.log ((m:ℝ)+2))^4/(m:ℝ) := by
    intro N
    rcases Nat.lt_or_ge 9 m with h9 | h9
    · exact (Sigma_le_BQ m N hm).trans (BQ_le_main m (by omega))
    · exact (Sigma_le_C0 m N hm).trans (C0_le_main m hm (by omega))
  have hmain := tsum_tail_bound hC hf hsum m hm (4*(Real.log ((m:ℝ)+2))^4/(m:ℝ)) hSle
  calc |(∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) * f n)
        - ∑ n ∈ Finset.range (m + 1), (ArithmeticFunction.moebius n : ℝ) * f n|
      ≤ C * (4*(Real.log ((m:ℝ)+2))^4/(m:ℝ)) := hmain
    _ = 4 * C * (Real.log ((m:ℝ)+2))^4 / (m:ℝ) := by ring

end

end Commons.NumberTheory.Moebius