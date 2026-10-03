/-
  Companion paper, §9: **the density-tail bound for the Friedlander–Iwaniec sequence**.

  `S9p.gtail_le_of_hyp` bounds `gtail g g̃ d m` but only under the hypothesis
  `|g(ν²)| ≤ C/ν²` for a *constant* `C` — which is FALSE for `g = FIg` (the local density of
  `X²+Y⁴`), since `FIg(p^{2k}) ≍ p^{−k}` is not bounded by `C/p^{2k}` along prime powers.  What is
  true (and all that is needed) is the `τ`-weighted bound

      `|FIg (ν²)| ≤ τ(ν)²/ν²`,   and   `|FIg ([ν²,d])| ≤ τ(d)²·3^{ω(d)}·τ(ν)²/ν²`,

  which is summable against `1/ν²` with the `τ²` weight.  This file proves the corresponding
  version of the tail bound, using the commons lemma
  `abs_tsum_moebius_mul_sub_sum_range_tau_sq_le`.

  The Euler-product input (9.8)/(9.9) is taken from the commons
  (`EulerProduct.tsum_moebius_lcm_eq_not_dvd`) and `S9k.Gprod_eq_tsum` / `S9m.Gprod_eq_prod_filter_mul`.
-/
import Mathlib
import Submission.ASP.S36
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Prime.Defs
import Submission.ASP.S9l
import Submission.ASP.S9k
import Submission.ASP.S9m
import Submission.ASP.S9n
import Submission.Commons.NumberTheory.EulerProduct.tsum_moebius_lcm_eq_not_dvd
import Submission.Commons.NumberTheory.Moebius.abs_tsum_moebius_mul_sub_sum_range_tau_sq_le
import Submission.Commons.NumberTheory.Divisors.sum_tau_pow_div_sq_tail_le

set_option maxHeartbeats 1600000

namespace Submission.ASP

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

/-! ### `∑_n τ(n)^k/n²` converges -/

/-- `∑_n τ(n)^k/n²` converges (for every `k`). -/
lemma summable_tau_pow_div_sq (k : ℕ) :
    Summable (fun n : ℕ => ((n.divisors.card : ℝ)) ^ k / (n : ℝ) ^ 2) := by
  obtain ⟨C, hC, htail⟩ := Commons.NumberTheory.Divisors.sum_tau_pow_div_sq_tail_le k
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  refine summable_of_sum_range_le (f := fun n : ℕ => ((n.divisors.card : ℝ)) ^ k / (n : ℝ) ^ 2)
    (fun n => div_nonneg (by positivity) (by positivity)) (c := 1 + C * (Real.log 3) ^ ((2 : ℝ) ^ k)) ?_
  intro N
  have hsub : Finset.range N ⊆
      insert (0:ℕ) (insert (1:ℕ) ((Finset.Icc 1 N).filter (fun n => 1 < n))) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rcases Nat.eq_zero_or_pos i with h0 | h1
    · rw [h0]; exact Finset.mem_insert_self _ _
    · rcases Nat.lt_or_ge 1 i with h | h
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, by omega⟩, h⟩))
      · have : i = 1 := by omega
        rw [this]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hstep := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun n : ℕ => ((n.divisors.card : ℝ)) ^ k / (n : ℝ) ^ 2) hsub
    (fun i _ _ => div_nonneg (by positivity) (by positivity))
  rw [Finset.sum_insert (by simp : (0:ℕ) ∉ insert (1:ℕ) ((Finset.Icc 1 N).filter (fun n => 1 < n))),
      Finset.sum_insert (by simp : (1:ℕ) ∉ (Finset.Icc 1 N).filter (fun n => 1 < n))] at hstep
  refine le_trans hstep ?_
  have hf0 : ((0 : ℕ).divisors.card : ℝ) ^ k / ((0 : ℕ) : ℝ) ^ 2 = 0 := by simp
  have hf1 : ((1 : ℕ).divisors.card : ℝ) ^ k / ((1 : ℕ) : ℝ) ^ 2 = 1 := by simp
  rw [hf0, hf1, zero_add]
  have htail1 := htail 1 N (le_refl 1)
  rw [show (((1 : ℕ) : ℝ) + 2) = 3 by norm_num] at htail1
  simp only [Nat.cast_one, div_one] at htail1
  have hCnn : 0 ≤ C * (Real.log 3) ^ ((2 : ℝ) ^ k) :=
    mul_nonneg hC.le (Real.rpow_nonneg hlog3.le _)
  linarith

/-- The `τ²`-weighted series with a Möbius factor is summable: it suffices to control the summand
on the squarefree numbers, since `μ` vanishes elsewhere. -/
lemma summable_moebius_mul_of_tau_sq {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ n : ℕ, Squarefree n → 1 ≤ n →
      |f n| ≤ C * ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ 2) :
    Summable (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) * f n) := by
  set C' : ℝ := max C 0 with hC'
  refine Summable.of_norm_bounded
    (g := fun n : ℕ => C' * (((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ 2))
    ((summable_tau_pow_div_sq 2).mul_left C') (fun n => ?_)
  rw [Real.norm_eq_abs]
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · rw [h0]; simp
  · by_cases hsf : Squarefree n
    · have hmu : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hfnn : 0 ≤ ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ 2 := by positivity
      calc |(ArithmeticFunction.moebius n : ℝ) * f n|
          = |(ArithmeticFunction.moebius n : ℝ)| * |f n| := abs_mul _ _
        _ ≤ 1 * (C * (((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ 2)) := by
            refine mul_le_mul hmu ?_ (abs_nonneg _) (by norm_num)
            rw [← mul_div_assoc]
            exact hf n hsf h0
        _ = C * (((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ 2) := one_mul _
        _ ≤ C' * (((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hfnn
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
      simp only [Int.cast_zero, zero_mul, abs_zero]
      exact mul_nonneg (le_max_right _ _) (div_nonneg (by positivity) (by positivity))

/-! ### The `τ²`-pointwise bound for `FIg` and `FIg ∘ lcm` -/

/-- `|FIg (p²)| ≤ 3/p²`. -/
lemma FIg_prime_sq_abs_le (p : ℕ) (hp : p.Prime) : |FIg (p ^ 2)| ≤ 3 / (p : ℝ) ^ 2 := by
  rw [abs_of_nonneg (FIg_nonneg _)]
  exact FIg_prime_sq_le p hp

/-- For squarefree `ν ≥ 1`, `FIg (ν²) ≤ τ(ν)²/ν²`. -/
lemma FIg_sq_le_tau_sq_div (ν : ℕ) (hν : Squarefree ν) :
    FIg (ν ^ 2) ≤ ((ν.divisors.card : ℝ)) ^ 2 / (ν : ℝ) ^ 2 := by
  have hν0 : 0 < ν := Nat.pos_of_ne_zero hν.ne_zero
  have h1 := FIg_sq_le_card_primeFactors ν hν
  have h2 := three_pow_card_primeFactors_le_card_divisors_sq ν hν0
  refine le_trans h1 (div_le_div_of_nonneg_right h2 (by positivity))

/-- For squarefree `d` and squarefree `ν ≥ 1`,
`FIg ([ν²,d]) ≤ 3^{ω(d)}·τ(ν)²/ν²`. -/
lemma FIg_lcm_le_tau_sq (ν d : ℕ) (hν1 : 1 ≤ ν) (hν : Squarefree ν) (hd : Squarefree d) :
    FIg (Nat.lcm (ν ^ 2) d) ≤ (3 : ℝ) ^ (d.primeFactors.card)
      * (((ν.divisors.card : ℝ)) ^ 2 / (ν : ℝ) ^ 2) := by
  by_cases hd1 : d = 0
  · rw [hd1] at hd; exact absurd hd not_squarefree_zero
  have hd1' : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd1
  have h := FIg_lcm_sq_le ν d hν1 hd hd1'
  have hsq := FIg_sq_le_tau_sq_div ν hν
  have hw : (0 : ℝ) ≤ ((ν.divisors.card : ℝ)) ^ 2 / (ν : ℝ) ^ 2 := by positivity
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hgcd : (Nat.gcd d ν : ℝ) / (d : ℝ) ≤ 1 := by
    rw [div_le_one hdpos]
    exact_mod_cast Nat.gcd_le_left ν (by omega)
  calc FIg (Nat.lcm (ν ^ 2) d)
      ≤ FIg (ν ^ 2) * ((3 : ℝ) ^ (d.primeFactors.card) * (Nat.gcd d ν : ℝ) / (d : ℝ)) := h
    _ ≤ (((ν.divisors.card : ℝ)) ^ 2 / (ν : ℝ) ^ 2)
          * ((3 : ℝ) ^ (d.primeFactors.card) * 1) := by
        have h3nn : (0 : ℝ) ≤ (3 : ℝ) ^ (d.primeFactors.card) := by positivity
        have hgc : 0 ≤ (3 : ℝ) ^ (d.primeFactors.card) * (Nat.gcd d ν : ℝ) / (d : ℝ) :=
          div_nonneg (mul_nonneg h3nn (Nat.cast_nonneg _)) hdpos.le
        have hstep2 : (3 : ℝ) ^ (d.primeFactors.card) * ((Nat.gcd d ν : ℝ) / (d : ℝ))
            ≤ (3 : ℝ) ^ (d.primeFactors.card) * 1 :=
          mul_le_mul_of_nonneg_left hgcd h3nn
        have hstep2' : (3 : ℝ) ^ (d.primeFactors.card) * (Nat.gcd d ν : ℝ) / (d : ℝ)
            ≤ (3 : ℝ) ^ (d.primeFactors.card) * 1 := by
          rw [mul_div_assoc]; exact hstep2
        exact mul_le_mul hsq hstep2' hgc hw
    _ = (3 : ℝ) ^ (d.primeFactors.card) * (((ν.divisors.card : ℝ)) ^ 2 / (ν : ℝ) ^ 2) := by ring

/-! ### Splitting the Euler product at the primes dividing `d` -/

/-- `∏'_{p prime}(if p ∈ S then 1 else 1 − g p²) = ∏'_{p prime, p ∉ S}(1 − g p²)`. -/
lemma tprod_prime_filter_eq (g : ℕ → ℝ) (S : Finset ℕ) :
    (∏' p : {p : ℕ // p.Prime}, (if (p : ℕ) ∈ S then (1 : ℝ) else 1 - g ((p : ℕ) ^ 2)))
      = ∏' p : {p : ℕ // p.Prime ∧ p ∉ S}, (1 - g ((p : ℕ) ^ 2)) := by
  rw [show (∏' p : {p : ℕ // p.Prime}, (if (p : ℕ) ∈ S then (1 : ℝ) else 1 - g ((p : ℕ) ^ 2)))
        = ∏' x : ℕ, Set.mulIndicator {x : ℕ | x.Prime}
            (fun x => if x ∈ S then (1 : ℝ) else 1 - g (x ^ 2)) x from
      tprod_subtype {x : ℕ | x.Prime} (fun x => if x ∈ S then (1 : ℝ) else 1 - g (x ^ 2)),
      show (∏' p : {p : ℕ // p.Prime ∧ p ∉ S}, (1 - g ((p : ℕ) ^ 2)))
        = ∏' x : ℕ, Set.mulIndicator {x : ℕ | x.Prime ∧ x ∉ S}
            (fun x => 1 - g (x ^ 2)) x from
      tprod_subtype {x : ℕ | x.Prime ∧ x ∉ S} (fun x => 1 - g (x ^ 2))]
  refine tprod_congr (fun x => ?_)
  by_cases hx : x.Prime
  · by_cases hS : x ∈ S
    · rw [Set.mulIndicator_of_mem (by simpa using hx),
        Set.mulIndicator_of_notMem (by simp [hS]), if_pos hS]
    · rw [Set.mulIndicator_of_mem (by simpa using hx),
        Set.mulIndicator_of_mem (by simp [hx, hS]), if_neg hS]
  · rw [Set.mulIndicator_of_notMem (by simpa using hx),
      Set.mulIndicator_of_notMem (by simp [hx])]

/-- The Euler product split at the primeness of `S`: `G = (∏_{p ∈ S}(1 − g p²))·∏'_{p ∉ S}(1 − g p²)`
(the second product being over the primes not in `S`). -/
lemma Gprod_eq_prod_mul_tprod_notMem (g : ℕ → ℝ) (S : Finset ℕ) {C : ℝ} (hC : 0 < C)
    (hbd : ∀ p : ℕ, p.Prime → |g (p ^ 2)| ≤ C / (p : ℝ) ^ 2) :
    Gprod g = (∏ p ∈ S.filter Nat.Prime, (1 - g (p ^ 2)))
      * ∏' p : {p : ℕ // p.Prime ∧ p ∉ S}, (1 - g ((p : ℕ) ^ 2)) := by
  rw [Gprod_eq_prod_filter_mul g S hC hbd, tprod_prime_filter_eq]

/-! ### The density `g̃` as an explicit product, and the Euler-factor factorisation -/

/-- `FIgtil d = ∏_{p ∣ d}(FIg p − FIg p²)/(1 − FIg p²)` for squarefree `d`. -/
lemma FIgtil_eq_prod (d : ℕ) (hd : Squarefree d) :
    FIgtil d = ∏ p ∈ d.primeFactors, (FIg p - FIg (p ^ 2)) / (1 - FIg (p ^ 2)) := by
  rw [FIgtil, if_pos hd]
  exact Finset.prod_congr rfl (fun p _ => rfl)

/-- `∏_{p ∣ d}(1 − FIg p²) > 0`. -/
lemma FI_prod_one_sub_pos (d : ℕ) : 0 < ∏ p ∈ d.primeFactors, (1 - FIg (p ^ 2)) := by
  refine Finset.prod_pos (fun p hp => ?_)
  have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp'.two_le
  have hb := FI_sq_pow_bound p 1 hp' le_rfl
  rw [mul_one, abs_of_nonneg (FIg_nonneg _)] at hb
  have h4 : (4 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
  have h34 : 3 / (p : ℝ) ^ 2 ≤ 3 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  linarith [le_trans hb h34]

/-! ### The Möbius sum of the `gtail` summand vanishes -/

/-- The two Euler-product identities (9.8) and (9.9) combine with the split of `G` to show that the
total mass of the `gtail` summand is zero. -/
theorem FI_tsum_gtail_eq_zero (d : ℕ) (hd : Squarefree d) :
    (∑' ν : ℕ, (ArithmeticFunction.moebius ν : ℝ)
      * (FIg (Nat.lcm (ν ^ 2) d) - FIgtil d * FIg (ν ^ 2))) = 0 := by
  classical
  set P : ℝ := ∏' p : {p : ℕ // p.Prime ∧ p ∉ d.primeFactors}, (1 - FIg ((p : ℕ) ^ 2)) with hP
  have hA : (∑' ν : ℕ, (ArithmeticFunction.moebius ν : ℝ) * FIg (Nat.lcm (ν ^ 2) d))
      = (∏ p ∈ d.primeFactors, (FIg p - FIg (p ^ 2))) * P := by
    rw [hP]
    exact Commons.NumberTheory.EulerProduct.tsum_moebius_lcm_eq_not_dvd
      (g := FIg) (fun m n hmn => FI_gdens_mul hmn) FI_gdens_one (by norm_num : (0 : ℝ) ≤ 3)
      (fun p _ => FIg_nonneg _) (fun p hp => FIg_prime_sq_le p hp) d hd
  have hB : (∑' ν : ℕ, (ArithmeticFunction.moebius ν : ℝ) * FIg (ν ^ 2)) = Gprod FIg :=
    FI_Gprod_eq_tsum.symm
  have hC : Gprod FIg = (∏ p ∈ d.primeFactors, (1 - FIg (p ^ 2))) * P := by
    rw [hP, Gprod_eq_prod_mul_tprod_notMem (g := FIg) (S := d.primeFactors) (C := 3)
      (by norm_num) (fun p hp => FIg_prime_sq_abs_le p hp)]
    rw [Finset.filter_true_of_mem (fun p hp => Nat.prime_of_mem_primeFactors hp)]
  have hFIgtil : FIgtil d
      = (∏ p ∈ d.primeFactors, (FIg p - FIg (p ^ 2)))
        / (∏ p ∈ d.primeFactors, (1 - FIg (p ^ 2))) := by
    rw [FIgtil_eq_prod d hd, Finset.prod_div_distrib]
  have hkey : (∑' ν : ℕ, (ArithmeticFunction.moebius ν : ℝ) * FIg (Nat.lcm (ν ^ 2) d))
      = FIgtil d * (∑' ν : ℕ, (ArithmeticFunction.moebius ν : ℝ) * FIg (ν ^ 2)) := by
    rw [hA, hB, hC, hFIgtil, ← mul_assoc,
      div_mul_cancel₀ _ (ne_of_gt (FI_prod_one_sub_pos d))]
  have hsum1 : Summable
      (fun ν : ℕ => (ArithmeticFunction.moebius ν : ℝ) * FIg (Nat.lcm (ν ^ 2) d)) :=
    summable_moebius_mul_of_tau_sq (C := (3 : ℝ) ^ (d.primeFactors.card))
      (fun n hsf hn => by
        rw [abs_of_nonneg (FIg_nonneg _), mul_div_assoc]
        exact FIg_lcm_le_tau_sq n d hn hsf hd)
  have hsum2 : Summable
      (fun ν : ℕ => (ArithmeticFunction.moebius ν : ℝ) * (FIgtil d * FIg (ν ^ 2))) :=
    Summable.congr ((summable_moebius_mul_of_tau_sq (C := 1) (fun n hsf hn => by
      rw [abs_of_nonneg (FIg_nonneg _), one_mul]
      exact FIg_sq_le_tau_sq_div n hsf)).mul_left (FIgtil d))
      (fun ν => by ring)
  have hg_eq : (∑' ν : ℕ, (ArithmeticFunction.moebius ν : ℝ) * (FIgtil d * FIg (ν ^ 2)))
      = FIgtil d * (∑' ν : ℕ, (ArithmeticFunction.moebius ν : ℝ) * FIg (ν ^ 2)) := by
    rw [show (∑' ν : ℕ, (ArithmeticFunction.moebius ν : ℝ) * (FIgtil d * FIg (ν ^ 2)))
        = ∑' ν : ℕ, FIgtil d * ((ArithmeticFunction.moebius ν : ℝ) * FIg (ν ^ 2)) from
      tsum_congr (fun ν => by ring)]
    rw [tsum_mul_left]
  rw [show (∑' ν : ℕ, (ArithmeticFunction.moebius ν : ℝ)
        * (FIg (Nat.lcm (ν ^ 2) d) - FIgtil d * FIg (ν ^ 2)))
      = ∑' ν : ℕ, ((ArithmeticFunction.moebius ν : ℝ) * FIg (Nat.lcm (ν ^ 2) d)
          - (ArithmeticFunction.moebius ν : ℝ) * (FIgtil d * FIg (ν ^ 2))) from
    tsum_congr (fun ν => by ring)]
  rw [Summable.tsum_sub hsum1 hsum2, hkey, hg_eq]
  ring

/-! ### The per-modulus density-tail bound -/

/-- The `gtail` summand, restricted to the squarefree numbers (harmless, since `μ` vanishes
elsewhere) so that the `τ²`-weighted comparison series is summable. -/
def gtailSummand (d : ℕ) (n : ℕ) : ℝ :=
  if Squarefree n then FIg (Nat.lcm (n ^ 2) d) - FIgtil d * FIg (n ^ 2) else 0

lemma abs_gtailSummand_le (d n : ℕ) (hd : Squarefree d) (hn : 1 ≤ n) (hsf : Squarefree n) :
    |gtailSummand d n| ≤ ((3 : ℝ) ^ (d.primeFactors.card) + FIgtil d)
      * ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ 2 := by
  rw [gtailSummand, if_pos hsf, mul_div_assoc]
  have h1 := FIg_lcm_le_tau_sq n d hn hsf hd
  have h2 := FIg_sq_le_tau_sq_div n hsf
  have hwnn : (0 : ℝ) ≤ ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ 2 := by positivity
  have hCl : (0 : ℝ) ≤ (3 : ℝ) ^ (d.primeFactors.card) := by positivity
  have hFnn : 0 ≤ FIgtil d := FIgtil_nonneg d
  have hFw : FIgtil d * FIg (n ^ 2) ≤ FIgtil d * (((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left h2 hFnn
  have hlcmnn : 0 ≤ FIg (Nat.lcm (n ^ 2) d) := FIg_nonneg _
  have hFnn' : (0 : ℝ) ≤ FIgtil d * FIg (n ^ 2) := mul_nonneg hFnn (FIg_nonneg _)
  rw [abs_sub_le_iff]
  constructor
  · calc FIg (Nat.lcm (n ^ 2) d) - FIgtil d * FIg (n ^ 2)
        ≤ (3 : ℝ) ^ (d.primeFactors.card) * (((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ 2)
          + FIgtil d * (((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ 2) := by
          have : -(FIgtil d * FIg (n ^ 2))
              ≤ FIgtil d * (((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ 2) := by linarith
          linarith
      _ = ((3 : ℝ) ^ (d.primeFactors.card) + FIgtil d)
          * (((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ 2) := by ring
  · calc FIgtil d * FIg (n ^ 2) - FIg (Nat.lcm (n ^ 2) d)
        ≤ FIgtil d * (((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ 2) := by linarith
      _ ≤ ((3 : ℝ) ^ (d.primeFactors.card) + FIgtil d)
          * (((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCl) hwnn

/-- **The density-tail bound for `X²+Y⁴`**: for squarefree `d`,
`|gtail(d,m)| ≤ 4(3^{ω(d)} + g̃(d))·(log(m+2))^4/m`. -/
theorem FI_gtail_le (d m : ℕ) (hd : Squarefree d) (hm : 1 ≤ m) :
    |gtail FIg FIgtil d m| ≤ 4 * ((3 : ℝ) ^ (d.primeFactors.card) + FIgtil d)
      * (Real.log ((m : ℝ) + 2)) ^ 4 / (m : ℝ) := by
  classical
  have hC : (0 : ℝ) ≤ (3 : ℝ) ^ (d.primeFactors.card) + FIgtil d := by
    have := FIgtil_nonneg d; positivity
  have hf : ∀ n : ℕ, 1 ≤ n → |gtailSummand d n|
      ≤ ((3 : ℝ) ^ (d.primeFactors.card) + FIgtil d)
        * ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ 2 := by
    intro n hn
    by_cases hsf : Squarefree n
    · exact abs_gtailSummand_le d n hd hn hsf
    · rw [gtailSummand, if_neg hsf, abs_zero]
      exact div_nonneg (mul_nonneg hC (by positivity)) (by positivity)
  have hsum : Summable (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) * gtailSummand d n) :=
    summable_moebius_mul_of_tau_sq (C := (3 : ℝ) ^ (d.primeFactors.card) + FIgtil d)
      (fun n hsf hn => abs_gtailSummand_le d n hd hn hsf)
  have htail := Commons.NumberTheory.Moebius.abs_tsum_moebius_mul_sub_sum_range_tau_sq_le
    (f := gtailSummand d) (C := (3 : ℝ) ^ (d.primeFactors.card) + FIgtil d) hC hf hsum m hm
  have hpt : ∀ n : ℕ, (ArithmeticFunction.moebius n : ℝ) * gtailSummand d n
      = (ArithmeticFunction.moebius n : ℝ)
        * (FIg (Nat.lcm (n ^ 2) d) - FIgtil d * FIg (n ^ 2)) := by
    intro n
    rw [gtailSummand]
    by_cases h : Squarefree n
    · rw [if_pos h]
    · rw [if_neg h, ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
      simp
  have hzero : (∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) * gtailSummand d n) = 0 := by
    rw [tsum_congr hpt]
    exact FI_tsum_gtail_eq_zero d hd
  have hpartial : (∑ n ∈ Finset.range (m + 1),
      (ArithmeticFunction.moebius n : ℝ) * gtailSummand d n) = gtail FIg FIgtil d m := by
    rw [gtail_eq_sum_range]
    exact Finset.sum_congr rfl (fun n _ => hpt n)
  rw [hzero, hpartial, zero_sub, abs_neg] at htail
  exact htail

/-! ### Summing the density-tail bound over the squarefree moduli -/

/-- `log 3 ≥ 1`. -/
lemma one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  have h4 : Real.exp 1 ≤ (3 : ℝ) := le_of_lt Real.exp_one_lt_three
  have h5 := Real.log_le_log (Real.exp_pos 1) h4
  rwa [Real.log_exp] at h5

/-- `∑_{d ≤ D, ♭}(3^{ω(d)} + g̃(d)) ≪ D·(log(D+2))^A`. -/
lemma sum_sqfree_three_pow_add_FIgtil_le :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ D : ℕ,
      (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        ((3 : ℝ) ^ (d.primeFactors.card) + FIgtil d))
        ≤ C * (D : ℝ) * (Real.log ((D : ℝ) + 2)) ^ A := by
  obtain ⟨C2, hC2, h2⟩ := Commons.NumberTheory.DivisorSum.sum_tau_pow_le 2
  obtain ⟨C3, K, hC3, hK, h3⟩ := sum_FIgtil_le
  refine ⟨4 * (max C2 C3 + 1), max 3 K + 1, by positivity, by positivity, fun D => ?_⟩
  rcases Nat.eq_zero_or_pos D with hD0 | hD
  · subst hD0; simp
  rcases Nat.lt_or_ge D 2 with hD2 | hD2
  · -- small `D`: the sum is `≤ 2` and the right-hand side is `≥ 4·(log 3)^A ≥ 1`
    have hD1 : D = 1 := by omega
    subst hD1
    have hsum_le : (∑ d ∈ (Finset.Icc 1 1).filter Squarefree,
        ((3 : ℝ) ^ (d.primeFactors.card) + FIgtil d)) ≤ 2 := by
      rw [Finset.Icc_self,
        Finset.filter_true_of_mem (fun x hx => by
          rw [Finset.mem_singleton.mp hx]; exact squarefree_one),
        Finset.sum_singleton, Nat.primeFactors_one, Finset.card_empty, pow_zero, FIgtil_one]
      norm_num
    have hA1 : (1 : ℝ) ≤ (Real.log 3) ^ (max 3 K + 1) :=
      Real.one_le_rpow one_le_log_three (by positivity)
    have hC1 : (4 : ℝ) ≤ 4 * (max C2 C3 + 1) := by
      have h := le_max_left C2 C3
      linarith [hC2.le]
    refine le_trans hsum_le ?_
    have hlog3 : Real.log (((1 : ℕ) : ℝ) + 2) = Real.log 3 := by norm_num
    rw [hlog3, Nat.cast_one, mul_one]
    nlinarith [hA1, hC1]
  · -- main case `D ≥ 2`
    have hD1 : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    have hlog : (1 : ℝ) ≤ Real.log ((D : ℝ) + 2) := by
      have h3' : (3 : ℝ) ≤ (D : ℝ) + 2 := by linarith
      exact le_trans one_le_log_three (Real.log_le_log (by norm_num) h3')
    have hlog0 : (0 : ℝ) < Real.log ((D : ℝ) + 2) := lt_of_lt_of_le zero_lt_one hlog
    rw [Finset.sum_add_distrib]
    -- the `3^{ω}` part
    have hb1 : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, (3 : ℝ) ^ (d.primeFactors.card))
        ≤ C2 * (D : ℝ) * (Real.log ((D : ℝ) + 2)) ^ (2 ^ 2 - 1 : ℕ) := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => by positivity)) ?_
      refine le_trans (Finset.sum_le_sum (fun d hd =>
        three_pow_card_primeFactors_le_card_divisors_sq d
          (by have := (Finset.mem_Icc.mp hd).1; omega))) ?_
      refine le_trans (h2 D hD) ?_
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC2.le (Nat.cast_nonneg D))
      refine pow_le_pow_left₀ (Real.log_nonneg (by linarith)) ?_ _
      exact Real.log_le_log (by linarith) (by linarith)
    -- the `g̃` part
    have hb2 : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, FIgtil d)
        ≤ C3 * (Real.log ((D : ℝ) + 2)) ^ K := by
      have h3' := h3 D hD2
      refine le_trans h3' ?_
      refine mul_le_mul_of_nonneg_left ?_ hC3.le
      exact Real.rpow_le_rpow (Real.log_nonneg (by exact_mod_cast hD))
        (Real.log_le_log (by linarith) (by linarith)) hK
    -- combine
    have hb2' : C3 * (Real.log ((D : ℝ) + 2)) ^ K
        ≤ C3 * (D : ℝ) * (Real.log ((D : ℝ) + 2)) ^ (max 3 K + 1) := by
      have hK' : K ≤ max 3 K + 1 := by
        have : K ≤ max 3 K := le_max_right _ _
        linarith
      have h2' : (Real.log ((D : ℝ) + 2)) ^ K ≤ (Real.log ((D : ℝ) + 2)) ^ (max 3 K + 1) :=
        Real.rpow_le_rpow_of_exponent_le hlog hK'
      calc C3 * (Real.log ((D : ℝ) + 2)) ^ K
          ≤ C3 * (Real.log ((D : ℝ) + 2)) ^ (max 3 K + 1) :=
            mul_le_mul_of_nonneg_left h2' hC3.le
        _ ≤ C3 * ((D : ℝ) * (Real.log ((D : ℝ) + 2)) ^ (max 3 K + 1)) := by
            refine mul_le_mul_of_nonneg_left ?_ hC3.le
            calc (Real.log ((D : ℝ) + 2)) ^ (max 3 K + 1)
                = 1 * (Real.log ((D : ℝ) + 2)) ^ (max 3 K + 1) := (one_mul _).symm
              _ ≤ (D : ℝ) * (Real.log ((D : ℝ) + 2)) ^ (max 3 K + 1) :=
                  mul_le_mul_of_nonneg_right hD1 (Real.rpow_nonneg hlog0.le _)
        _ = C3 * (D : ℝ) * (Real.log ((D : ℝ) + 2)) ^ (max 3 K + 1) := by ring
    have hb1' : C2 * (D : ℝ) * (Real.log ((D : ℝ) + 2)) ^ (2 ^ 2 - 1 : ℕ)
        ≤ C2 * (D : ℝ) * (Real.log ((D : ℝ) + 2)) ^ (max 3 K + 1) := by
      have h3' : (((2 ^ 2 - 1 : ℕ)) : ℝ) ≤ max 3 K + 1 := by
        have h4 : (3 : ℝ) ≤ max 3 K := le_max_left _ _
        have h5 : (((2 ^ 2 - 1 : ℕ)) : ℝ) = 3 := by norm_num
        linarith
      rw [← Real.rpow_natCast]
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC2.le (Nat.cast_nonneg D))
      exact Real.rpow_le_rpow_of_exponent_le hlog h3'
    have hfinal := add_le_add (le_trans hb1 hb1') (le_trans hb2 hb2')
    refine le_trans hfinal ?_
    have hxn : (0 : ℝ) < (Real.log ((D : ℝ) + 2)) ^ (max 3 K + 1) :=
      Real.rpow_pos_of_pos hlog0 _
    have hDnn : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
    have hM1 : C2 ≤ max C2 C3 + 1 := by
      have := le_max_left C2 C3; linarith
    have hM2 : C3 ≤ max C2 C3 + 1 := by
      have := le_max_right C2 C3; linarith
    have hM0 : (0 : ℝ) ≤ max C2 C3 + 1 := by
      have := le_max_left C2 C3; linarith [hC2.le]
    nlinarith [hxn, hDnn, hM1, hM2, hM0, hC2.le, hC3.le,
      mul_nonneg hDnn hxn.le, mul_nonneg (mul_nonneg hDnn hxn.le) hxn.le]

/-- **The density-tail bound summed over the squarefree moduli `d ≤ D`.** -/
theorem FI_gtail_sum_le :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ D m : ℕ, 1 ≤ m →
      (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |gtail FIg FIgtil d m|)
        ≤ C * (D : ℝ) * (Real.log ((D : ℝ) + 2)) ^ A
            * (Real.log ((m : ℝ) + 2)) ^ 4 / (m : ℝ) := by
  obtain ⟨C1, A, hC1, hA, h1⟩ := sum_sqfree_three_pow_add_FIgtil_le
  refine ⟨4 * C1, A, by positivity, hA, fun D m hm => ?_⟩
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hstep : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |gtail FIg FIgtil d m|)
      ≤ ∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
          (4 * ((3 : ℝ) ^ (d.primeFactors.card) + FIgtil d)
            * (Real.log ((m : ℝ) + 2)) ^ 4 / (m : ℝ)) := by
    refine Finset.sum_le_sum (fun d hd => ?_)
    exact FI_gtail_le d m (Finset.mem_filter.mp hd).2 hm
  refine le_trans hstep ?_
  have hb := h1 D
  have hlogm : (0 : ℝ) ≤ (Real.log ((m : ℝ) + 2)) ^ 4 := by positivity
  have hfac : (∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
        (4 * ((3 : ℝ) ^ (d.primeFactors.card) + FIgtil d)
          * (Real.log ((m : ℝ) + 2)) ^ 4 / (m : ℝ)))
      = (4 * (Real.log ((m : ℝ) + 2)) ^ 4 / (m : ℝ))
        * ∑ d ∈ (Finset.Icc 1 D).filter Squarefree,
            ((3 : ℝ) ^ (d.primeFactors.card) + FIgtil d) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    ring
  rw [hfac]
  have h4Lm : (0 : ℝ) ≤ 4 * (Real.log ((m : ℝ) + 2)) ^ 4 / (m : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) hlogm) hm0.le
  refine le_trans (mul_le_mul_of_nonneg_left hb h4Lm) (le_of_eq (by ring))

end

end Submission.ASP
