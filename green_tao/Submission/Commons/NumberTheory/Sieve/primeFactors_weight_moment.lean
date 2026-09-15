import Mathlib.Algebra.Order.Ring.Star
import Submission.Commons.Analysis.RealPow.one_add_pow_le_two_pow_mul
import Submission.Commons.NumberTheory.Nat.prod_prime_dvd_of_subset_primeFactors
import Submission.Commons.Analysis.RealPow.prod_mul_rpow_neg_half_div_prod_eq
import Submission.Commons.Analysis.Sum.sum_Icc_rpow_neg_three_halves_le
import Submission.Commons.NumberTheory.Mertens.factorial_log_eq_sum_legendre

namespace Commons.NumberTheory.Sieve

open Finset

/-- The number of multiples of `r` in `{1, …, N}` equals `N / r`. -/
lemma card_Icc_filter_dvd (N r : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => r ∣ n)).card = N / r := by
  have h : (Finset.Icc 1 N).filter (fun n => r ∣ n)
      = (Finset.range (N + 1)).filter (fun k => k ≠ 0 ∧ r ∣ k) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, hd⟩; exact ⟨by omega, by omega, hd⟩
    · rintro ⟨h1, h2, hd⟩; exact ⟨⟨by omega, by omega⟩, hd⟩
  rw [h, Nat.card_multiples']

/-- For `1 ≤ n ≤ N`, the prime factors of `n` are among the primes `≤ N`. -/
lemma weight_primeFactors_subset_primesLE {n N : ℕ} (hn : 1 ≤ n) (hN : n ≤ N) :
    n.primeFactors ⊆ Nat.primesLE N := by
  have hdvd : n ∣ N.factorial := Nat.dvd_factorial (by omega) hN
  have hsub : n.primeFactors ⊆ (N.factorial).primeFactors :=
    Nat.primeFactors_mono hdvd (Nat.factorial_ne_zero N)
  rwa [Commons.NumberTheory.Mertens.primeFactors_factorial_eq_primesLE N] at hsub

/-- Euler-product style bound: for a finite set `S` of naturals `≥ 1` and `B ≥ 0`,
`∑_{t ⊆ S} ∏_{p ∈ t} B p^{-3/2} ≤ exp (3 B)`. -/
lemma sum_powerset_prod_mul_rpow_neg_le_exp {B : ℝ} (hB : 0 ≤ B) (S : Finset ℕ)
    (hS : ∀ p ∈ S, 1 ≤ p) :
    (∑ t ∈ S.powerset, ∏ p ∈ t, B * (p:ℝ)^(-(3/2:ℝ))) ≤ Real.exp (3 * B) := by
  have hSsum : ∑ p ∈ S, (p:ℝ)^(-(3/2:ℝ)) ≤ 3 := by
    rcases S.eq_empty_or_nonempty with h | hne
    · rw [h, Finset.sum_empty]; norm_num
    · set M := S.max' hne with hM
      have hsub : S ⊆ Finset.Icc 1 M := by
        intro p hp
        exact Finset.mem_Icc.mpr ⟨hS p hp, Finset.le_max' S p hp⟩
      calc ∑ p ∈ S, (p:ℝ)^(-(3/2:ℝ))
          ≤ ∑ j ∈ Finset.Icc 1 M, (j:ℝ)^(-(3/2:ℝ)) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hsub
            intro j hj hjS
            exact Real.rpow_nonneg (by positivity) _
        _ = ∑ j ∈ Finset.Icc 1 M, (j:ℝ)^(-(3:ℝ)/2) := by
            apply Finset.sum_congr rfl; intro j hj
            rw [show (-(3/2:ℝ)) = (-(3:ℝ)/2) by norm_num]
        _ ≤ 3 := Commons.Analysis.Sum.sum_Icc_rpow_neg_three_halves_le M
  calc ∑ t ∈ S.powerset, ∏ p ∈ t, B * (p:ℝ)^(-(3/2:ℝ))
      = ∏ p ∈ S, (1 + B * (p:ℝ)^(-(3/2:ℝ))) := (Finset.prod_one_add S).symm
    _ ≤ ∏ p ∈ S, Real.exp (B * (p:ℝ)^(-(3/2:ℝ))) := by
        apply Finset.prod_le_prod
        · intro p hp
          have hp0 : (0:ℝ) ≤ (p:ℝ) := by positivity
          have hpw : (0:ℝ) ≤ (p:ℝ)^(-(3/2:ℝ)) := Real.rpow_nonneg hp0 _
          nlinarith [hB, hpw]
        · intro p hp
          have := Real.add_one_le_exp (B * (p:ℝ)^(-(3/2:ℝ)))
          linarith
    _ = Real.exp (∑ p ∈ S, B * (p:ℝ)^(-(3/2:ℝ))) := (Real.exp_sum S _).symm
    _ = Real.exp (B * ∑ p ∈ S, (p:ℝ)^(-(3/2:ℝ))) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (3 * B) := by
        apply Real.exp_le_exp.mpr
        calc B * ∑ p ∈ S, (p:ℝ)^(-(3/2:ℝ)) ≤ B * 3 := mul_le_mul_of_nonneg_left hSsum hB
          _ = 3 * B := by ring

theorem primeFactors_weight_moment (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
        (∏ p ∈ n.primeFactors, (1 + (p : ℝ) ^ (-(1/2 : ℝ)))) ^ q ≤ C := by
  classical
  refine ⟨Real.exp (3 * (2:ℝ)^q), Real.exp_pos _, ?_⟩
  intro N hN
  set B : ℝ := (2:ℝ)^q with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  set Wd : ℕ → ℝ := fun n => ∏ p ∈ n.primeFactors, (1 + B * (p:ℝ)^(-(1/2:ℝ))) with hWd
  -- (1) per-n comparison
  have hstep1 : ∀ n : ℕ,
      (∏ p ∈ n.primeFactors, (1 + (p:ℝ)^(-(1/2:ℝ))))^q ≤ Wd n := by
    intro n
    rw [hWd, ← Finset.prod_pow]
    apply Finset.prod_le_prod
    · intro p hp
      have hp0 : (0:ℝ) ≤ (p:ℝ) := by positivity
      have hw : 0 ≤ (p:ℝ)^(-(1/2:ℝ)) := Real.rpow_nonneg hp0 _
      exact pow_nonneg (by linarith) q
    · intro p hp
      have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
      have hx0 : 0 ≤ (p:ℝ)^(-(1/2:ℝ)) := Real.rpow_nonneg (by positivity) _
      have hx1 : (p:ℝ)^(-(1/2:ℝ)) ≤ 1 := by
        have h := Real.rpow_le_rpow_of_nonpos (show (0:ℝ) < 1 by norm_num)
          (show (1:ℝ) ≤ (p:ℝ) by exact_mod_cast hpp.one_le)
          (show (-(1/2:ℝ)) ≤ 0 by norm_num)
        rwa [Real.one_rpow] at h
      have hp1 := Commons.Analysis.RealPow.one_add_pow_le_two_pow_mul q ((p:ℝ)^(-(1/2:ℝ))) hx0 hx1
      rw [hBdef]
      exact hp1
  -- (2) swap the two sums
  have hswap : ∑ n ∈ Finset.Icc 1 N, Wd n
      = ∑ t ∈ (Nat.primesLE N).powerset, (∏ p ∈ t, B * (p:ℝ)^(-(1/2:ℝ)))
          * (((Finset.Icc 1 N).filter (fun n => t ⊆ n.primeFactors)).card : ℝ) := by
    have h1 : ∀ n ∈ Finset.Icc 1 N, Wd n
        = ∑ t ∈ (Nat.primesLE N).powerset,
            (if t ⊆ n.primeFactors then (∏ p ∈ t, B * (p:ℝ)^(-(1/2:ℝ))) else 0) := by
      intro n hn
      simp only [hWd]
      rw [Finset.prod_one_add]
      rw [show (∑ t ∈ (n.primeFactors).powerset, ∏ p ∈ t, B * (p:ℝ)^(-(1/2:ℝ)))
            = ∑ t ∈ (n.primeFactors).powerset,
                (if t ⊆ n.primeFactors then (∏ p ∈ t, B * (p:ℝ)^(-(1/2:ℝ))) else 0) from
          Finset.sum_congr rfl (fun t ht => by rw [if_pos (Finset.mem_powerset.mp ht)])]
      exact Finset.sum_subset
        (Finset.powerset_mono.mpr (weight_primeFactors_subset_primesLE (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2))
        (fun t htS htns => by rw [if_neg]; intro htc; exact htns (Finset.mem_powerset.mpr htc))
    calc ∑ n ∈ Finset.Icc 1 N, Wd n
        = ∑ n ∈ Finset.Icc 1 N, ∑ t ∈ (Nat.primesLE N).powerset,
            (if t ⊆ n.primeFactors then (∏ p ∈ t, B * (p:ℝ)^(-(1/2:ℝ))) else 0) :=
          Finset.sum_congr rfl h1
      _ = ∑ t ∈ (Nat.primesLE N).powerset, ∑ n ∈ Finset.Icc 1 N,
            (if t ⊆ n.primeFactors then (∏ p ∈ t, B * (p:ℝ)^(-(1/2:ℝ))) else 0) :=
          Finset.sum_comm
      _ = ∑ t ∈ (Nat.primesLE N).powerset, (∏ p ∈ t, B * (p:ℝ)^(-(1/2:ℝ)))
            * (((Finset.Icc 1 N).filter (fun n => t ⊆ n.primeFactors)).card : ℝ) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- (3) term-by-term bound
  have hterm : ∀ t ∈ (Nat.primesLE N).powerset,
      (∏ p ∈ t, B * (p:ℝ)^(-(1/2:ℝ)))
        * (((Finset.Icc 1 N).filter (fun n => t ⊆ n.primeFactors)).card : ℝ)
        ≤ (N:ℝ) * ∏ p ∈ t, B * (p:ℝ)^(-(3/2:ℝ)) := by
    intro t ht
    rw [Finset.mem_powerset] at ht
    have htprime : ∀ p ∈ t, Nat.Prime p := fun p hp => (Nat.mem_primesLE.mp (ht hp)).2
    have htpos : ∀ p ∈ t, 0 < p := fun p hp => lt_of_lt_of_le (by norm_num) (htprime p hp).two_le
    have hsub : (Finset.Icc 1 N).filter (fun n => t ⊆ n.primeFactors)
        ⊆ (Finset.Icc 1 N).filter (fun n => (∏ p ∈ t, p) ∣ n) := by
      intro n hn
      rw [Finset.mem_filter] at hn ⊢
      exact ⟨hn.1, Commons.NumberTheory.Nat.prod_prime_dvd_of_subset_primeFactors htprime hn.2⟩
    have hcardNat : ((Finset.Icc 1 N).filter (fun n => t ⊆ n.primeFactors)).card
        ≤ N / (∏ p ∈ t, p) := by
      calc ((Finset.Icc 1 N).filter (fun n => t ⊆ n.primeFactors)).card
          ≤ ((Finset.Icc 1 N).filter (fun n => (∏ p ∈ t, p) ∣ n)).card :=
            Finset.card_le_card hsub
        _ = N / (∏ p ∈ t, p) := card_Icc_filter_dvd N (∏ p ∈ t, p)
    have hcard : (((Finset.Icc 1 N).filter (fun n => t ⊆ n.primeFactors)).card : ℝ)
        ≤ (N:ℝ) / (∏ p ∈ t, (p:ℝ)) := by
      calc (((Finset.Icc 1 N).filter (fun n => t ⊆ n.primeFactors)).card : ℝ)
          ≤ ((N / (∏ p ∈ t, p) : ℕ) : ℝ) := by exact_mod_cast hcardNat
        _ ≤ (N:ℝ) / ((∏ p ∈ t, p : ℕ) : ℝ) := Nat.cast_div_le
        _ = (N:ℝ) / (∏ p ∈ t, (p:ℝ)) := by push_cast; rfl
    have hA0 : 0 ≤ ∏ p ∈ t, B * (p:ℝ)^(-(1/2:ℝ)) := by
      apply Finset.prod_nonneg; intro p hp; positivity
    calc (∏ p ∈ t, B * (p:ℝ)^(-(1/2:ℝ)))
          * (((Finset.Icc 1 N).filter (fun n => t ⊆ n.primeFactors)).card : ℝ)
        ≤ (∏ p ∈ t, B * (p:ℝ)^(-(1/2:ℝ))) * ((N:ℝ) / (∏ p ∈ t, (p:ℝ))) :=
          mul_le_mul_of_nonneg_left hcard hA0
      _ = (N:ℝ) * ((∏ p ∈ t, B * (p:ℝ)^(-(1/2:ℝ))) * (∏ p ∈ t, (p:ℝ))⁻¹) := by
          rw [div_eq_mul_inv]; ring
      _ = (N:ℝ) * ∏ p ∈ t, B * (p:ℝ)^(-(3/2:ℝ)) := by
          rw [Commons.Analysis.RealPow.prod_mul_rpow_neg_half_div_prod_eq B t htpos]
  -- (4) sum bound
  have hsum : ∑ n ∈ Finset.Icc 1 N, Wd n ≤ (N:ℝ) * Real.exp (3 * B) := by
    rw [hswap]
    calc ∑ t ∈ (Nat.primesLE N).powerset, (∏ p ∈ t, B * (p:ℝ)^(-(1/2:ℝ)))
            * (((Finset.Icc 1 N).filter (fun n => t ⊆ n.primeFactors)).card : ℝ)
        ≤ ∑ t ∈ (Nat.primesLE N).powerset, (N:ℝ) * ∏ p ∈ t, B * (p:ℝ)^(-(3/2:ℝ)) :=
          Finset.sum_le_sum hterm
      _ = (N:ℝ) * ∑ t ∈ (Nat.primesLE N).powerset, ∏ p ∈ t, B * (p:ℝ)^(-(3/2:ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ (N:ℝ) * Real.exp (3 * B) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply sum_powerset_prod_mul_rpow_neg_le_exp hB0
          intro p hp
          exact (Nat.mem_primesLE.mp hp).2.one_le
  -- final
  have hmain : ∑ n ∈ Finset.Icc 1 N,
        (∏ p ∈ n.primeFactors, (1 + (p:ℝ)^(-(1/2:ℝ))))^q ≤ (N:ℝ) * Real.exp (3*B) := by
    calc ∑ n ∈ Finset.Icc 1 N, (∏ p ∈ n.primeFactors, (1 + (p:ℝ)^(-(1/2:ℝ))))^q
        ≤ ∑ n ∈ Finset.Icc 1 N, Wd n := Finset.sum_le_sum (fun n hn => hstep1 n)
      _ ≤ (N:ℝ) * Real.exp (3 * B) := hsum
  have hNne : (N:ℝ) ≠ 0 := by
    have : (0:ℝ) < N := by exact_mod_cast hN
    exact ne_of_gt this
  calc (N:ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, (∏ p ∈ n.primeFactors, (1 + (p:ℝ)^(-(1/2:ℝ))))^q
      ≤ (N:ℝ)⁻¹ * ((N:ℝ) * Real.exp (3*B)) := mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = Real.exp (3 * B) := by rw [← mul_assoc, inv_mul_cancel₀ hNne, one_mul]

end Commons.NumberTheory.Sieve