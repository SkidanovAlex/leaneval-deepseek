/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Analysis.IonescuWainger.iwC0SmallPrimeExp
import Submission.Work.Analysis.IonescuWainger.iwPconcrete_mono

/-!
# `[2^l] ⊆ P_{≤l}` for the Ionescu–Wainger denominator sets

Krause–Mirek–Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals of Math. 195 (2022), Appendix A: for `ρ ∈ (0,1]` and every `l ≥ C⁰_ρ`, the
concrete Ionescu–Wainger set `P_{≤l}` of admissible denominators contains the whole interval
`[1, 2^l]`:

the main result of this file, stated at the end.

Here `P_{≤l} = iwPconcrete ρ l` is the set of `q = Q w` with `Q ∣ Q_0^{(l)} = (N_0^{(l)}!)^{D_ρ}`
and `w ∈ W_{≤l}`, the products of at most `D_ρ` distinct primes from `(N_0^{(l)}, 2^l]`, each
taken to a power in `[1, D_ρ]` (see `Work.Analysis.IonescuWainger.Basic`).  The threshold is
`iwC0 ρ = ⌈(2/ρ)·(1+ε_ρ)/ε_ρ⌉ + ⌈10/ρ⌉ + 100`, where `D_ρ = ⌊2/ρ⌋ + 1` and
`ε_ρ = ρD_ρ/2 - 1`; note the identity `(2/ρ)·(1+ε_ρ)/ε_ρ = D_ρ/ε_ρ`.

## The argument

Given `1 ≤ q ≤ 2^l`, split `q = iwLow N q · iwHigh N q` at the threshold `N = N_0^{(l)}`
(the "small prime" and "large prime" parts of the prime factorization of `q`, from
`Work.Analysis.IonescuWainger.IwMono`).  Then

* `iwLow N q ∣ Q_0^{(l)}`: for every prime `p ≤ N` dividing `q` with exponent `j`, the fact
  `p ^ j ≤ q ≤ 2 ^ l` and `prime_rpow_le` (`N_0 ≤ p ^ ((1+ε_ρ)⌊N_0/p⌋)`) give
  `j ≤ D_ρ ⌊N_0/p⌋ ≤ D_ρ v_p(N_0!)`; this is `iwC0SmallPrimeExp`;
* `iwHigh N q ∈ W_{≤l}`: every prime `p > N` dividing `q` satisfies `p ≤ q ≤ 2^l`, i.e. lies in
  the range `(N_0^{(l)}, 2^l]`, appears in `q` with exponent at most `D_ρ` (since
  `p ≥ N > 2^{ρl/2}` and `p ^ j ≤ 2^l` force `j < 2/ρ < D_ρ`), and the number of such primes is
  at most `D_ρ` (their product is `≤ q ≤ 2^l` while each is `> 2^{ρl/2}`).

Both are pure arithmetic; the two threshold conditions on `l` that make them work are
`l ε_ρ ≥ D_ρ` (equivalently `l ≥ C⁰_ρ`'s first term) and `l ≥ 1`, and they are provided by
`iwC0 ρ ≤ l`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Analysis.IonescuWainger

namespace IwCont

/-- `2^{ρl/2} < N_0^{(l)}`, since `N_0^{(l)} = ⌊2^{ρl/2}⌋ + 1`. -/
theorem iwN0_gt (ρ : ℝ) (l : ℕ) : (2 : ℝ) ^ (ρ * (l : ℝ) / 2) < (iwN0 ρ l : ℝ) := by
  rw [iwN0, Nat.cast_add, Nat.cast_one]
  have := Nat.lt_floor_add_one ((2 : ℝ) ^ (ρ * (l : ℝ) / 2))
  linarith

/-- `2/ρ < D_ρ`, the lower bound coming from the floor in the definition of `D_ρ`. -/
theorem iwD_gt (ρ : ℝ) : 2 / ρ < (iwD ρ : ℝ) := by
  rw [iwD, Nat.cast_add, Nat.cast_one]
  exact Nat.lt_floor_add_one _

/-- **Large primes have bounded multiplicity in `q ≤ 2^l`.**  A prime `p > N_0^{(l)}` occurs in
`q ≤ 2^l` with exponent at most `D_ρ`: from `p ≥ N_0^{(l)} + 1 > 2^{ρl/2}` and `p^{v_p(q)} ≤ 2^l`
one gets `v_p(q) · ρ l / 2 < l`, hence `v_p(q) < 2/ρ < D_ρ`. -/
theorem factorization_le_iwD {ρ : ℝ} (hρ : 0 < ρ) {l q p : ℕ}
    (hl : iwC0 ρ ≤ l) (hq1 : 1 ≤ q) (hq : q ≤ 2 ^ l) (hp : p.Prime)
    (hpN : iwN0 ρ l < p) : q.factorization p ≤ iwD ρ := by
  by_cases hj : q.factorization p = 0
  · simp [hj]
  have hq0 : q ≠ 0 := by omega
  have hdvd : p ^ q.factorization p ∣ q := Nat.ordProj_dvd q p
  have hle : p ^ q.factorization p ≤ q := Nat.le_of_dvd (by omega) hdvd
  have hpgt : (2 : ℝ) ^ (ρ * (l : ℝ) / 2) < (p : ℝ) :=
    lt_of_lt_of_le (iwN0_gt ρ l) (by exact_mod_cast hpN.le)
  have hlpos : 0 < (l : ℝ) := by
    have h1 : (100:ℕ) ≤ iwC0 ρ := by rw [iwC0]; omega
    have h2 : (0:ℕ) < l := by omega
    exact_mod_cast h2
  have hjpos : (0:ℝ) < (q.factorization p : ℝ) := by positivity
  have hstep1 : (q.factorization p : ℝ) * Real.log (p : ℝ) ≤ (l : ℝ) * Real.log 2 := by
    have h1 : ((p ^ q.factorization p : ℕ) : ℝ) ≤ ((2 ^ l : ℕ) : ℝ) := by
      exact_mod_cast le_trans hle hq
    rw [Nat.cast_pow, Nat.cast_pow] at h1
    have hpos : (0:ℝ) < (p : ℝ) ^ (q.factorization p) := pow_pos (by exact_mod_cast hp.pos) _
    have h2 := Real.log_le_log hpos h1
    rwa [Real.log_pow, Real.log_pow] at h2
  have hstep2 : ρ * (l : ℝ) / 2 * Real.log 2 < Real.log (p : ℝ) := by
    have h2 := Real.log_lt_log (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _) hpgt
    rwa [Real.log_rpow (by norm_num : (0:ℝ) < 2)] at h2
  have h3 : (q.factorization p : ℝ) * (ρ * (l : ℝ) / 2) * Real.log 2
      < (q.factorization p : ℝ) * Real.log (p : ℝ) := by
    have h := mul_lt_mul_of_pos_left hstep2 hjpos
    nlinarith [h]
  have h4 : (q.factorization p : ℝ) * (ρ * (l : ℝ) / 2) * Real.log 2
      < (l : ℝ) * Real.log 2 := lt_of_lt_of_le h3 hstep1
  have h5 : (q.factorization p : ℝ) * (ρ * (l : ℝ) / 2) < (l : ℝ) :=
    (mul_lt_mul_iff_of_pos_right (Real.log_pos (by norm_num : (1:ℝ) < 2))).mp h4
  have hkey : ρ * (q.factorization p : ℝ) / 2 < 1 := by nlinarith [h5, hlpos]
  have hlt : (q.factorization p : ℝ) < (iwD ρ : ℝ) := by
    have h3' : (q.factorization p : ℝ) < 2 / ρ := by
      rw [lt_div_iff₀ hρ]; nlinarith [hkey]
    have := iwD_gt ρ; linarith
  exact Nat.le_of_lt (by exact_mod_cast hlt)

/-- The primes of `q` above the threshold `N_0^{(l)}` are exactly the primes of `iwPrimeRange ρ l`
dividing `q` (every prime divisor of `q` is at most `q ≤ 2^l`). -/
theorem support_high_eq {ρ : ℝ} {l q : ℕ} (hq0 : q ≠ 0) (hq : q ≤ 2 ^ l) :
    q.factorization.support.filter (fun p => iwN0 ρ l < p)
      = (iwPrimeRange ρ l).filter (fun p => p ∣ q) := by
  ext p
  rw [Finset.mem_filter, Finset.mem_filter, Nat.support_factorization, Nat.mem_primeFactors,
      IwMono.mem_iwPrimeRange_iff]
  constructor
  · rintro ⟨⟨hpp, hpq, -⟩, hlt⟩
    exact ⟨⟨hlt, Nat.le_trans (Nat.le_of_dvd (by omega) hpq) hq, hpp⟩, hpq⟩
  · rintro ⟨⟨hlt, -, hpp⟩, hpq⟩
    exact ⟨⟨hpp, hpq, hq0⟩, hlt⟩

/-- **At most `D_ρ` large prime factors.**  A number `q ≤ 2^l` has at most `D_ρ` distinct prime
divisors exceeding `N_0^{(l)}`: their product is at most `q ≤ 2^l` while each exceeds
`2^{ρl/2}`, so `k · ρ l / 2 < l` and hence `k < 2/ρ < D_ρ`. -/
theorem iwPrimeRangeCard {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l q : ℕ}
    (hl : iwC0 ρ ≤ l) (hq1 : 1 ≤ q) (hq : q ≤ 2 ^ l) :
    ((iwPrimeRange ρ l).filter (fun p => p ∣ q)).card ≤ iwD ρ := by
  set s := (iwPrimeRange ρ l).filter (fun p => p ∣ q) with hs
  have hsp : ∀ p ∈ s, p.Prime := fun p hp =>
    (IwMono.mem_iwPrimeRange_iff.mp (Finset.mem_filter.mp hp).1).2.2
  by_cases hs0 : s.card = 0
  · simp [hs0]
  have hk1 : 1 ≤ s.card := Nat.one_le_iff_ne_zero.mpr hs0
  have hq0 : q ≠ 0 := by omega
  -- the product of the elements of `s` divides `q`
  have hdvd : (∏ p ∈ s, p) ∣ q := by
    have hprod_eq : (∏ p ∈ s, p) = (∏ p ∈ s, p ^ (1:ℕ)) := by simp
    rw [hprod_eq]
    refine (Nat.factorization_le_iff_dvd ?_ (by omega)).mp (fun r => ?_)
    · rw [Finset.prod_ne_zero_iff]
      intro p hp
      exact pow_ne_zero _ (hsp p hp).ne_zero
    · rw [prod_prime_pow_factorization hsp r]
      by_cases hr : r ∈ s
      · rw [if_pos hr]
        have hrq : r ∣ q := (Finset.mem_filter.mp hr).2
        have hrp : r.Prime := hsp r hr
        have hne : q.factorization r ≠ 0 := by
          intro hz
          rcases (Nat.factorization_eq_zero_iff q r).mp hz with h | h | h
          · exact h hrp
          · exact h hrq
          · exact hq0 h
        omega
      · rw [if_neg hr]; exact Nat.zero_le _
  have hprod_le : (∏ p ∈ s, p) ≤ q := Nat.le_of_dvd (by omega) hdvd
  -- `(N_0^{(l)} + 1) ^ s.card ≤ q ≤ 2^l`
  have hN1 : ∀ p ∈ s, iwN0 ρ l + 1 ≤ p := fun p hp =>
    Nat.succ_le_of_lt (IwMono.mem_iwPrimeRange_iff.mp (Finset.mem_filter.mp hp).1).1
  have hpow_le : (iwN0 ρ l + 1) ^ s.card ≤ q := by
    calc (iwN0 ρ l + 1) ^ s.card = ∏ _p ∈ s, (iwN0 ρ l + 1) := (Finset.prod_const _).symm
      _ ≤ ∏ p ∈ s, p := Finset.prod_le_prod₀ (fun p _ => Nat.zero_le _) hN1
      _ ≤ q := hprod_le
  -- logarithmic chain
  have hN1gt : (2 : ℝ) ^ (ρ * (l : ℝ) / 2) < ((iwN0 ρ l + 1 : ℕ) : ℝ) := by
    have h := iwN0_gt ρ l
    push_cast
    linarith
  have hP : (0:ℝ) < ((iwN0 ρ l + 1 : ℕ) : ℝ) := by positivity
  have hstep1 : (s.card : ℝ) * (ρ * (l : ℝ) / 2 * Real.log 2)
      < (s.card : ℝ) * Real.log ((iwN0 ρ l + 1 : ℕ) : ℝ) := by
    have h2 : ρ * (l : ℝ) / 2 * Real.log 2 < Real.log ((iwN0 ρ l + 1 : ℕ) : ℝ) := by
      have h3 := Real.log_lt_log (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _) hN1gt
      rwa [Real.log_rpow (by norm_num : (0:ℝ) < 2)] at h3
    exact mul_lt_mul_of_pos_left h2 (by exact_mod_cast (by omega : 0 < s.card))
  have hstep2 : (s.card : ℝ) * Real.log ((iwN0 ρ l + 1 : ℕ) : ℝ) ≤ (l : ℝ) * Real.log 2 := by
    have h1 : (((iwN0 ρ l + 1) ^ s.card : ℕ) : ℝ) ≤ ((2 ^ l : ℕ) : ℝ) := by
      exact_mod_cast le_trans hpow_le hq
    rw [Nat.cast_pow, Nat.cast_pow] at h1
    have h2 := Real.log_le_log (pow_pos hP _) h1
    rwa [Real.log_pow, Real.log_pow] at h2
  have hmain : (s.card : ℝ) * (ρ * (l : ℝ) / 2) < (l : ℝ) := by
    have h4 : (s.card : ℝ) * (ρ * (l : ℝ) / 2) * Real.log 2 < (l : ℝ) * Real.log 2 := by
      have := lt_of_lt_of_le hstep1 hstep2
      nlinarith [this]
    exact (mul_lt_mul_iff_of_pos_right (Real.log_pos (by norm_num : (1:ℝ) < 2))).mp h4
  have hkey : ρ * (s.card : ℝ) / 2 < 1 := by
    have hlpos : 0 < (l : ℝ) := by
      have h1 : (100:ℕ) ≤ iwC0 ρ := by rw [iwC0]; omega
      exact_mod_cast (by omega : 0 < l)
    nlinarith [hmain, hlpos]
  have hlt : (s.card : ℝ) < (iwD ρ : ℝ) := by
    have h3' : (s.card : ℝ) < 2 / ρ := by rw [lt_div_iff₀ hρ]; nlinarith [hkey]
    have := iwD_gt ρ; linarith
  exact Nat.le_of_lt (by exact_mod_cast hlt)

/-- **The small-prime part of `q` divides `Q_0^{(l)}`.**  For every prime `p ≤ N_0^{(l)}` the
exponent of `p` in `q ≤ 2^l` is at most `D_ρ · v_p(N_0^{(l)}!)`, by `iwC0SmallPrimeExp`. -/
theorem iwLow_dvd_iwQ0 {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l q : ℕ}
    (hl : iwC0 ρ ≤ l) (hq1 : 1 ≤ q) (hq : q ≤ 2 ^ l) :
    IwMono.iwLow (iwN0 ρ l) q ∣ iwQ0 ρ l := by
  refine (Nat.factorization_le_iff_dvd (IwMono.iwLow_ne_zero _ _) (iwQ0_ne_zero ρ l)).mp (fun p => ?_)
  rw [IwMono.iwLow_factorization, IwMono.iwQ0_factorization]
  by_cases hc : p ∈ q.factorization.support.filter (fun p => p ≤ iwN0 ρ l)
  · rw [if_pos hc]
    obtain ⟨hpsupp, hple⟩ := Finset.mem_filter.mp hc
    have hne : q.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hpsupp
    have hpprime : p.Prime := by
      by_contra hp'
      exact hne ((Nat.factorization_eq_zero_iff q p).mpr (Or.inl hp'))
    have hle : p ^ q.factorization p ≤ q := Nat.le_of_dvd (by omega) (Nat.ordProj_dvd q p)
    exact iwC0SmallPrimeExp hρ hρ1 hl hq hpprime hple hle
  · rw [if_neg hc]; exact Nat.zero_le _

/-- **The large-prime part of `q` lies in `W_{≤l}`.** -/
theorem iwHigh_mem_iwW {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l q : ℕ}
    (hl : iwC0 ρ ≤ l) (hq1 : 1 ≤ q) (hq : q ≤ 2 ^ l) :
    IwMono.iwHigh (iwN0 ρ l) q ∈ iwW ρ l := by
  have hq0 : q ≠ 0 := by omega
  refine mem_iwW.mpr ⟨?_, ?_⟩
  · refine (Nat.factorization_le_iff_dvd (IwMono.iwHigh_ne_zero _ _) (iwProd_ne_zero ρ l)).mp
      (fun p => ?_)
    rw [IwMono.iwHigh_factorization, IwMono.iwProd_factorization]
    by_cases hc : p ∈ q.factorization.support.filter (fun p => iwN0 ρ l < p)
    · rw [if_pos hc]
      obtain ⟨hpsupp, hplt⟩ := Finset.mem_filter.mp hc
      have hne : q.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hpsupp
      have hpprime : p.Prime := by
        by_contra hp'
        exact hne ((Nat.factorization_eq_zero_iff q p).mpr (Or.inl hp'))
      have hpq : p ∣ q := by
        by_contra hp'
        exact hne ((Nat.factorization_eq_zero_iff q p).mpr (Or.inr (Or.inl hp')))
      have hple : p ≤ 2 ^ l := Nat.le_trans (Nat.le_of_dvd (by omega) hpq) hq
      rw [if_pos (IwMono.mem_iwPrimeRange_iff.mpr ⟨hplt, hple, hpprime⟩)]
      exact factorization_le_iwD hρ hl hq1 hq hpprime hplt
    · rw [if_neg hc]; exact Nat.zero_le _
  · rw [IwMono.iwHigh_support, support_high_eq hq0 hq]
    exact iwPrimeRangeCard hρ hρ1 hl hq1 hq

end IwCont

/-- **Appendix A, inclusion `[2^l] ⊆ P_{≤l}`.**  For `ρ ∈ (0,1]` and `l ≥ C⁰_ρ`, every
denominator `1 ≤ q ≤ 2^l` belongs to the concrete Ionescu–Wainger set `iwPconcrete ρ l`: it
factors as `q = Q · w` with `Q ∣ Q_0^{(l)} = (N_0^{(l)}!)^{D_ρ}` (the small primes `≤ N_0^{(l)}`)
and `w ∈ W_{≤l}` (the at most `D_ρ` large primes `> N_0^{(l)}`, each to a power `≤ D_ρ`). -/
theorem iwPconcrete_contains_range {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l q : ℕ}
    (hl : iwC0 ρ ≤ l) (hq1 : 1 ≤ q) (hq2 : q ≤ 2 ^ l) : q ∈ iwPconcrete ρ l := by
  have hq0 : q ≠ 0 := by omega
  refine mem_iwPconcrete.mpr
    ⟨IwMono.iwLow (iwN0 ρ l) q,
     Nat.mem_divisors.mpr ⟨IwCont.iwLow_dvd_iwQ0 hρ hρ1 hl hq1 hq2, iwQ0_ne_zero ρ l⟩,
     IwMono.iwHigh (iwN0 ρ l) q, IwCont.iwHigh_mem_iwW hρ hρ1 hl hq1 hq2, ?_⟩
  exact (IwMono.iwLow_mul_iwHigh (m := iwN0 ρ l) (w := q) hq0).symm

end Work.Analysis.IonescuWainger
