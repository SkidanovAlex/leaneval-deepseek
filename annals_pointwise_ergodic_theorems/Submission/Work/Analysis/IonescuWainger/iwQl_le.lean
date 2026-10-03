/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Analysis.IonescuWainger.Pset

/-!
# Growth of the common denominator `Q_{≤l}` of the Ionescu–Wainger frequency set

Appendix A of Krause–Mirek–Tao, *Pointwise ergodic theorems for non-conventional bilinear
polynomial averages*, Annals of Math. 195 (2022), attaches to each scale `l` the set `P_{≤l}` of
admissible denominators and its common denominator `Q_{≤l} = lcm(P_{≤l})`.  The Fourier analysis
of the IW projections `Π_{l,≤k}` is carried out on the cyclic group `ℤ/Q_{≤l}`, and for this one
needs the *upper* bound `Q_{≤l} ≤ 2^{C_ρ 2^l}` (Krause–Mirek–Tao, Appendix A).

This file proves that bound for the formalisation `iwQl ρ l = (iwP ρ l).lcm id` of
`Work.Analysis.IonescuWainger.iwQl`:

* `Work.Analysis.IonescuWainger.iwQl_le`

## The proof

Write `D = D_ρ`.  For `l ≤ iwC0 ρ` we have `P_{≤l} = [2^l]`, so `Q_{≤l} ∣ (2^l)! ≤ (2^l)^{2^l}`,
i.e. `log Q_{≤l} ≤ 2^l · l log 2 ≤ iwC0 ρ · 2^l log 2`.

For `l > iwC0 ρ` every element of `P_{≤l}` is `Q · w` with `Q ∣ Q_0^{(l)} = (N_0^{(l)}!)^{D}`
and `w ∣ ∏_{p ∈ (N_0^{(l)}, 2^l], p prime} p^{D}`; hence

`Q_{≤l} ∣ Q_0^{(l)} · ∏_{p ≤ 2^l, p prime} p^{D}`,

so `log Q_{≤l} ≤ log Q_0^{(l)} + D log (∏_{p ≤ 2^l, p prime} p)`.

* `log Q_0^{(l)} ≤ 2 D (1 + log 2) 2^{ρ l} ≤ 2 D (1 + log 2) 2^l`  (`iwN_0^{(l)} ≤ 2·2^{ρl/2}`,
  `N! ≤ N^N`, and `x log 2 ≤ 2^x`);
* `∏_{p ≤ 2^l, p prime} p ≤ 4^{2^l} = 2^{2^{l+1}}` (the Chebyshev/Erdős bound on the primorial,
  `Mathlib.NumberTheory.Primorial`), so `D log (∏_{p ≤ 2^l} p) ≤ 2 D log 2 · 2^l`.

Both cases are therefore of the shape `log Q_{≤l} ≤ K · 2^l` for the single constant
`K = iwC0 ρ · log 2 + 2 D (1 + 2 log 2)`, and exponentiating gives the claim with
`C = K / log 2 + 1`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Analysis.IonescuWainger

/-! ## The Chebyshev/Erdős bound for the primorial -/

/-- **Chebyshev bound.** The product of the primes in `[m, 2^l]` is at most `2^{2^{l+1}} = 4^{2^l}`
— the classical bound `θ(x) ≤ (log 4) x` for the Chebyshev function at `x = 2^l`.  This follows
immediately from Mathlib's `primorial_le_four_pow` since the primes in `[m, 2^l]` are a
sub-collection of the primes `≤ 2^l`. -/
private theorem prime_prod_Icc_le (m l : ℕ) :
    (∏ p ∈ (Finset.Icc m (2 ^ l)).filter Nat.Prime, p) ≤ 2 ^ (2 ^ (l + 1)) := by
  have hsub : (Finset.Icc m (2 ^ l)).filter Nat.Prime ⊆ Nat.primesLE (2 ^ l) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact Nat.mem_primesLE.mpr ⟨(Finset.mem_Icc.mp hp.1).2, hp.2⟩
  calc ∏ p ∈ (Finset.Icc m (2 ^ l)).filter Nat.Prime, p
      ≤ ∏ p ∈ Nat.primesLE (2 ^ l), p :=
        Finset.prod_le_prod_of_subset_of_one_le' hsub
          (fun p hp _ => by have := (Nat.mem_primesLE.mp hp).2.two_le; omega)
    _ = primorial (2 ^ l) := (primorial_eq_prod_primesLE _).symm
    _ ≤ 4 ^ (2 ^ l) := primorial_le_four_pow _
    _ = 2 ^ (2 ^ (l + 1)) := by
        rw [show (4:ℕ) = 2 ^ 2 from rfl, ← pow_mul, pow_succ]
        ring

/-- The prime product `iwProd ρ l = ∏_{p ∈ (N_0^{(l)}, 2^l]} p^{D_ρ}` is at most
`(2^{2^{l+1}})^{D_ρ}`. -/
private theorem iwProd_le_pow {ρ : ℝ} (l : ℕ) :
    (iwProd ρ l : ℕ) ≤ (2 ^ (2 ^ (l + 1))) ^ iwD ρ := by
  have hprime : (∏ p ∈ iwPrimeRange ρ l, p) ≤ 2 ^ (2 ^ (l + 1)) :=
    prime_prod_Icc_le (iwN0 ρ l + 1) l
  rw [iwProd, Finset.prod_pow]
  exact Nat.pow_le_pow_left hprime _

/-- `log (iwProd ρ l) ≤ 2 D_ρ log 2 · 2^l`. -/
private lemma log_iwProd_le {ρ : ℝ} (l : ℕ) :
    Real.log ((iwProd ρ l : ℕ) : ℝ) ≤ 2 * (iwD ρ : ℝ) * (2 : ℝ) ^ (l : ℝ) * Real.log 2 := by
  have hpos : (0 : ℝ) < ((iwProd ρ l : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (iwProd_ne_zero ρ l)
  have h1 : ((iwProd ρ l : ℕ) : ℝ) ≤ (((2 ^ (2 ^ (l + 1))) ^ iwD ρ : ℕ) : ℝ) := by
    exact_mod_cast iwProd_le_pow (ρ := ρ) l
  have h2 := Real.log_le_log hpos h1
  have h3 : Real.log ((((2 ^ (2 ^ (l + 1))) ^ iwD ρ : ℕ)) : ℝ)
      = ((2 ^ (l + 1) : ℕ) : ℝ) * (iwD ρ : ℝ) * Real.log 2 := by
    rw [← pow_mul, Nat.cast_pow, Real.log_pow]
    push_cast
    ring
  rw [h3] at h2
  have h4 : ((2 ^ (l + 1) : ℕ) : ℝ) = 2 * (2 : ℝ) ^ (l : ℝ) := by
    rw [Nat.cast_pow, Real.rpow_natCast, pow_succ]
    ring
  rw [h4] at h2
  linarith [h2]

/-! ## Elementary estimates for `Q_0^{(l)}` -/

/-- `x * log 2 ≤ 2 ^ x` for every real `x`: the elementary bound that compares the linear scale
with the exponential scale. -/
private lemma mul_log_two_le_two_rpow (x : ℝ) : x * Real.log 2 ≤ (2 : ℝ) ^ x := by
  have h := Real.add_one_le_exp (x * Real.log 2)
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) x, mul_comm (Real.log 2) x]
  linarith

/-- **Logarithmic bound for `Q_0^{(l)} = (N_0^{(l)}!)^{D_ρ}`.**  With `N_0^{(l)} ≤ 2·2^{ρl/2}` and
`N_0! ≤ N_0^{N_0}` we get `log Q_0 ≤ D_ρ · N_0 log N_0 ≤ 2 D_ρ (1 + log 2) 2^{ρl}`. -/
private lemma log_iwQ0_le {ρ : ℝ} (hρ : 0 < ρ) (l : ℕ) :
    Real.log ((iwQ0 ρ l : ℕ) : ℝ)
      ≤ 2 * (iwD ρ : ℝ) * (1 + Real.log 2) * (2 : ℝ) ^ (ρ * (l : ℝ)) := by
  set S : ℝ := (2 : ℝ) ^ (ρ * (l : ℝ)) with hSdef
  set t : ℝ := (2 : ℝ) ^ (ρ * (l : ℝ) / 2) with htdef
  have hSpos : 0 < S := by rw [hSdef]; positivity
  have htpos : 0 < t := by rw [htdef]; positivity
  have ht1 : 1 ≤ t := by
    rw [htdef]; exact Real.one_le_rpow (by norm_num) (by positivity)
  have htt : t * t = S := by
    rw [htdef, hSdef, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have htS : t ≤ S := by
    have h : t ≤ t * t := by nlinarith [ht1, htpos]
    linarith [htt]
  have hLpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hxL : (ρ * (l : ℝ) / 2) * Real.log 2 ≤ t := by
    rw [htdef]; exact mul_log_two_le_two_rpow _
  have hN0pos : (0 : ℝ) < ((iwN0 ρ l : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < iwN0 ρ l by rw [iwN0]; exact Nat.succ_pos _)
  have hN0le : ((iwN0 ρ l : ℕ) : ℝ) ≤ 2 * t := by
    have hfl : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le (le_of_lt htpos)
    have heq : ((iwN0 ρ l : ℕ) : ℝ) = ((⌊t⌋₊ : ℕ) : ℝ) + 1 := by
      rw [iwN0, ← htdef, Nat.cast_add, Nat.cast_one]
    rw [heq]; linarith
  have hlogN0 : Real.log ((iwN0 ρ l : ℕ) : ℝ)
      ≤ Real.log 2 + (ρ * (l : ℝ) / 2) * Real.log 2 := by
    have h1 : Real.log ((iwN0 ρ l : ℕ) : ℝ) ≤ Real.log (2 * t) :=
      Real.log_le_log hN0pos hN0le
    have h2 : Real.log (2 * t) = Real.log 2 + (ρ * (l : ℝ) / 2) * Real.log 2 := by
      rw [Real.log_mul (by norm_num) (ne_of_gt htpos), htdef,
        Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
    linarith [h1, h2.le]
  have hlogN0pos : 0 ≤ Real.log ((iwN0 ρ l : ℕ) : ℝ) :=
    Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ iwN0 ρ l by rw [iwN0]; exact Nat.le_add_left 1 _))
  have hfact : Real.log (((iwN0 ρ l).factorial : ℕ) : ℝ)
      ≤ ((iwN0 ρ l : ℕ) : ℝ) * Real.log ((iwN0 ρ l : ℕ) : ℝ) := by
    have h := Nat.factorial_le_pow (iwN0 ρ l)
    have hR : (((iwN0 ρ l).factorial : ℕ) : ℝ) ≤ (((iwN0 ρ l) ^ (iwN0 ρ l) : ℕ) : ℝ) := by
      exact_mod_cast h
    have hp : (0 : ℝ) < (((iwN0 ρ l).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    have h2 := Real.log_le_log hp hR
    rw [Nat.cast_pow, Real.log_pow] at h2
    exact h2
  have hD0 : (0 : ℝ) ≤ (iwD ρ : ℝ) := by positivity
  rw [iwQ0, Nat.cast_pow, Real.log_pow]
  have hstep1 := mul_le_mul_of_nonneg_left hfact hD0
  have hstep2 : ((iwN0 ρ l : ℕ) : ℝ) * Real.log ((iwN0 ρ l : ℕ) : ℝ)
      ≤ (2 * t) * (Real.log 2 + (ρ * (l : ℝ) / 2) * Real.log 2) := by
    calc ((iwN0 ρ l : ℕ) : ℝ) * Real.log ((iwN0 ρ l : ℕ) : ℝ)
        ≤ (2 * t) * Real.log ((iwN0 ρ l : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hN0le hlogN0pos
      _ ≤ (2 * t) * (Real.log 2 + (ρ * (l : ℝ) / 2) * Real.log 2) :=
          mul_le_mul_of_nonneg_left hlogN0 (by positivity)
  have hstep3 : (2 * t) * (Real.log 2 + (ρ * (l : ℝ) / 2) * Real.log 2)
      ≤ 2 * (1 + Real.log 2) * S := by
    nlinarith [hxL, htS, hLpos, htpos, htt]
  have hstep4 := mul_le_mul_of_nonneg_left hstep3 hD0
  have hstep2' := mul_le_mul_of_nonneg_left hstep2 hD0
  nlinarith [hstep1, hstep2', hstep4]

/-! ## The growth bound for `Q_{≤l}` -/

theorem iwQl_le {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ l, (iwQl ρ l : ℝ) ≤ (2 : ℝ) ^ (C * (2 : ℝ) ^ (l : ℝ)) := by
  set L : ℝ := Real.log 2 with hLdef
  set D : ℝ := (iwD ρ : ℝ) with hDdef
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by norm_num)
  have hD1 : 1 ≤ D := by
    rw [hDdef]; exact_mod_cast (show 1 ≤ iwD ρ by rw [iwD]; exact Nat.le_add_left 1 _)
  have hD0 : 0 ≤ D := le_trans zero_le_one hD1
  set K : ℝ := (iwC0 ρ : ℝ) * L + 2 * D * (1 + 2 * L) with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have h1 : 0 ≤ (iwC0 ρ : ℝ) * L := mul_nonneg (by positivity) hLpos.le
    have h2 : 0 < 2 * D * (1 + 2 * L) := by nlinarith [hD1, hLpos]
    linarith
  refine ⟨K / L + 1, ?_, ?_⟩
  · have : 0 ≤ K / L := div_nonneg hKpos.le hLpos.le
    linarith
  intro l
  have hlog : Real.log ((iwQl ρ l : ℕ) : ℝ) ≤ K * (2 : ℝ) ^ (l : ℝ) := by
    by_cases hl : l ≤ iwC0 ρ
    · -- Case `l ≤ iwC0 ρ`: `P_{≤l} = [2^l]` and `Q_{≤l} ∣ (2^l)! ≤ (2^l)^{2^l}`
      have hdvd : iwQl ρ l ∣ (2 ^ l).factorial := by
        rw [iwQl, show iwP ρ l = Finset.Icc 1 (2 ^ l) from by rw [iwP, if_pos hl]]
        refine Finset.lcm_dvd (fun q hq => ?_)
        exact Nat.dvd_factorial (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2
      have hle : iwQl ρ l ≤ (2 ^ l).factorial := Nat.le_of_dvd (Nat.factorial_pos _) hdvd
      have h1 : Real.log ((iwQl ρ l : ℕ) : ℝ) ≤ ((2 ^ l : ℕ) : ℝ) * ((l : ℝ) * L) := by
        calc Real.log ((iwQl ρ l : ℕ) : ℝ)
            ≤ Real.log (((2 ^ l).factorial : ℕ) : ℝ) :=
              Real.log_le_log (by exact_mod_cast iwQl_pos) (by exact_mod_cast hle)
          _ ≤ Real.log ((((2 ^ l) ^ (2 ^ l) : ℕ)) : ℝ) :=
              Real.log_le_log (by exact_mod_cast Nat.factorial_pos _)
                (by exact_mod_cast Nat.factorial_le_pow (2 ^ l))
          _ = ((2 ^ l : ℕ) : ℝ) * ((l : ℝ) * L) := by
              rw [Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow]
              simp only [Nat.cast_ofNat]
              rw [← hLdef, Nat.cast_pow]
              norm_num
      have h2 : ((2 ^ l : ℕ) : ℝ) * ((l : ℝ) * L) ≤ K * (2 : ℝ) ^ (l : ℝ) := by
        have h2l : ((2 ^ l : ℕ) : ℝ) = (2 : ℝ) ^ (l : ℝ) := by
          rw [Nat.cast_pow, Real.rpow_natCast]
          norm_num
        rw [h2l]
        have hlR : (l : ℝ) ≤ (iwC0 ρ : ℝ) := by exact_mod_cast hl
        have hX : 0 ≤ (2 : ℝ) ^ (l : ℝ) := Real.rpow_nonneg (by norm_num) _
        have hlk : (l : ℝ) * L ≤ K := by
          have h3 : (l : ℝ) * L ≤ (iwC0 ρ : ℝ) * L :=
            mul_le_mul_of_nonneg_right hlR hLpos.le
          have h4 : (iwC0 ρ : ℝ) * L ≤ K := by
            rw [hKdef]
            have : 0 ≤ 2 * D * (1 + 2 * L) := by nlinarith [hD1, hLpos]
            linarith
          linarith
        calc (2 : ℝ) ^ (l : ℝ) * ((l : ℝ) * L)
            = ((l : ℝ) * L) * (2 : ℝ) ^ (l : ℝ) := by ring
          _ ≤ K * (2 : ℝ) ^ (l : ℝ) := mul_le_mul_of_nonneg_right hlk hX
      linarith [h1, h2]
    · -- Case `l > iwC0 ρ`: `P_{≤l} = P^{concrete}_{≤l}` and every element divides
      -- `Q_0^{(l)} · iwProd ρ l`
      have hdvd : iwQl ρ l ∣ iwQ0 ρ l * iwProd ρ l := by
        rw [iwQl, show iwP ρ l = iwPconcrete ρ l from by rw [iwP, if_neg hl]]
        refine Finset.lcm_dvd (fun q hq => ?_)
        obtain ⟨Q, hQ, w, hw, rfl⟩ := mem_iwPconcrete.mp hq
        exact mul_dvd_mul (Nat.mem_divisors.mp hQ).1 (mem_iwW.mp hw).1
      have hle : iwQl ρ l ≤ iwQ0 ρ l * iwProd ρ l :=
        Nat.le_of_dvd
          (Nat.mul_pos (Nat.pos_of_ne_zero (iwQ0_ne_zero ρ l))
            (Nat.pos_of_ne_zero (iwProd_ne_zero ρ l))) hdvd
      have hQ0pos : (0 : ℝ) < ((iwQ0 ρ l : ℕ) : ℝ) := by
        exact_mod_cast (show 0 < iwQ0 ρ l from Nat.pos_of_ne_zero (iwQ0_ne_zero ρ l))
      have hPpos : (0 : ℝ) < ((iwProd ρ l : ℕ) : ℝ) := by
        exact_mod_cast (show 0 < iwProd ρ l from Nat.pos_of_ne_zero (iwProd_ne_zero ρ l))
      have hmain : Real.log ((iwQl ρ l : ℕ) : ℝ)
          ≤ Real.log ((iwQ0 ρ l : ℕ) : ℝ) + Real.log ((iwProd ρ l : ℕ) : ℝ) := by
        calc Real.log ((iwQl ρ l : ℕ) : ℝ)
            ≤ Real.log (((iwQ0 ρ l * iwProd ρ l : ℕ)) : ℝ) :=
              Real.log_le_log (by exact_mod_cast iwQl_pos) (by exact_mod_cast hle)
          _ = Real.log ((iwQ0 ρ l : ℕ) : ℝ) + Real.log ((iwProd ρ l : ℕ) : ℝ) := by
              rw [Nat.cast_mul, Real.log_mul (ne_of_gt hQ0pos) (ne_of_gt hPpos)]
      have hlogQ0 : Real.log ((iwQ0 ρ l : ℕ) : ℝ) ≤ 2 * D * (1 + L) * (2 : ℝ) ^ (l : ℝ) := by
        have h := log_iwQ0_le hρ l
        rw [← hDdef, ← hLdef] at h
        have hexp : (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ (2 : ℝ) ^ (l : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
                nlinarith [hρ1, hl0])
        have hc : 0 ≤ 2 * D * (1 + L) := by nlinarith [hD1, hLpos]
        nlinarith [h, hexp, hc]
      have hlogP : Real.log ((iwProd ρ l : ℕ) : ℝ) ≤ 2 * D * (2 : ℝ) ^ (l : ℝ) * L := by
        have h := log_iwProd_le (ρ := ρ) l
        rw [← hDdef, ← hLdef] at h
        exact h
      have hK : 2 * D * (1 + L) * (2 : ℝ) ^ (l : ℝ) + 2 * D * (2 : ℝ) ^ (l : ℝ) * L
          ≤ K * (2 : ℝ) ^ (l : ℝ) := by
        have hX : 0 ≤ (2 : ℝ) ^ (l : ℝ) := Real.rpow_nonneg (by norm_num) _
        have h0 : 0 ≤ (iwC0 ρ : ℝ) * L := mul_nonneg (by positivity) hLpos.le
        nlinarith [hX, h0, hKdef]
      linarith [hmain, hlogQ0, hlogP, hK]
  have hpos : (0 : ℝ) < ((iwQl ρ l : ℕ) : ℝ) := by exact_mod_cast iwQl_pos
  have hXpos : 0 < (2 : ℝ) ^ (l : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hKL : (K / L + 1) * L = K + L := by field_simp
  have hfin : K * (2 : ℝ) ^ (l : ℝ) ≤ (K / L + 1) * (2 : ℝ) ^ (l : ℝ) * L := by
    have h' : (K / L + 1) * (2 : ℝ) ^ (l : ℝ) * L = (K + L) * (2 : ℝ) ^ (l : ℝ) := by
      rw [mul_assoc, mul_comm ((2 : ℝ) ^ (l : ℝ)) L, ← mul_assoc, hKL]
    rw [h']
    nlinarith [hLpos, hXpos]
  rw [← Real.log_le_log_iff hpos
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2)
          ((K / L + 1) * (2 : ℝ) ^ (l : ℝ))),
      Real.log_rpow (by norm_num : (0 : ℝ) < 2), ← hLdef]
  linarith [hlog, hfin]

end Work.Analysis.IonescuWainger
