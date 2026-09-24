import Mathlib
import Submission.Work.ChenPlan.H2.Sieve
import Submission.Work.ChenPlan.H2.weighted_rem_bound

/-!
# The total sieve remainder of Chen's `h2`

The remainders of the per-`q` sieves sum into the `3^{ω(d)}`-weighted shifted Bombieri–Vinogradov
remainder: the moduli `m = q·d` (`q` a window prime, `d ∣ oddPrimLt M`) are odd and `< D`, the
map `(q,d) ↦ q·d` is injective (the primes of `d` are `< M ≤ q`), and `3^{ω(qd)} = 3·3^{ω(d)}`.
Hence `Σ_q remSumQ x M q (D/q) ≤ (1/3)·Σ_{m odd ≤ D} 3^{ω(m)}|θ_m(x) - x/φ(m)|`.
-/

open Finset Filter
open scoped BigOperators
open scoped ArithmeticFunction.Omega

namespace Work.ChenPlan.H2

noncomputable section

open Commons.NumberTheory.Chen.ChenEight

/-- The `3^{ω(d)}`-weighted shifted Bombieri–Vinogradov remainder, in the `shiftRem` vocabulary. -/
theorem weighted_rem_bound_shiftRem :
    ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in Filter.atTop,
      ((Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊).filter
          (fun d : ℕ => d % 2 = 1)).sum
        (fun d => (3 : ℝ) ^ d.primeFactors.card * shiftRem x d)
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  intro A hA
  obtain ⟨B, hB, h⟩ := Work.ChenPlan.H2.weighted_rem_bound A hA
  refine ⟨B, hB, h.mono (fun x hx => ?_)⟩
  refine le_trans (Finset.sum_le_sum (fun d _ => ?_)) hx
  rw [shiftRem]
  congr 1
  rw [show ((Finset.range (x + 1)).filter (fun p => p.Prime ∧ d ∣ p + 2)).sum
      (fun p => Real.log (p : ℝ)) = thetaD x d from rfl]

/-- Every element of `oddPrimLt M`'s divisor set is odd. -/
lemma odd_of_dvd_oddPrimLt' {M d : ℕ} (hd : d ∣ oddPrimLt M) : d % 2 = 1 := by
  rcases Nat.eq_zero_or_pos (d % 2) with h0 | h0
  · exfalso
    have h2 : 2 ∣ d := Nat.dvd_of_mod_eq_zero h0
    have : oddPrimLt M % 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_trans h2 hd)
    have := oddPrimLt_odd M
    omega
  · have := Nat.mod_lt d (by norm_num : 0 < 2)
    omega

/-- A prime dividing `oddPrimLt M` is `< M`. -/
lemma prime_lt_of_dvd_oddPrimLt {q M : ℕ} (hq : q.Prime) (hqd : q ∣ oddPrimLt M) : q < M := by
  rw [oddPrimLt_eq_prod_oddLt] at hqd
  obtain ⟨r, hr, hqr⟩ := (hq.prime.dvd_finsetProd_iff (fun r : ℕ => r)).mp hqd
  have hrp : r.Prime := (Submission.mem_oddLt.mp hr).1
  have hrM : r < M := (Submission.mem_oddLt.mp hr).2.2
  rcases (Nat.dvd_prime hrp).mp hqr with h | h
  · exact absurd h hq.ne_one
  · omega

/-- **The total remainder.** -/
theorem remSumQ_sum_le {B A : ℝ} (hB : 0 < B) (hA : 0 < A)
    (hBV : ∀ᶠ x : ℕ in Filter.atTop,
      ((Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊).filter
          (fun d : ℕ => d % 2 = 1)).sum
        (fun d => (3 : ℝ) ^ d.primeFactors.card * shiftRem x d)
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (∑ q ∈ Submission.winPrimes (siftM x) (winY x),
          remSumQ x (siftM x) q (lvlD B x / (q : ℝ)))
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  filter_upwards [hBV, eventually_siftM_ge 3, eventually_ge_atTop 8] with x hbv hMs3 hBs8
  set M : ℕ := siftM x with hMdef
  set Y : ℕ := winY x with hYdef
  set L : ℝ := lvlD B x with hLdef
  set BVf : Finset ℕ := (Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊).filter
    (fun d : ℕ => d % 2 = 1) with hBVf
  set Pf : Finset (ℕ × ℕ) :=
    ((Submission.winPrimes M Y).product ((oddPrimLt M).divisors)).filter
      (fun p : ℕ × ℕ => (p.2 : ℝ) < L / (p.1 : ℝ)) with hPf
  -- every pair consists of primes/divisors with `q ≥ M`
  have hmem : ∀ p ∈ Pf, p.1.Prime ∧ M ≤ p.1 ∧ p.1 < Y ∧ p.2 ∣ oddPrimLt M ∧ (p.2 : ℝ) < L / (p.1 : ℝ) := by
    intro p hp
    rw [hPf, Finset.mem_filter] at hp
    obtain ⟨hp, hpL⟩ := hp
    have hp' : p ∈ Submission.winPrimes M Y ×ˢ (oddPrimLt M).divisors := hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp'
    obtain ⟨hqp, hq3, hqM, hqY⟩ := Submission.mem_winPrimes.mp hp1
    exact ⟨hqp, hqM, hqY, (Nat.mem_divisors.mp hp2).1, hpL⟩
  -- injectivity of `(q,d) ↦ q*d`
  have hinj : ∀ p ∈ Pf, ∀ p' ∈ Pf, p.1 * p.2 = p'.1 * p'.2 → p = p' := by
    intro p hp p' hp' heq
    obtain ⟨hqp, hqM, hqY, hpd, hpL⟩ := hmem p hp
    obtain ⟨hq'p, hq'M, hq'Y, hp'd, hp'L⟩ := hmem p' hp'
    have hdvd1 : p.1 ∣ p'.1 * p'.2 := ⟨p.2, by rw [heq]⟩
    have hq_not_dvd : ¬ (p.1 ∣ p'.2) := by
      intro hdiv
      exact absurd (prime_lt_of_dvd_oddPrimLt hqp (dvd_trans hdiv hp'd))
        (not_lt.mpr hqM)
    have hp1 : p.1 = p'.1 := by
      rcases hqp.dvd_mul.mp hdvd1 with h | h
      · rcases (Nat.dvd_prime hq'p).mp h with h' | h'
        · exact absurd h' hqp.ne_one
        · exact h'
      · exact absurd h hq_not_dvd
    have hp2 : p.2 = p'.2 := by
      have h := heq
      rw [hp1] at h
      exact Nat.mul_left_cancel (n := p'.1) hq'p.pos h
    exact Prod.ext hp1 hp2
  -- rewrite the sum over pairs
  have hsum1 : (∑ q ∈ Submission.winPrimes M Y,
        remSumQ x M q (L / (q : ℝ)))
      = ∑ p ∈ Pf, (3 : ℝ) ^ p.2.primeFactors.card * shiftRem x (p.1 * p.2) := by
    rw [hPf, Finset.sum_filter]
    rw [show ((Submission.winPrimes M Y).product ((oddPrimLt M).divisors))
        = Submission.winPrimes M Y ×ˢ (oddPrimLt M).divisors from Finset.product_eq_sprod]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [remSumQ, Finset.sum_filter]
  -- each term is `(1/3)` of the term at the modulus `q*d`
  have hsum2 : (∑ p ∈ Pf, (3 : ℝ) ^ p.2.primeFactors.card * shiftRem x (p.1 * p.2))
      = (1 / 3) * ∑ p ∈ Pf, (3 : ℝ) ^ (p.1 * p.2).primeFactors.card
          * shiftRem x (p.1 * p.2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    obtain ⟨hqp, hqM, hqY, hpd, hpL⟩ := hmem p hp
    have hcop : Nat.Coprime p.1 p.2 := coprime_winPrime_divisor hqp hqM hpd
    have hω : (p.1 * p.2).primeFactors.card = p.2.primeFactors.card + 1 := by
      have hp2ne : p.2 ≠ 0 := by
        intro h
        rw [h] at hpd
        have h0 : oddPrimLt M = 0 := eq_zero_of_zero_dvd hpd
        have hpos : 0 < oddPrimLt M := by
          rw [oddPrimLt_eq_prod_oddLt]
          exact Finset.prod_pos (fun r hr => (Submission.mem_oddLt.mp hr).1.pos)
        omega
      rw [Nat.primeFactors_mul hqp.ne_zero hp2ne, hqp.primeFactors]
      have hnotmem : p.1 ∉ p.2.primeFactors := by
        intro hmem
        have hdvd : p.1 ∣ p.2 := Nat.dvd_of_mem_primeFactors hmem
        exact absurd (prime_lt_of_dvd_oddPrimLt hqp (dvd_trans hdvd hpd)) (not_lt.mpr hqM)
      have hdisj : Disjoint ({p.1} : Finset ℕ) p.2.primeFactors := by
        rw [Finset.disjoint_left]
        intro r hr1 hr2
        rw [Finset.mem_singleton] at hr1
        exact hnotmem (hr1 ▸ hr2)
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
      omega
    rw [hω, pow_succ]
    ring
  -- pass to the image of the pair map
  have himg : (∑ p ∈ Pf, (3 : ℝ) ^ (p.1 * p.2).primeFactors.card * shiftRem x (p.1 * p.2))
      = ∑ m ∈ Pf.image (fun p : ℕ × ℕ => p.1 * p.2),
          (3 : ℝ) ^ m.primeFactors.card * shiftRem x m :=
    (Finset.sum_image (f := fun m : ℕ => (3 : ℝ) ^ m.primeFactors.card * shiftRem x m)
      hinj).symm
  -- the image is contained in the Bombieri–Vinogradov range
  have hM3 : 3 ≤ M := by rw [hMdef]; exact hMs3
  have hsub : Pf.image (fun p : ℕ × ℕ => p.1 * p.2) ⊆ BVf := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨p, hp, rfl⟩ := hm
    obtain ⟨hqp, hqM, hqY, hpd, hpL⟩ := hmem p hp
    have hp2ne : p.2 ≠ 0 := by
      intro h
      rw [h] at hpd
      have h0 : oddPrimLt M = 0 := eq_zero_of_zero_dvd hpd
      have hpos : 0 < oddPrimLt M := by
        rw [oddPrimLt_eq_prod_oddLt]
        exact Finset.prod_pos (fun r hr => (Submission.mem_oddLt.mp hr).1.pos)
      omega
    have hodd2 : p.2 % 2 = 1 := odd_of_dvd_oddPrimLt' hpd
    have hodd1 : p.1 % 2 = 1 := by
      have hp2 : p.1 ≠ 2 := by omega
      rcases hqp.eq_two_or_odd with h | h
      · exact absurd h hp2
      · exact h
    have hmulodd : (p.1 * p.2) % 2 = 1 := by
      rw [Nat.mul_mod, hodd1, hodd2]
    have hple : ((p.1 * p.2 : ℕ) : ℝ) < Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B := by
      have hqpos : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast hqp.pos
      have h1 : (p.2 : ℝ) * (p.1 : ℝ) < (L / (p.1 : ℝ)) * (p.1 : ℝ) :=
        mul_lt_mul_of_pos_right hpL hqpos
      rw [div_mul_cancel₀ _ hqpos.ne'] at h1
      have h2 : ((p.1 * p.2 : ℕ) : ℝ) = (p.2 : ℝ) * (p.1 : ℝ) := by push_cast; ring
      rw [h2]
      calc (p.2 : ℝ) * (p.1 : ℝ) < L := h1
        _ = Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B := by rw [hLdef, lvlD]
    rw [hBVf, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.pos_of_ne_zero (Nat.mul_ne_zero hqp.ne_zero hp2ne),
      Nat.le_floor (le_of_lt hple)⟩, hmulodd⟩
  have hfin : (∑ m ∈ Pf.image (fun p : ℕ × ℕ => p.1 * p.2),
        (3 : ℝ) ^ m.primeFactors.card * shiftRem x m)
      ≤ ∑ m ∈ BVf, (3 : ℝ) ^ m.primeFactors.card * shiftRem x m :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun m _ _ => mul_nonneg (by positivity) (abs_nonneg _))
  have hbv' : (∑ m ∈ BVf, (3 : ℝ) ^ m.primeFactors.card * shiftRem x m)
      ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := hbv
  rw [hsum1, hsum2, himg]
  have hsum_nonneg : (0 : ℝ) ≤ ∑ m ∈ Pf.image (fun p : ℕ × ℕ => p.1 * p.2),
      (3 : ℝ) ^ m.primeFactors.card * shiftRem x m :=
    Finset.sum_nonneg (fun m _ => mul_nonneg (by positivity) (abs_nonneg _))
  calc (1 / 3) * ∑ m ∈ Pf.image (fun p : ℕ × ℕ => p.1 * p.2),
          (3 : ℝ) ^ m.primeFactors.card * shiftRem x m
      ≤ (1 / 3) * ∑ m ∈ BVf, (3 : ℝ) ^ m.primeFactors.card * shiftRem x m :=
        mul_le_mul_of_nonneg_left hfin (by norm_num)
    _ ≤ 1 * ((x : ℝ) / (Real.log (x : ℝ)) ^ A) := by
        nlinarith [hsum_nonneg, hfin, hbv']
    _ = (x : ℝ) / (Real.log (x : ℝ)) ^ A := by ring

end

end Work.ChenPlan.H2
