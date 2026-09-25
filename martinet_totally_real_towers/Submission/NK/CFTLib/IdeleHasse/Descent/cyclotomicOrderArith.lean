import Mathlib

/-!
# The arithmetic seed of the local condition

For `a > 1` and `m > 0` there is a prime `q` with `m ∣ orderOf (a : ZMod q)`.  This is the
existence statement needed to build the cyclic cyclotomic extension `M = K(ζ_q)` of Milne's
Lemma VII.7.3 with prescribed local degree at a given finite place: if `a = N Q` is the absolute
norm of the place and `q ∤ N Q`, then `Gal(K(ζ_q)/K) ↪ (ZMod q)ˣ` is cyclic and the local degree
at `w | Q` is `orderOf (N Q : ZMod q)`, so choosing `q` with `n ∣ orderOf (N Q : ZMod q)` gives
`n ∣ [M_w : K_Q]`.

## The construction (Zsigmondy-type, avoiding the prime-power exceptions)

The earlier pieces of the workspace provide `ℓ ^ r ∣ orderOf (a : ZMod p)` for a *single* prime
power `ℓ ^ r` (van der Waerden/Lang: `NK.CFTLib.ArtinReciprocityIdeal.vdwPrimeExistsProved`).
For a general modulus `m` we use the cyclotomic polynomial instead: take
`N := m * p₁ * p₂` with two distinct primes `p₁, p₂ > max a m`, so that `N` is *not* a prime
power and hence `eval 1 (cyclotomic N ℤ) = 1` (`Polynomial.eval_one_cyclotomic_not_prime_pow`);
put `M := ∏_{p | N * a} (p - 1)` (so that every prime `p | N` divides `a ^ M - 1` if `p ∤ a`),
`b := a ^ M`, and let `q` be a prime divisor of `|Φ_N(b)|` — which is `> 1` by
`Polynomial.sub_one_lt_natAbs_cyclotomic_eval`.  Every prime `p | N` fails to divide `Φ_N(b)`
(if `p ∤ a` because `b ≡ 1 (mod p)` and `Φ_N(1) = 1`; if `p | a` because `b ≡ 0` and
`Φ_N(0) = coeff 0 = 1`), so `q ∤ N`; hence `N = orderOf (b : ZMod q) ∣ orderOf (a : ZMod q)`
(primitivity of `b` in `ZMod q` and `orderOf_pow_dvd`), and `m ∣ N`.

Everything here is pure number theory, with no number-field input. -/

open Polynomial

set_option maxHeartbeats 800000

namespace NK.CFTLib.IdeleHasse.Descent

/-- **The arithmetic seed**: for `a > 1` and `m > 0` there is a prime `q` with
`m ∣ orderOf (a : ZMod q)`. -/
theorem exists_prime_orderOf_dvd (a m : ℕ) (ha : 1 < a) (hm : 0 < m) :
    ∃ q : ℕ, q.Prime ∧ m ∣ orderOf (a : ZMod q) := by
  obtain ⟨p₁, hp₁, hpp₁⟩ := Nat.exists_infinite_primes (max a m + 1)
  obtain ⟨p₂, hp₂, hpp₂⟩ := Nat.exists_infinite_primes (max (max a m + 1) p₁ + 1)
  have hp₁' : max a m < p₁ := by omega
  have hp₂' : p₁ < p₂ := by omega
  set N : ℕ := m * p₁ * p₂ with hN
  have hp₁2 : 2 ≤ p₁ := by omega
  have hp₂2 : 2 ≤ p₂ := by omega
  have hNpos : 0 < N := by rw [hN]; positivity
  have hp₁N : p₁ ∣ N := ⟨m * p₂, by rw [hN]; ring⟩
  have hp₂N : p₂ ∣ N := ⟨m * p₁, by rw [hN]; ring⟩
  have hNge : 2 ≤ N := by
    have h1 : 2 ≤ p₁ * p₂ := by nlinarith [hp₁2, hp₂2]
    calc 2 = 1 * 2 := by norm_num
      _ ≤ m * (p₁ * p₂) := Nat.mul_le_mul (by omega) h1
      _ = N := by rw [hN]; ring
  have hNne : N ≠ 1 := by omega
  have hN2 : 1 < N := by omega
  have hp₁p₂ : p₁ ≠ p₂ := by omega
  have hNotPP : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ k ≠ N := by
    intro p hp k hk
    have h1 : p₁ ∣ p := hpp₁.dvd_of_dvd_pow (by rw [hk]; exact hp₁N)
    have h2 : p₂ ∣ p := hpp₂.dvd_of_dvd_pow (by rw [hk]; exact hp₂N)
    have e1 : p₁ = p := (Nat.prime_dvd_prime_iff_eq hpp₁ hp).mp h1
    have e2 : p₂ = p := (Nat.prime_dvd_prime_iff_eq hpp₂ hp).mp h2
    omega
  set M : ℕ := (N * a).primeFactors.prod (fun p => p - 1) with hM
  have hMfact : ∀ p, p.Prime → p ∣ N * a → (p - 1) ∣ M := by
    intro p hp hpdvd
    exact Finset.dvd_prod_of_mem _ (Nat.Prime.mem_primeFactors hp hpdvd (by positivity))
  have hMpos : 0 < M := by
    rw [hM]
    have hmem : p₁ ∈ (N * a).primeFactors :=
      Nat.Prime.mem_primeFactors hpp₁ (Dvd.dvd.mul_right hp₁N a) (by positivity)
    exact Finset.prod_pos (fun p hp => by
      have := Nat.Prime.two_le ((Nat.mem_primeFactors.mp hp).1)
      omega)
  set b : ℕ := a ^ M with hb
  have hb2 : 2 ≤ b := by
    rw [hb]
    calc 2 ≤ a := ha
      _ = a ^ 1 := (pow_one a).symm
      _ ≤ a ^ M := Nat.pow_le_pow_right (by omega) hMpos
  have hb1 : b ≠ 1 := by omega
  have hbP : ∀ p, p.Prime → p ∣ N → p ∣ a → p ∣ b := by
    intro p hp hpN hpa
    rw [hb]
    exact dvd_pow hpa (by omega)
  have hbM : ∀ p, p.Prime → p ∣ N → ¬ p ∣ a → (a : ZMod p) ^ M = 1 := by
    intro p hp hpN hpa
    obtain ⟨s, hs⟩ := hMfact p hp (Dvd.dvd.mul_right hpN a)
    haveI : Fact p.Prime := ⟨hp⟩
    have hne : (a : ZMod p) ≠ 0 := by
      intro h0
      exact hpa ((CharP.cast_eq_zero_iff (ZMod p) p a).mp h0)
    calc (a : ZMod p) ^ M = (a : ZMod p) ^ ((p - 1) * s) := by rw [hs]
      _ = ((a : ZMod p) ^ (p - 1)) ^ s := by rw [pow_mul]
      _ = 1 := by rw [ZMod.pow_card_sub_one_eq_one hne, one_pow]
  set Φ : ℕ := ((cyclotomic N ℤ).eval ((b : ℤ))).natAbs with hΦ
  have hΦ1 : 1 < Φ := by
    have h := sub_one_lt_natAbs_cyclotomic_eval (n := N) (q := b) hN2 hb1
    rw [hΦ]
    omega
  set q : ℕ := Φ.minFac with hq
  have hqprime : q.Prime := Nat.minFac_prime (by omega)
  have hqΦ : q ∣ Φ := Nat.minFac_dvd Φ
  have hmapΦ : ∀ p : ℕ, [Fact p.Prime] →
      ((((cyclotomic N ℤ).eval ((b : ℤ)) : ℤ) : ZMod p) =
        (cyclotomic N (ZMod p)).eval (((b : ℤ) : ZMod p))) := by
    intro p _
    rw [← map_cyclotomic_int N (ZMod p), eval_intCast_map, Int.coe_castRingHom,
      Int.cast_natCast]
  have hbad : ∀ p, p.Prime → p ∣ N → ¬ p ∣ Φ := by
    intro p hp hpN hpdvdΦ
    haveI : Fact p.Prime := ⟨hp⟩
    have hpz : (p : ℤ) ∣ (cyclotomic N ℤ).eval ((b : ℤ)) := by
      have h1 : (p : ℤ) ∣ (Φ : ℤ) := by exact_mod_cast hpdvdΦ
      rw [hΦ] at h1
      exact Int.dvd_natAbs.mp h1
    have hz : (((cyclotomic N ℤ).eval ((b : ℤ)) : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hpz
    rw [hmapΦ p] at hz
    by_cases hpa : p ∣ a
    · have hbz : (((b : ℤ) : ZMod p)) = 0 := by
        have hbdvd : (p : ℤ) ∣ (b : ℤ) := by exact_mod_cast hbP p hp hpN hpa
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd (b : ℤ) p).mpr hbdvd
      rw [hbz, ← coeff_zero_eq_eval_zero, cyclotomic_coeff_zero (ZMod p) hN2] at hz
      exact one_ne_zero hz
    · have hbz : (((b : ℤ) : ZMod p)) = 1 := by
        have h1 : (a : ZMod p) ^ M = 1 := hbM p hp hpN hpa
        have h2 : (((b : ℤ) : ZMod p)) = (a : ZMod p) ^ M := by
          rw [hb]
          push_cast
          ring
        rw [h2, h1]
      rw [hbz, eval_one_cyclotomic_not_prime_pow (R := ZMod p) (fun hp' k => hNotPP hp' k)] at hz
      exact one_ne_zero hz
  have hqN : ¬ q ∣ N := fun h => hbad q hqprime h hqΦ
  haveI : Fact q.Prime := ⟨hqprime⟩
  haveI : NeZero (N : ZMod q) := NeZero.of_not_dvd (ZMod q) hqN
  have hroot : (cyclotomic N (ZMod q)).IsRoot (b : ZMod q) := by
    rw [IsRoot.def]
    have hpz : (q : ℤ) ∣ (cyclotomic N ℤ).eval ((b : ℤ)) := by
      have h1 : (q : ℤ) ∣ (Φ : ℤ) := by exact_mod_cast hqΦ
      rw [hΦ] at h1
      exact Int.dvd_natAbs.mp h1
    have hzq : ((((cyclotomic N ℤ).eval ((b : ℤ)) : ℤ) : ZMod q)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hpz
    rw [hmapΦ q] at hzq
    rw [show (b : ZMod q) = (((b : ℤ)) : ZMod q) from by rw [Int.cast_natCast]]
    exact hzq
  have hprim : IsPrimitiveRoot (b : ZMod q) N := (isRoot_cyclotomic_iff).mp hroot
  have hordb : orderOf (b : ZMod q) = N := (hprim.eq_orderOf).symm
  have hdvdb : orderOf (b : ZMod q) ∣ orderOf (a : ZMod q) := by
    have hbe : (b : ZMod q) = (a : ZMod q) ^ M := by rw [hb, Nat.cast_pow]
    rw [hbe]
    exact orderOf_pow_dvd M
  have hNdvd : N ∣ orderOf (a : ZMod q) := hordb ▸ hdvdb
  have hmN : m ∣ N := ⟨p₁ * p₂, by rw [hN]; ring⟩
  exact ⟨q, hqprime, hmN.trans hNdvd⟩

end NK.CFTLib.IdeleHasse.Descent
