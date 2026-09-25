import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.vdwPrimeExistsProved

namespace NK.CFTLib.ArtinReciprocityIdeal

open Polynomial

/-- `Φ_m(0) = 1` (for `m > 1`) and `Φ_m(1) = 1` (for `m > 1` not a prime power), packaged:
evaluating `Φ_m` at `0` or at `1` gives `1`. -/
lemma eval_cyclotomic_eq_one_of_eq_zero_or_one {m : ℕ} (hm1 : 1 < m)
    (hnotpp : ∀ {r : ℕ}, Nat.Prime r → ∀ k : ℕ, r ^ k ≠ m) {R : Type*} [CommRing R]
    {x : R} (hx : x = 0 ∨ x = 1) : eval x (cyclotomic m R) = 1 := by
  rcases hx with rfl | rfl
  · rw [← coeff_zero_eq_eval_zero (cyclotomic m R), cyclotomic_coeff_zero R hm1]
  · exact eval_one_cyclotomic_not_prime_pow (R := R) hnotpp

/-- The `ℤ`-evaluation of a cyclotomic polynomial at `b`, cast to `ZMod p`, is the
`ZMod p`-evaluation at `(b : ZMod p)`. -/
lemma intCast_eval_cyclotomic (m b p : ℕ) :
    ((eval (b : ℤ) (cyclotomic m ℤ) : ℤ) : ZMod p)
      = eval (b : ZMod p) (cyclotomic m (ZMod p)) := by
  rw [← map_cyclotomic_int m (ZMod p)]
  have h : (b : ZMod p) = Int.castRingHom (ZMod p) (b : ℤ) := by
    rw [Int.coe_castRingHom]
    exact (Int.cast_natCast (R := ZMod p) b).symm
  rw [h, eval_map, eval₂_hom, Int.coe_castRingHom]

/-- If `p` divides `|Φ_m(b)|` then `(b : ZMod p)` is a root of `Φ_m` over `ZMod p`. -/
lemma eval_cyclotomic_zmod_eq_zero_of_dvd {m b p : ℕ}
    (h : p ∣ (eval (b : ℤ) (cyclotomic m ℤ)).natAbs) :
    eval (b : ZMod p) (cyclotomic m (ZMod p)) = 0 := by
  have hN : ((eval (b : ℤ) (cyclotomic m ℤ)).natAbs : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ p).2 h
  have hcast : ((eval (b : ℤ) (cyclotomic m ℤ) : ℤ) : ZMod p) = 0 := by
    rcases Int.natAbs_eq (eval (b : ℤ) (cyclotomic m ℤ)) with hh | hh
    · rw [hh, Int.cast_natCast]; exact hN
    · rw [hh, Int.cast_neg, Int.cast_natCast, hN, neg_zero]
  rw [← intCast_eval_cyclotomic]
  exact hcast

/-- **Existence of a prime whose order of `a` is divisible by a prescribed `n`.**
For `a > 1`, `n > 0` and any finite set `S` of primes there is a prime `q > a`, `q ∉ S`,
with `n ∣ orderOf (a mod q)`. -/
theorem auxiliaryPrimeOrder (a : ℕ) (ha : 1 < a) (n : ℕ) (hn : 0 < n) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    ∃ q : ℕ, q.Prime ∧ q ∉ S ∧ a < q ∧ n ∣ orderOf ((a : ZMod q)) := by
  -- We work with `m := 6 * n`, a multiple of `n` which is not a prime power.
  set m : ℕ := 6 * n with hm
  have hm1 : 1 < m := by rw [hm]; omega
  have hm0 : m ≠ 0 := by rw [hm]; omega
  have hndvdm : n ∣ m := ⟨6, by rw [hm]; ring⟩
  -- `m` is not a prime power
  have hnotpp : ∀ {r : ℕ}, Nat.Prime r → ∀ k : ℕ, r ^ k ≠ m := by
    intro r hr k hrk
    have h2 : 2 ∣ r ^ k := by rw [hrk]; exact ⟨3 * n, by rw [hm]; ring⟩
    have h3 : 3 ∣ r ^ k := by rw [hrk]; exact ⟨2 * n, by rw [hm]; ring⟩
    have hr2 : r = 2 := (hr.dvd_iff_eq (by norm_num)).1 (Nat.prime_two.dvd_of_dvd_pow h2)
    have hr3 : r = 3 := (hr.dvd_iff_eq (by norm_num)).1 (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  -- The finite set of primes to be avoided.
  set F : Finset ℕ := S ∪ (Finset.range (a + 1)).filter Nat.Prime ∪ m.primeFactors with hF
  have hFprime : ∀ q ∈ F, q.Prime := by
    intro q hq
    rw [hF, Finset.mem_union, Finset.mem_union, Finset.mem_filter] at hq
    rcases hq with (hqS | ⟨_, hqP⟩) | hqF
    · exact hS q hqS
    · exact hqP
    · exact Nat.prime_of_mem_primeFactors hqF
  -- The exponent `M` making every `q ∈ F` satisfy `q - 1 ∣ M`.
  set M : ℕ := ∏ q ∈ F, (q - 1) with hM
  have hM1 : 1 ≤ M := by
    rw [hM]
    exact Finset.one_le_prod₀ (fun q hq => by have hq' := (hFprime q hq).two_le; omega)
  have hMge : ∀ q ∈ F, q - 1 ∣ M := by
    intro q hq
    rw [hM]
    exact Finset.dvd_prod_of_mem (fun q => q - 1) hq
  -- The base point `b = a^M`.
  set b : ℕ := a ^ M with hb
  have hb2 : 2 ≤ b := by
    rw [hb]
    calc 2 ≤ a := ha
      _ = a ^ 1 := (pow_one a).symm
      _ ≤ a ^ M := Nat.pow_le_pow_right (by omega : 0 < a) hM1
  have hb1 : b ≠ 1 := by omega
  set N : ℕ := (eval (b : ℤ) (cyclotomic m ℤ)).natAbs with hN
  have hN1 : 1 < N := by
    have h := sub_one_lt_natAbs_cyclotomic_eval (n := m) (q := b) hm1 hb1
    omega
  -- `p` is the smallest prime divisor of `Φ_m(b)`.
  set p : ℕ := N.minFac with hp
  have hpprime : p.Prime := by
    rw [hp]; exact Nat.minFac_prime (by omega : N ≠ 1)
  have hpdvd : p ∣ N := by rw [hp]; exact Nat.minFac_dvd N
  haveI : Fact p.Prime := ⟨hpprime⟩
  -- The crucial point: no prime of `F` divides `Φ_m(b)`.
  have hpnotF : p ∉ F := by
    intro hpF
    have hev1 : eval (b : ZMod p) (cyclotomic m (ZMod p)) = 1 := by
      apply eval_cyclotomic_eq_one_of_eq_zero_or_one hm1 hnotpp
      by_cases hpa : p ∣ a
      · left
        have ha0 : (a : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff a p).2 hpa
        rw [hb, Nat.cast_pow, ha0, zero_pow (by omega : M ≠ 0)]
      · right
        obtain ⟨k, hk⟩ := hMge p hpF
        have ha0 : (a : ZMod p) ≠ 0 := by
          intro h
          exact hpa ((ZMod.natCast_eq_zero_iff a p).1 h)
        have hfermat : (a : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha0
        rw [hb, Nat.cast_pow, hk, pow_mul, hfermat, one_pow]
    have hev0 : eval (b : ZMod p) (cyclotomic m (ZMod p)) = 0 :=
      eval_cyclotomic_zmod_eq_zero_of_dvd (m := m) (b := b) (by rw [← hN]; exact hpdvd)
    rw [hev1] at hev0
    exact one_ne_zero hev0
  have hpgt : a < p := by
    by_contra hle
    have hle' : p ≤ a := Nat.le_of_not_lt hle
    exact hpnotF (by
      rw [hF, Finset.mem_union, Finset.mem_union, Finset.mem_filter]
      exact Or.inl (Or.inr ⟨Finset.mem_range.2 (by omega), hpprime⟩))
  have hpnotS : p ∉ S := fun h => hpnotF (by simp [hF, h])
  have hpnotdm : ¬ p ∣ m := by
    intro hpm
    exact hpnotF (by
      rw [hF, Finset.mem_union, Finset.mem_union]
      exact Or.inr ((Nat.mem_primeFactors).2 ⟨hpprime, hpm, hm0⟩))
  -- Hence `p ∤ m`, so `(m : ZMod p) ≠ 0` and `Φ_m` has a primitive root.
  haveI : NeZero (m : ZMod p) := NeZero.of_not_dvd (ZMod p) hpnotdm
  have hroot : IsRoot (cyclotomic m (ZMod p)) (b : ZMod p) := by
    rw [IsRoot.def]
    exact eval_cyclotomic_zmod_eq_zero_of_dvd (m := m) (b := b) (by rw [← hN]; exact hpdvd)
  have hprim : IsPrimitiveRoot (b : ZMod p) m := isRoot_cyclotomic_iff.1 hroot
  have hordb : orderOf (b : ZMod p) = m := hprim.eq_orderOf.symm
  have hdiv : orderOf (b : ZMod p) ∣ orderOf ((a : ZMod p)) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [hb, Nat.cast_pow, ← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  rw [hordb] at hdiv
  exact ⟨p, hpprime, hpnotS, hpgt, hndvdm.trans hdiv⟩

end NK.CFTLib.ArtinReciprocityIdeal
