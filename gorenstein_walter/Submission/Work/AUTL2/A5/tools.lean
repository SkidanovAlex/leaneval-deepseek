/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA AUTL2 / A5 : field-theoretic tools for the odd-index lemma

This file collects the finite-field facts used by `Work.AUTL2.A5.odd_index`:

* `isSquare_of_pow_eq_one_of_dvd` : an element of `GF(p^k)` whose order divides `(p^k-1)/2`
  is a square;
* `pow_pow_mod` : `x ^ p ^ i` only depends on `i % k` in `GF(p^k)`;
* `sigma_pow_repr` : an order-two automorphism `σ ≠ 1` of `GF(p^k)` is the `(k/2)`-th
  Frobenius power: `k` is even and `σ x = x ^ p ^ (k/2)`;
* `norm_one_isSquare` : if `y * σ y = 1` then `y` is a square.
-/
import Mathlib
import Submission.Work.AUTL2.Defs
import Submission.Work.AUTL2.Mobius
import Submission.Work.AUTL2.Stabilizer
import Submission.Work.AUTL2.Galois.decomposition
import Submission.Work.AUTL2.Norm.square

open scoped MatrixGroups

set_option linter.style.haveILetI false

namespace Work.AUTL2.A5

/-! ## Squares in `GF(p^k)` -/

/-- An element of `GF(p^k)` (`p` odd, `p^k ≥ 5`) whose order divides `(p^k-1)/2` is a square. -/
theorem isSquare_of_pow_eq_one_of_dvd (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k)
    {x : GaloisField p k} {m : ℕ} (hm : m ∣ p ^ k / 2) (h : x ^ m = 1) : IsSquare x := by
  have hk : k ≠ 0 := by rintro rfl; simp at hq
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p k) = p ^ k := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p k hk]
  have hhalf : p ^ k / 2 = (p ^ k - 1) / 2 := by
    have hodd : p ^ k % 2 = 1 := Nat.odd_iff.mp (Odd.pow hp)
    omega
  have hchar : ringChar (GaloisField p k) ≠ 2 := by
    have hp2 : p ≠ 2 := by
      intro h2
      have := hp
      rw [h2] at this
      exact (by decide : ¬ Odd 2) this
    haveI : CharP (GaloisField p k) p := inferInstance
    rw [ringChar.eq (GaloisField p k) p]
    exact hp2
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by simp⟩
  · rw [FiniteField.isSquare_iff hchar hx0, hcard, hhalf]
    obtain ⟨t, ht⟩ := hm
    rw [hhalf] at ht
    have h1 : x ^ ((p ^ k - 1) / 2) = (x ^ m) ^ t := by rw [ht, pow_mul]
    have h2 : (x ^ m) ^ t = 1 := by rw [h, one_pow]
    rw [h1, h2]

/-! ## Frobenius powers -/

/-- `x ^ p ^ k = x` in `GF(p^k)`. -/
theorem pow_pow_card (p k : ℕ) [Fact p.Prime] (x : GaloisField p k) : x ^ p ^ k = x := by
  match k with
  | 0 => simp
  | (k + 1) =>
    haveI : Fintype (GaloisField p (k + 1)) := Fintype.ofFinite _
    have hcard : Fintype.card (GaloisField p (k + 1)) = p ^ (k + 1) := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card p (k + 1) (Nat.succ_ne_zero k)]
    rw [← hcard]; exact FiniteField.pow_card x

/-- `y ^ (p ^ k) ^ n = y` in `GF(p^k)`. -/
theorem pow_pow_card_pow (p k n : ℕ) [Fact p.Prime] (y : GaloisField p k) :
    y ^ (p ^ k) ^ n = y := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_mul, ih, pow_pow_card]

/-- `x ^ p ^ (j + k) = x ^ p ^ j` in `GF(p^k)`. -/
theorem pow_pow_add_card (p k j : ℕ) [Fact p.Prime] (x : GaloisField p k) :
    x ^ p ^ (j + k) = x ^ p ^ j := by
  rw [pow_add, pow_mul, pow_pow_card]

/-- `x ^ p ^ i` only depends on `i % k` in `GF(p^k)`. -/
theorem pow_pow_mod (p k i : ℕ) [Fact p.Prime] (x : GaloisField p k) :
    x ^ p ^ i = x ^ p ^ (i % k) := by
  have h : i = i % k + k * (i / k) := (Nat.mod_add_div i k).symm
  conv_lhs => rw [h]
  rw [show p ^ (i % k + k * (i / k)) = p ^ (i % k) * (p ^ k) ^ (i / k) from by
    rw [pow_add, pow_mul], pow_mul, pow_pow_card_pow]

/-! ## `σ` is a Frobenius power -/

/-- An order-two automorphism `σ ≠ 1` of `GF(p^k)` is the `(k/2)`-th Frobenius power. -/
theorem sigma_pow_repr (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k)
    (σ : GaloisField p k ≃+* GaloisField p k) (hσ : σ * σ = 1) (hne : σ ≠ 1) :
    ∃ i : ℕ, 2 * i = k ∧ ∀ x : GaloisField p k, σ x = x ^ p ^ i := by
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hq; simp at hq
    · exact h
  have hf : ∀ x : ZMod p, σ (algebraMap (ZMod p) (GaloisField p k) x) =
      algebraMap (ZMod p) (GaloisField p k) x := by
    intro x
    have hx : ((x.val : ℕ) : ZMod p) = x := ZMod.natCast_zmod_val x
    have e : algebraMap (ZMod p) (GaloisField p k) x = ((x.val : ℕ) : GaloisField p k) := by
      conv_lhs => rw [← hx]
      exact map_natCast (algebraMap (ZMod p) (GaloisField p k)) x.val
    rw [e]
    exact map_natCast σ x.val
  let σA : GaloisField p k ≃ₐ[ZMod p] GaloisField p k := AlgEquiv.ofRingEquiv (f := σ) hf
  have hσA2 : σA * σA = 1 := by
    ext x
    rw [AlgEquiv.mul_apply]
    rw [show σA (σA x) = σ (σA x) from AlgEquiv.ofRingEquiv_apply hf (σA x)]
    rw [show σA x = σ x from AlgEquiv.ofRingEquiv_apply hf x]
    have h := congrArg (fun e : GaloisField p k ≃+* GaloisField p k => e x) hσ
    simpa using h
  have hσAne : σA ≠ 1 := by
    intro h
    apply hne
    ext x
    have h' := congrArg (fun e : GaloisField p k ≃ₐ[ZMod p] GaloisField p k => e x) h
    rw [show σA x = σ x from AlgEquiv.ofRingEquiv_apply hf x] at h'
    simpa using h'
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod p) p (GaloisField p k) σA
  have hi' : ∀ x, σA x = x ^ p ^ i := by
    intro x
    have := hi x
    simp only [Nat.card_zmod] at this
    exact this
  set φ : GaloisField p k ≃ₐ[ZMod p] GaloisField p k :=
    FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) (GaloisField p k) with hφdef
  have hφp : ∀ x, φ x = x ^ p := by
    intro x
    rw [hφdef]
    have := congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic (ZMod p)
      (GaloisField p k)) x
    simpa [ZMod.card p] using this
  have hφord : orderOf φ = k := by
    rw [hφdef, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
      GaloisField.finrank p hk.ne']
  have hφpow : ∀ (n : ℕ) (x : GaloisField p k), (φ ^ n) x = x ^ p ^ n := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, AlgEquiv.mul_apply, ih, hφp, ← pow_mul]
      congr 1
      rw [pow_succ']
  have hφi : σA = φ ^ i := by
    ext x
    rw [hi' x, hφpow]
  have hkdvd : k ∣ 2 * i := by
    rw [← hφord, orderOf_dvd_iff_pow_eq_one]
    exact show φ ^ (2 * i) = 1 by
      rw [show 2 * i = i + i from by ring, pow_add, ← hφi, hσA2]
  have hkndvd : ¬ k ∣ i := by
    intro hd
    apply hσAne
    rw [hφi]
    exact orderOf_dvd_iff_pow_eq_one.mp (hφord.symm ▸ hd)
  have hjlt : i % k < k := Nat.mod_lt _ hk
  have hjne : i % k ≠ 0 := by
    intro h0
    exact hkndvd (Nat.dvd_of_mod_eq_zero h0)
  have hjdvd : k ∣ 2 * (i % k) := by
    have hsplit : 2 * i = 2 * (i % k) + k * (2 * (i / k)) := by
      have h := Nat.mod_add_div i k
      calc 2 * i = 2 * (i % k + k * (i / k)) := by rw [h]
        _ = 2 * (i % k) + 2 * (k * (i / k)) := by ring
        _ = 2 * (i % k) + k * (2 * (i / k)) := by ring
    have hsum : 2 * (i % k) + k * (2 * (i / k)) = k * (2 * (i / k)) + 2 * (i % k) := by
      ring
    rw [hsplit, hsum] at hkdvd
    exact (Nat.dvd_add_iff_right (dvd_mul_right k _)).mpr hkdvd
  refine ⟨i % k, ?_, fun x => ?_⟩
  · obtain ⟨c, hc⟩ := hjdvd
    have hc1 : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · exfalso
        rw [h, mul_zero] at hc
        rcases Nat.mul_eq_zero.mp hc with h' | h'
        · exact absurd h' (by norm_num)
        · exact hjne h'
      · exact h
    have hc2 : c < 2 := by
      have h1 : k * c = 2 * (i % k) := hc.symm
      have h2 : 2 * (i % k) < 2 * k := Nat.mul_lt_mul_of_pos_left hjlt (by norm_num)
      have h3 : k * c < k * 2 := by rw [h1, mul_comm k 2]; exact h2
      exact (Nat.mul_lt_mul_left hk).mp h3
    have hc3 : c = 1 := by omega
    rw [hc3, mul_one] at hc
    exact hc
  · rw [show σ x = σA x from (AlgEquiv.ofRingEquiv_apply hf x).symm, hi' x, pow_pow_mod]

/-- If `y * σ y = 1` (`σ` an order-two automorphism of `GF(p^k)`, `σ ≠ 1`) then `y` is a
square. -/
theorem norm_one_isSquare (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k)
    (σ : GaloisField p k ≃+* GaloisField p k) (hσ : σ * σ = 1) (hne : σ ≠ 1)
    {y : GaloisField p k} (h : y * σ y = 1) : IsSquare y := by
  obtain ⟨i, h2i, hi⟩ := sigma_pow_repr p k hp hq σ hσ hne
  have hy : y ^ (1 + p ^ i) = 1 := by
    rw [pow_add, pow_one, ← hi y, h]
  refine isSquare_of_pow_eq_one_of_dvd p k hp hq (m := 1 + p ^ i) ?_ hy
  have hkey : p ^ k = p ^ (2 * i) := by rw [h2i]
  rw [hkey]
  have hpodd : Odd (p ^ i) := Odd.pow hp
  have hhalf : p ^ (2 * i) / 2 = (p ^ (2 * i) - 1) / 2 := by
    have := Nat.odd_iff.mp (Odd.pow hp : Odd (p ^ (2 * i)))
    omega
  rw [hhalf]
  have heven : 2 ∣ p ^ i - 1 := by
    have := Nat.odd_iff.mp hpodd
    omega
  obtain ⟨s, hs⟩ := heven
  have hsq : p ^ (2 * i) = (p ^ i) ^ 2 := by rw [← pow_mul, mul_comm]
  have hp2 : (p ^ i) ^ 2 - 1 = (p ^ i - 1) * (p ^ i + 1) := by
    have h := Nat.sq_sub_sq (p ^ i) 1
    rw [one_pow, mul_comm] at h
    exact h
  have hval : (p ^ (2 * i) - 1) / 2 = s * (1 + p ^ i) := by
    rw [hsq, hp2, hs, add_comm (p ^ i) 1]
    rw [show (2 * s) * (1 + p ^ i) / 2 = s * (1 + p ^ i) from by
      rw [mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]]
  rw [hval]
  exact ⟨s, by ring⟩

end Work.AUTL2.A5
