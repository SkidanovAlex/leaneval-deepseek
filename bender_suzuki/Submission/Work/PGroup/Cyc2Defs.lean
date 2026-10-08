import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Cyclotomic values `Φ_n(2)` : basic interface

This file sets up the small vocabulary needed for the Zsigmondy/Bang argument that
produces, for every `k ≥ 2`, `k ≠ 6`, a prime `p` with `orderOf (2 : ZMod p) = k`.

The main object is `PhiZ n = Φ_n(2)`, the value at `2` of the `n`-th cyclotomic polynomial.

## Main results

* `PhiZ_pos`, `PhiZ_one_lt` : `0 < Φ_n(2)` and `1 < Φ_n(2)` for `2 ≤ n`.
* `PhiZ_dvd_pow_sub_one` : `Φ_n(2) ∣ 2 ^ n - 1`.
* `not_two_dvd_PhiZ` : `Φ_n(2)` is odd (for `n ≥ 1`).
* `eval_cyclotomic_eq_PhiZ` : the evaluation of `cyclotomic n (ZMod p)` at `2` is the image
  of `Φ_n(2)`.
* `orderOf_two_eq_of_dvd_PhiZ` : if `p ∣ Φ_n(2)` and `p ∤ n` (with `p` prime) then
  `orderOf (2 : ZMod p) = n`.  This is the "sufficiency" half of the primitive-prime-divisor
  correspondence.
* `PhiZ_dvd_geom` : for a prime `ℓ ∣ n`, `Φ_n(2)` divides `∑_{i<ℓ} (2^{n/ℓ})^i`.
-/

namespace Work.PGroup

/-- `PhiZ n = Φ_n(2)`, the value at `2` of the `n`-th cyclotomic polynomial, as an integer. -/
noncomputable def PhiZ (n : ℕ) : ℤ := (Polynomial.cyclotomic n ℤ).eval 2

/-- `PhiN n = Φ_n(2)`, the value at `2` of the `n`-th cyclotomic polynomial, as a natural
number (the coercion of `PhiZ n`). -/
noncomputable def PhiN (n : ℕ) : ℕ := (PhiZ n).toNat


lemma PhiZ_pos (n : ℕ) : 0 < PhiZ n :=
  Polynomial.cyclotomic_pos' n (show (1 : ℤ) < 2 by norm_num)

lemma PhiZ_one_lt {n : ℕ} (hn : 2 ≤ n) : 1 < PhiZ n := by
  have h := Polynomial.sub_one_pow_totient_lt_cyclotomic_eval (n := n) (q := 2) hn
    (show (1 : ℝ) < 2 by norm_num)
  have h2 : Polynomial.eval (2 : ℝ) (Polynomial.cyclotomic n ℝ) = (PhiZ n : ℝ) := by
    rw [PhiZ]
    simpa using Polynomial.cyclotomic.eval_apply (2 : ℤ) n (Int.castRingHom ℝ)
  rw [h2] at h
  rw [show (2 : ℝ) - 1 = 1 by norm_num, one_pow] at h
  exact_mod_cast h

lemma PhiN_cast (n : ℕ) : (PhiN n : ℤ) = PhiZ n := by
  rw [PhiN]; exact Int.toNat_of_nonneg (le_of_lt (PhiZ_pos n))

lemma PhiN_pos (n : ℕ) : 0 < PhiN n := by
  have h := PhiZ_pos n
  have hc := PhiN_cast n
  omega

lemma PhiN_one_lt {n : ℕ} (hn : 2 ≤ n) : 1 < PhiN n := by
  have h := PhiZ_one_lt hn
  have hc := PhiN_cast n
  omega

/-- Natural-number divisibility of `PhiN` is integer divisibility of `PhiZ`. -/
lemma dvd_PhiN_iff {p n : ℕ} : p ∣ PhiN n ↔ (p : ℤ) ∣ PhiZ n := by
  rw [← Int.natCast_dvd_natCast, PhiN_cast]

/-- `Φ_n(2)` divides `2 ^ n - 1`. -/
lemma PhiZ_dvd_pow_sub_one (n : ℕ) : PhiZ n ∣ (2 : ℤ) ^ n - 1 := by
  obtain ⟨Q, hQ⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one n ℤ
  refine ⟨Polynomial.eval 2 Q, ?_⟩
  have h := congrArg (Polynomial.eval (2 : ℤ)) hQ
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_mul] at h
  rw [PhiZ]
  exact h

/-- `Φ_n(2)` is odd (for `n ≥ 1`). -/
lemma not_two_dvd_PhiZ {n : ℕ} (hn : 1 ≤ n) : ¬ (2 : ℤ) ∣ PhiZ n := by
  intro h
  have h1 : (2 : ℤ) ∣ (2 : ℤ) ^ n := dvd_pow_self 2 (by omega : n ≠ 0)
  have h2 : (2 : ℤ) ∣ (2 : ℤ) ^ n - 1 := h.trans (PhiZ_dvd_pow_sub_one n)
  have h3 : (2 : ℤ) ∣ (1 : ℤ) := by
    simpa using dvd_sub h1 h2
  norm_num at h3

/-- Evaluation of `cyclotomic n (ZMod p)` at `2` is the image of `Φ_n(2)`. -/
lemma eval_cyclotomic_eq_PhiZ (n p : ℕ) :
    Polynomial.eval (2 : ZMod p) (Polynomial.cyclotomic n (ZMod p)) = ((PhiZ n : ℤ) : ZMod p) := by
  rw [← Polynomial.map_cyclotomic_int n (ZMod p), Polynomial.eval_map]
  rw [show (2 : ZMod p) = Int.castRingHom (ZMod p) (2 : ℤ) by norm_num]
  rw [Polynomial.eval₂_at_apply]
  rfl

/-- If a prime `p` divides `Φ_n(2)` and does not divide `n`, then `2` has multiplicative
order exactly `n` modulo `p`. -/
lemma orderOf_two_eq_of_dvd_PhiZ (p n : ℕ) (hp : p.Prime) (hndvd : ¬ p ∣ n)
    (hdvd : (p : ℤ) ∣ PhiZ n) : orderOf (2 : ZMod p) = n := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (n : ZMod p) := ⟨by
    intro h; rw [ZMod.natCast_eq_zero_iff] at h; exact hndvd h⟩
  have hev : Polynomial.eval (2 : ZMod p) (Polynomial.cyclotomic n (ZMod p)) = 0 := by
    rw [eval_cyclotomic_eq_PhiZ, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hdvd
  have hroot : (Polynomial.cyclotomic n (ZMod p)).IsRoot (2 : ZMod p) := hev
  have hprim : IsPrimitiveRoot (2 : ZMod p) n := (Polynomial.isRoot_cyclotomic_iff).1 hroot
  exact IsPrimitiveRoot.iff_orderOf.1 hprim

/-- For a prime `ℓ` dividing `n`, the value `Φ_n(2)` divides the geometric sum
`∑_{i<ℓ} (2^{n/ℓ})^i`.  This is the polynomial divisibility `Φ_n ∣ (X^n - 1)/(X^{n/ℓ} - 1)`
evaluated at `2`. -/
lemma PhiZ_dvd_geom {ℓ n : ℕ} (hℓ : ℓ.Prime) (hdvd : ℓ ∣ n) :
    PhiZ n ∣ ∑ i ∈ Finset.range ℓ, ((2 : ℤ) ^ (n / ℓ)) ^ i := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : PhiZ 0 = 1 := by
      rw [PhiZ, Polynomial.cyclotomic_zero, Polynomial.eval_one]
    rw [h0]; exact one_dvd _
  · have hdvd' : n / ℓ ∣ n := Nat.div_dvd_of_dvd hdvd
    have hdn : n / ℓ < n := Nat.div_lt_self hn hℓ.one_lt
    have hdprop : n / ℓ ∈ n.properDivisors := Nat.mem_properDivisors.2 ⟨hdvd', hdn⟩
    have hp1 : (Polynomial.X ^ (n / ℓ) - 1) * Polynomial.cyclotomic n ℤ ∣ Polynomial.X ^ n - 1 :=
      Polynomial.X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ hdprop
    have h1 : (Polynomial.X : Polynomial ℤ) ^ n = (Polynomial.X ^ (n / ℓ)) ^ ℓ := by
      rw [← pow_mul]; congr 1; exact (Nat.div_mul_cancel hdvd).symm
    have hX : (Polynomial.X : Polynomial ℤ) ^ n - 1
        = (Polynomial.X ^ (n / ℓ) - 1) * ∑ i ∈ Finset.range ℓ, (Polynomial.X ^ (n / ℓ)) ^ i :=
      calc (Polynomial.X : Polynomial ℤ) ^ n - 1
          = (Polynomial.X ^ (n / ℓ)) ^ ℓ - 1 := by rw [h1]
        _ = (∑ i ∈ Finset.range ℓ, (Polynomial.X ^ (n / ℓ)) ^ i) * (Polynomial.X ^ (n / ℓ) - 1) :=
              (geom_sum_mul _ _).symm
        _ = (Polynomial.X ^ (n / ℓ) - 1) * ∑ i ∈ Finset.range ℓ, (Polynomial.X ^ (n / ℓ)) ^ i := by
              ring
    rw [hX] at hp1
    obtain ⟨K, hK⟩ := hp1
    have hXne : (Polynomial.X : Polynomial ℤ) ^ (n / ℓ) - 1 ≠ 0 := by
      have hpos : 0 < n / ℓ := Nat.div_pos (Nat.le_of_dvd hn hdvd) hℓ.pos
      simpa using Polynomial.X_pow_sub_C_ne_zero hpos (1 : ℤ)
    have hcancel : Polynomial.cyclotomic n ℤ * K
        = ∑ i ∈ Finset.range ℓ, (Polynomial.X ^ (n / ℓ)) ^ i := by
      refine mul_left_cancel₀ hXne ?_
      rw [hK]; ring
    refine ⟨Polynomial.eval 2 K, ?_⟩
    have hev := congrArg (Polynomial.eval (2 : ℤ)) hcancel
    simp only [Polynomial.eval_mul, Polynomial.eval_finsetSum, Polynomial.eval_pow,
      Polynomial.eval_X] at hev
    rw [PhiZ]
    exact hev.symm

end Work.PGroup
