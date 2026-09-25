import Mathlib

namespace NK.CFTLib.ARL

/-- Auxiliary arithmetic fact: if `ℓ` is prime and `x ^ (ℓ ^ k) = 1` in `ZMod ℓ`, then `x = 1`.
In other words, the group `(ZMod ℓ)ˣ` (of order `ℓ - 1`, coprime to `ℓ`) has no element of
`ℓ`-power order except `1`.  The proof is an induction on `k`, using Fermat's little theorem in
the form `y ^ ℓ = y` in `ZMod ℓ`. -/
lemma eq_one_of_pow_prime_pow_eq_one {ℓ : ℕ} (hℓ : ℓ.Prime) (k : ℕ) {x : ZMod ℓ}
    (h : x ^ (ℓ ^ k) = 1) : x = 1 := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      have hfl : Fact ℓ.Prime := ⟨hℓ⟩
      rw [pow_succ, pow_mul, ZMod.pow_card] at h
      exact ih h

/-- **Existence of a prime `p` whose residue class of `a` has order divisible by `ℓ ^ E`.**

For `a ≥ 2`, `ℓ` prime, `E ≥ 1` and `a ≢ 1 (mod ℓ)`, there is a prime `p` with
`p ∤ a`, `ℓ ^ E ∣ orderOf (a mod p)`, and `ℓ ^ E < p`.

The proof takes the cyclotomic value `Φ = ∑_{i < ℓ} b ^ i` with `b = a ^ (ℓ ^ (E - 1))`, so that
`Φ * (b - 1) = a ^ (ℓ ^ E) - 1`.  The hypothesis `a ≢ 1 (mod ℓ)` guarantees that `Φ > 1` and that
no prime divisor of `Φ` divides `b - 1`; hence a prime `p ∣ Φ` satisfies `(a mod p) ^ (ℓ ^ E) = 1`
and `(a mod p) ^ (ℓ ^ (E - 1)) ≠ 1`, which forces `orderOf (a mod p) = ℓ ^ E`.  Finally
`orderOf (a mod p) ∣ p - 1` gives `ℓ ^ E < p`. -/
theorem exists_prime_dvd_orderOf_not_modEq_one (a ℓ E : ℕ) (ha : 2 ≤ a) (hℓ : ℓ.Prime) (hE : 1 ≤ E)
    (h : ¬ a ≡ 1 [MOD ℓ]) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ a ∧ ℓ ^ E ∣ orderOf ((a : ZMod p)) ∧ ℓ ^ E < p := by
  set b : ℕ := a ^ (ℓ ^ (E - 1)) with hb
  set Φ : ℕ := ∑ i ∈ Finset.range ℓ, b ^ i with hΦ
  have hb2 : 2 ≤ b := by
    rw [hb]
    calc 2 ≤ a := ha
      _ = a ^ 1 := (pow_one a).symm
      _ ≤ a ^ (ℓ ^ (E - 1)) := Nat.pow_le_pow_right (by omega) (Nat.one_le_pow _ _ hℓ.pos)
  have hb1 : 1 ≤ b := le_trans (by omega : 1 ≤ 2) hb2
  have hΦ2 : 2 ≤ Φ := by
    have h1mem : 1 ∈ Finset.range ℓ := Finset.mem_range.mpr hℓ.one_lt
    have hle : b ^ 1 ≤ Φ := by
      rw [hΦ]
      exact Finset.single_le_sum (fun i _ => Nat.zero_le _) h1mem
    calc 2 ≤ b ^ 1 := by simpa using hb2
      _ ≤ Φ := hle
  obtain ⟨p, hp_prime, hp_dvd_Φ⟩ := Nat.exists_prime_and_dvd (by omega : Φ ≠ 1)
  have hfp : Fact p.Prime := ⟨hp_prime⟩
  have hΦ0 : (Φ : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p Φ).mpr hp_dvd_Φ
  have hΦsum : (Φ : ZMod p) = ∑ i ∈ Finset.range ℓ, (b : ZMod p) ^ i := by
    rw [hΦ]; push_cast; rfl
  have hgeomZ : (b : ZMod p) ^ ℓ = 1 := by
    have hg := geom_sum_mul (b : ZMod p) ℓ
    rw [← hΦsum, hΦ0, zero_mul] at hg
    exact sub_eq_zero.mp hg.symm
  have hbcast : (b : ZMod p) = (a : ZMod p) ^ (ℓ ^ (E - 1)) := by rw [hb]; push_cast; rfl
  have hxpow : (a : ZMod p) ^ (ℓ ^ E) = 1 := by
    have hbc : (b : ZMod p) ^ ℓ = (a : ZMod p) ^ (ℓ ^ E) := by
      rw [hbcast, ← pow_mul]
      congr 1
      rw [← pow_succ, Nat.sub_add_cancel hE]
    rwa [hbc] at hgeomZ
  have hxne0 : (a : ZMod p) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (pow_ne_zero E hℓ.pos.ne')] at hxpow
    exact one_ne_zero hxpow.symm
  have hp_not_dvd_a : ¬ p ∣ a := by
    intro hpa
    exact hxne0 ((CharP.cast_eq_zero_iff (ZMod p) p a).mpr hpa)
  have hp_not_dvd_bm1 : ¬ p ∣ b - 1 := by
    intro hpdvd
    have hb_eq : (b : ZMod p) = 1 := by
      have h0 : ((b - 1 : ℕ) : ZMod p) = 0 :=
        (CharP.cast_eq_zero_iff (ZMod p) p (b - 1)).mpr hpdvd
      have h0' : (b : ZMod p) - 1 = 0 := by rw [Nat.cast_sub hb1] at h0; simpa using h0
      exact sub_eq_zero.mp h0'
    have hΦℓ : (Φ : ZMod p) = (ℓ : ZMod p) := by
      rw [hΦsum]
      simp [hb_eq]
    have hℓ0 : (ℓ : ZMod p) = 0 := by rw [← hΦℓ]; exact hΦ0
    have hp_dvd_ℓ : p ∣ ℓ := (CharP.cast_eq_zero_iff (ZMod p) p ℓ).mp hℓ0
    have hp_eq : p = ℓ := ((Nat.Prime.dvd_iff_eq hℓ hp_prime.ne_one).mp hp_dvd_ℓ).symm
    have hℓdvd : ℓ ∣ b - 1 := hp_eq ▸ hpdvd
    have hbeq : (b : ZMod ℓ) = 1 := by
      have h0 : ((b - 1 : ℕ) : ZMod ℓ) = 0 :=
        (CharP.cast_eq_zero_iff (ZMod ℓ) ℓ (b - 1)).mpr hℓdvd
      have h0' : (b : ZMod ℓ) - 1 = 0 := by rw [Nat.cast_sub hb1] at h0; simpa using h0
      exact sub_eq_zero.mp h0'
    have hpow1 : (a : ZMod ℓ) ^ (ℓ ^ (E - 1)) = 1 := by
      have hx : ((a ^ (ℓ ^ (E - 1)) : ℕ) : ZMod ℓ) = 1 := by rw [← hb]; exact hbeq
      simpa using hx
    have haeq1 : (a : ZMod ℓ) = 1 := eq_one_of_pow_prime_pow_eq_one hℓ (E - 1) hpow1
    have hmod : a ≡ 1 [MOD ℓ] := by
      rw [← Nat.cast_one] at haeq1
      exact (ZMod.natCast_eq_natCast_iff a 1 ℓ).mp haeq1
    exact h hmod
  have hxne : (a : ZMod p) ^ (ℓ ^ (E - 1)) ≠ 1 := by
    intro hcontra
    apply hp_not_dvd_bm1
    have hb_eq : (b : ZMod p) = 1 := by
      have hx : ((a ^ (ℓ ^ (E - 1)) : ℕ) : ZMod p) = 1 := by simpa using hcontra
      rw [hb]
      exact hx
    have h0 : ((b - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub hb1]
      simp [hb_eq]
    exact (CharP.cast_eq_zero_iff (ZMod p) p (b - 1)).mp h0
  have hxpow_dvd : orderOf ((a : ZMod p)) ∣ ℓ ^ E := orderOf_dvd_iff_pow_eq_one.mpr hxpow
  have hℓE_dvd_ord : ℓ ^ E ∣ orderOf ((a : ZMod p)) := by
    rw [Nat.dvd_prime_pow hℓ] at hxpow_dvd
    obtain ⟨k, hkE, hk⟩ := hxpow_dvd
    have hkEq : k = E := by
      by_contra hne
      have hlt : k < E := lt_of_le_of_ne hkE hne
      have hdvd' : orderOf ((a : ZMod p)) ∣ ℓ ^ (E - 1) := by
        rw [hk]; exact pow_dvd_pow ℓ (by omega)
      exact hxne (orderOf_dvd_iff_pow_eq_one.mp hdvd')
    rw [hk, hkEq]
  have hdvd_pm1 : ℓ ^ E ∣ p - 1 := dvd_trans hℓE_dvd_ord (ZMod.orderOf_dvd_card_sub_one hxne0)
  have hlt : ℓ ^ E < p := by
    have hpos : 0 < p - 1 := Nat.sub_pos_of_lt hp_prime.one_lt
    have hle : ℓ ^ E ≤ p - 1 := Nat.le_of_dvd hpos hdvd_pm1
    exact lt_of_le_of_lt hle (Nat.sub_one_lt hp_prime.ne_zero)
  exact ⟨p, hp_prime, hp_not_dvd_a, hℓE_dvd_ord, hlt⟩

end NK.CFTLib.ARL
