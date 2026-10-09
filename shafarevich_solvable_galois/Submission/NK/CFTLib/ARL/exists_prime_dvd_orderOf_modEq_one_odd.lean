import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib.ARL

/-- Binomial truncation: if `y ^ 2 = 0` then `(1 + y) ^ n = 1 + n * y`. -/
lemma pow_add_one_eq_of_sq_eq_zero {R : Type*} [CommRing R] (y : R) (hy : y ^ 2 = 0) (n : ℕ) :
    (1 + y) ^ n = 1 + (n : R) * y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    have hyy : y * y = 0 := by rw [← pow_two]; exact hy
    calc (1 + (n : R) * y) * (1 + y)
        = 1 + (n : R) * y + y + (n : R) * (y * y) := by ring
      _ = 1 + (n : R) * y + y + 0 := by rw [hyy, mul_zero]
      _ = 1 + ((n + 1 : ℕ) : R) * y := by push_cast; ring

/-- Arithmetic core: for `a ≡ 1 (mod ℓ)` with `ℓ` an odd prime, the cyclotomic-type value
`Φ = ∑_{i < ℓ} (a ^ (ℓ ^ (E-1))) ^ i` is divisible by `ℓ` but not by `ℓ ^ 2`.  The proof
computes `Φ ≡ ℓ (mod ℓ ^ 2)` inside `ZMod (ℓ ^ 2)`. -/
lemma not_dvd_sq_geom_sum (a ℓ E : ℕ) (hℓ : ℓ.Prime) (hodd : Odd ℓ) (hE : 1 ≤ E)
    (h : a ≡ 1 [MOD ℓ]) :
    ¬ ℓ ^ 2 ∣ ∑ i ∈ Finset.range ℓ, (a ^ (ℓ ^ (E - 1))) ^ i := by
  have hmod : a % ℓ = 1 := by
    have h1 : a % ℓ = 1 % ℓ := h
    rw [Nat.mod_eq_of_lt hℓ.one_lt] at h1
    exact h1
  have ha_eq : a = ℓ * (a / ℓ) + 1 := by
    have h' := Nat.div_add_mod a ℓ
    omega
  have hcast : (a : ZMod (ℓ ^ 2)) =
      1 + (ℓ : ZMod (ℓ ^ 2)) * ((a / ℓ : ℕ) : ZMod (ℓ ^ 2)) := by
    conv_lhs => rw [ha_eq]
    push_cast
    ring
  let L : ZMod (ℓ ^ 2) := (ℓ : ZMod (ℓ ^ 2)) * ((a / ℓ : ℕ) : ZMod (ℓ ^ 2))
  have hL2 : L ^ 2 = 0 := by
    show ((ℓ : ZMod (ℓ ^ 2)) * ((a / ℓ : ℕ) : ZMod (ℓ ^ 2))) ^ 2 = 0
    rw [mul_pow]
    have h : (ℓ : ZMod (ℓ ^ 2)) ^ 2 = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [h, zero_mul]
  let Y : ZMod (ℓ ^ 2) := ((ℓ ^ E : ℕ) : ZMod (ℓ ^ 2)) * ((a / ℓ : ℕ) : ZMod (ℓ ^ 2))
  have hY2 : Y ^ 2 = 0 := by
    show (((ℓ ^ E : ℕ) : ZMod (ℓ ^ 2)) * ((a / ℓ : ℕ) : ZMod (ℓ ^ 2))) ^ 2 = 0
    rw [mul_pow]
    have h : (((ℓ ^ E : ℕ) : ZMod (ℓ ^ 2))) ^ 2 = 0 := by
      rw [← Nat.cast_pow, CharP.cast_eq_zero_iff (ZMod (ℓ ^ 2)) (ℓ ^ 2)]
      rw [show (ℓ ^ E) ^ 2 = ℓ ^ (E * 2) by rw [pow_mul]]
      exact pow_dvd_pow ℓ (by omega)
    rw [h, zero_mul]
  have hB : ((a ^ (ℓ ^ (E - 1)) : ℕ) : ZMod (ℓ ^ 2)) = 1 + Y := by
    rw [Nat.cast_pow, hcast, pow_add_one_eq_of_sq_eq_zero L hL2]
    congr 1
    show ((ℓ ^ (E - 1) : ℕ) : ZMod (ℓ ^ 2)) * L = Y
    simp only [L, Y]
    rw [← mul_assoc, ← Nat.cast_mul, ← pow_succ, Nat.sub_add_cancel hE]
  intro hdvd
  set Φ : ℕ := ∑ i ∈ Finset.range ℓ, (a ^ (ℓ ^ (E - 1))) ^ i with hΦdef
  have hΦcast : (Φ : ZMod (ℓ ^ 2)) =
      ∑ i ∈ Finset.range ℓ, ((a ^ (ℓ ^ (E - 1)) : ℕ) : ZMod (ℓ ^ 2)) ^ i := by
    rw [hΦdef]; push_cast; rfl
  have h2dvd : 2 ∣ ℓ - 1 := by obtain ⟨k, hk⟩ := hodd; exact ⟨k, by omega⟩
  have hsumid : (∑ i ∈ Finset.range ℓ, i) = ℓ * ((ℓ - 1) / 2) := by
    rw [Finset.sum_range_id]
    rw [Nat.mul_div_assoc (k := 2) (n := ℓ - 1) ℓ h2dvd]
  have hp : ℓ ^ (E - 1) * ℓ = ℓ ^ E := by rw [← pow_succ, Nat.sub_add_cancel hE]
  have hdvd2 : ℓ ^ 2 ∣ (∑ i ∈ Finset.range ℓ, i) * ℓ ^ E := by
    rw [hsumid]
    have heq : ℓ * ((ℓ - 1) / 2) * ℓ ^ E = ℓ ^ 2 * (ℓ ^ (E - 1) * ((ℓ - 1) / 2)) := by
      rw [pow_two, ← hp]; ring
    rw [heq]
    exact dvd_mul_right _ _
  have hΦsum : (Φ : ZMod (ℓ ^ 2)) = (ℓ : ZMod (ℓ ^ 2)) := by
    rw [hΦcast]
    calc ∑ i ∈ Finset.range ℓ, ((a ^ (ℓ ^ (E - 1)) : ℕ) : ZMod (ℓ ^ 2)) ^ i
        = ∑ i ∈ Finset.range ℓ, (1 + ((i : ZMod (ℓ ^ 2)) * Y)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hB, pow_add_one_eq_of_sq_eq_zero Y hY2 i]
      _ = (ℓ : ZMod (ℓ ^ 2)) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul]
          have hconst : (∑ i ∈ Finset.range ℓ, (1 : ZMod (ℓ ^ 2))) = (ℓ : ZMod (ℓ ^ 2)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          have hSY : (∑ i ∈ Finset.range ℓ, ((i : ℕ) : ZMod (ℓ ^ 2))) * Y = 0 := by
            have h0 : (((∑ i ∈ Finset.range ℓ, i) * ℓ ^ E : ℕ) : ZMod (ℓ ^ 2)) = 0 := by
              rw [CharP.cast_eq_zero_iff (ZMod (ℓ ^ 2)) (ℓ ^ 2)]
              exact hdvd2
            rw [← Nat.cast_sum]
            simp only [Y]
            rw [← mul_assoc, ← Nat.cast_mul, h0, zero_mul]
          rw [hconst, hSY, add_zero]
  have h0 : (Φ : ZMod (ℓ ^ 2)) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod (ℓ ^ 2)) (ℓ ^ 2) Φ).mpr hdvd
  have hℓne : (ℓ : ZMod (ℓ ^ 2)) ≠ 0 := by
    intro hc
    have hd : ℓ ^ 2 ∣ ℓ := (CharP.cast_eq_zero_iff (ZMod (ℓ ^ 2)) (ℓ ^ 2) ℓ).mp hc
    have hle : ℓ ^ 2 ≤ ℓ := Nat.le_of_dvd hℓ.pos hd
    have hlt : ℓ < ℓ ^ 2 := by nlinarith [hℓ.two_le]
    omega
  rw [hΦsum] at h0
  exact hℓne h0

theorem exists_prime_dvd_orderOf_modEq_one_odd (a ℓ E : ℕ) (ha : 2 ≤ a) (hℓ : ℓ.Prime) (hodd : Odd ℓ)
    (hE : 1 ≤ E) (h : a ≡ 1 [MOD ℓ]) :
    ∃ p : ℕ, p.Prime ∧ ¬ p ∣ a ∧ ℓ ^ E ∣ orderOf ((a : ZMod p)) ∧ ℓ ^ E < p := by
  set b : ℕ := a ^ (ℓ ^ (E - 1)) with hb
  set Φ : ℕ := ∑ i ∈ Finset.range ℓ, b ^ i with hΦ
  -- `a ≡ 1 [MOD ℓ]` gives `a = ℓ * (a / ℓ) + 1`, hence `a > ℓ`
  have hmod : a % ℓ = 1 := by
    have h1 : a % ℓ = 1 % ℓ := h
    rw [Nat.mod_eq_of_lt hℓ.one_lt] at h1
    exact h1
  have ha_eq : a = ℓ * (a / ℓ) + 1 := by
    have h' := Nat.div_add_mod a ℓ
    omega
  have hdiv : 1 ≤ a / ℓ := by
    rcases Nat.eq_zero_or_pos (a / ℓ) with h0 | hpos
    · rw [h0, mul_zero, zero_add] at ha_eq
      omega
    · exact hpos
  have hℓ_lt_a : ℓ < a := by
    have hle : ℓ + 1 ≤ a := by
      have h1 : ℓ + 1 = ℓ * 1 + 1 := by ring
      rw [h1, ha_eq]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left ℓ hdiv) 1
    omega
  -- `b ≥ a > ℓ` and `Φ ≥ b ^ (ℓ - 1) ≥ b > ℓ`
  have hb_ge_a : a ≤ b := by
    rw [hb]
    exact Nat.le_self_pow (pow_ne_zero _ hℓ.pos.ne') a
  have hb2 : 2 ≤ b := le_trans ha hb_ge_a
  have hbpos : 0 < b := by omega
  have hb1 : 1 ≤ b := by omega
  have hΦ_gt : ℓ < Φ := by
    have hterm : b ^ (ℓ - 1) ≤ Φ := by
      rw [hΦ]
      exact Finset.single_le_sum (fun i _ => Nat.zero_le _)
        (Finset.mem_range.mpr (by have := hℓ.pos; omega))
    have hb_pow : b ≤ b ^ (ℓ - 1) := by
      simpa using Nat.pow_le_pow_right hbpos (by have := hℓ.two_le; omega : 1 ≤ ℓ - 1)
    calc ℓ < a := hℓ_lt_a
      _ ≤ b := hb_ge_a
      _ ≤ b ^ (ℓ - 1) := hb_pow
      _ ≤ Φ := hterm
  -- `ℓ ∣ Φ`
  have hbmod : (b : ZMod ℓ) = 1 := by
    rw [hb, Nat.cast_pow]
    have ha1 : (a : ZMod ℓ) = 1 := by
      simpa using (ZMod.natCast_eq_natCast_iff a 1 ℓ).mpr h
    rw [ha1, one_pow]
  have hΦmod : (Φ : ZMod ℓ) = 0 := by
    rw [hΦ, Nat.cast_sum]
    rw [Finset.sum_congr rfl (fun i _ => by rw [Nat.cast_pow, hbmod, one_pow])]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, ZMod.natCast_self]
  have hℓ_dvd_Φ : ℓ ∣ Φ := (CharP.cast_eq_zero_iff (ZMod ℓ) ℓ Φ).mp hΦmod
  -- `ℓ ^ 2 ∤ Φ`
  have hnotdvd : ¬ ℓ ^ 2 ∣ Φ := by
    rw [hΦ, hb]
    exact not_dvd_sq_geom_sum a ℓ E hℓ hodd hE h
  -- write `Φ = ℓ * m`, then `ℓ ∤ m` and `m ≥ 2`
  set m : ℕ := Φ / ℓ with hm
  have hΦ_eq : Φ = ℓ * m := by
    rw [hm, mul_comm]
    exact (Nat.div_mul_cancel hℓ_dvd_Φ).symm
  have hℓ_not_dvd_m : ¬ ℓ ∣ m := by
    intro hd
    apply hnotdvd
    obtain ⟨k, hk⟩ := hd
    rw [hΦ_eq, hk, pow_two]
    exact ⟨k, by ring⟩
  have hm2 : 2 ≤ m := by
    have h : 1 < m := by
      refine (Nat.mul_lt_mul_left (by have := hℓ.pos; omega : 0 < ℓ)).mp ?_
      rw [mul_one, ← hΦ_eq]
      exact hΦ_gt
    omega
  obtain ⟨p, hp_prime, hp_dvd_m⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have hm_dvd_Φ : m ∣ Φ := by rw [hΦ_eq]; exact ⟨ℓ, by ring⟩
  have hp_dvd_Φ : p ∣ Φ := dvd_trans hp_dvd_m hm_dvd_Φ
  have hp_ne_ℓ : p ≠ ℓ := by
    intro hpe
    rw [hpe] at hp_dvd_m
    exact hℓ_not_dvd_m hp_dvd_m
  haveI : Fact p.Prime := ⟨hp_prime⟩
  -- The prime `p` divides the cyclotomic value, so `(b mod p) ^ ℓ = 1`
  have hΦp0 : (Φ : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p Φ).mpr hp_dvd_Φ
  have hΦp_sum : (Φ : ZMod p) = ∑ i ∈ Finset.range ℓ, (b : ZMod p) ^ i := by
    rw [hΦ]; push_cast; rfl
  have hgeomZ : (b : ZMod p) ^ ℓ = 1 := by
    have hg := geom_sum_mul (b : ZMod p) ℓ
    rw [← hΦp_sum, hΦp0, zero_mul] at hg
    exact sub_eq_zero.mp hg.symm
  have hbcast : (b : ZMod p) = (a : ZMod p) ^ (ℓ ^ (E - 1)) := by
    rw [hb]; push_cast; rfl
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
  -- the order is not `ℓ ^ (E - 1)`
  have hxne : (a : ZMod p) ^ (ℓ ^ (E - 1)) ≠ 1 := by
    intro hcontra
    have hb_eq : (b : ZMod p) = 1 := by
      have hx : ((a ^ (ℓ ^ (E - 1)) : ℕ) : ZMod p) = 1 := by simpa using hcontra
      rw [hb]; exact hx
    have hΦp_eq : (Φ : ZMod p) = (ℓ : ZMod p) := by
      rw [hΦ, Nat.cast_sum]
      rw [Finset.sum_congr rfl (fun i _ => by rw [Nat.cast_pow, hb_eq, one_pow])]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hℓ0 : (ℓ : ZMod p) = 0 := by rw [← hΦp_eq]; exact hΦp0
    have hp_dvd_ℓ : p ∣ ℓ := (CharP.cast_eq_zero_iff (ZMod p) p ℓ).mp hℓ0
    exact hp_ne_ℓ ((Nat.Prime.dvd_iff_eq hℓ hp_prime.ne_one).mp hp_dvd_ℓ).symm
  -- the order is exactly `ℓ ^ E`
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
