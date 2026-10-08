import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.GL2odd

open Nat

/-- Splitting lemma: if `d` (nonzero) divides a product `A * B`, then `d` factors as
`a * b` with `a ∣ A` and `b ∣ B`. -/
private lemma exists_dvd_mul_split {A B d : ℕ} (hdpos : 0 < d) (hd : d ∣ A * B) :
    ∃ a b : ℕ, d = a * b ∧ a ∣ A ∧ b ∣ B := by
  set a := d.gcd A with ha
  set b := d / a with hb
  have hapos : 0 < a := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left d A) hdpos
  refine ⟨a, b, ?_, Nat.gcd_dvd_right d A, ?_⟩
  · exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left d A)).symm
  · set r := A / a with hr
    have hAr : A = a * r := (Nat.mul_div_cancel' (Nat.gcd_dvd_right d A)).symm
    have hab : d = a * b := (Nat.mul_div_cancel' (Nat.gcd_dvd_left d A)).symm
    have hcop : b.Coprime r := by
      rw [Nat.coprime_iff_gcd_eq_one]
      have h1 : a * (b.gcd r) = a := by
        rw [← Nat.gcd_mul_left a b r, ← hab, ← hAr, ha]
      exact Nat.eq_of_mul_eq_mul_left hapos (by rw [mul_one]; exact h1)
    have hb_dvd_rB : b ∣ r * B := by
      have : a * b ∣ a * (r * B) := by
        rw [← hab]
        calc d ∣ A * B := hd
          _ = (a * r) * B := by rw [hAr]
          _ = a * (r * B) := by ring
      exact Nat.dvd_of_mul_dvd_mul_left hapos this
    exact hcop.dvd_of_dvd_mul_left hb_dvd_rB

theorem odd_dvd_pm1_sq_mul_pp1_eq_one {p d : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hdodd : Odd d) (hdvd : d ∣ (p - 1) ^ 2 * (p + 1)) (hmod : d ≡ 1 [MOD p]) :
    d = 1 := by
  have hpne2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hpodd
    omega
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hdne : d ≠ 0 := by
    rintro h
    rw [h] at hdodd
    exact Nat.not_odd_iff_even.mpr ⟨0, rfl⟩ hdodd
  have hdpos : 0 < d := Nat.pos_of_ne_zero hdne
  -- split `d = a * b` with `a ∣ (p-1)^2` and `b ∣ p+1`
  obtain ⟨a, b, hab, ha, hb⟩ := exists_dvd_mul_split hdpos hdvd
  have hpd1 : 0 < p - 1 := by omega
  have hpd2pos : 0 < (p - 1) ^ 2 := pow_pos hpd1 2
  have hp1pos : 0 < p + 1 := by omega
  have ha_pos : 0 < a := Nat.pos_of_dvd_of_pos ha hpd2pos
  have hb_pos : 0 < b := Nat.pos_of_dvd_of_pos hb hp1pos
  set m := (p - 1) ^ 2 / a with hm
  set n := (p + 1) / b with hn
  have ham : a * m = (p - 1) ^ 2 := Nat.mul_div_cancel' ha
  have hbn : b * n = p + 1 := Nat.mul_div_cancel' hb
  have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd hpd2pos ha) ha_pos
  have hn_pos : 0 < n := Nat.div_pos (Nat.le_of_dvd hp1pos hb) hb_pos
  -- residue computations in `ZMod p`
  haveI : Fact p.Prime := ⟨hp⟩
  have hpq : (((p - 1) ^ 2 : ℕ) : ZMod p) = 1 := by
    rw [Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ p), ZMod.natCast_self]
    ring
  have hpp1 : ((p + 1 : ℕ) : ZMod p) = 1 := by
    rw [Nat.cast_add, ZMod.natCast_self]
    ring
  have hd1 : (d : ZMod p) = 1 := by
    simpa using (ZMod.natCast_eq_natCast_iff d 1 p).mpr hmod
  have hab_z : (a : ZMod p) * (b : ZMod p) = 1 := by
    rw [← Nat.cast_mul, ← hab]; exact hd1
  have hbn_z : (b : ZMod p) * (n : ZMod p) = 1 := by
    rw [← Nat.cast_mul, hbn]; exact hpp1
  have ham_z : (a : ZMod p) * (m : ZMod p) = 1 := by
    rw [← Nat.cast_mul, ham]; exact hpq
  have hbn_z' : (n : ZMod p) * (b : ZMod p) = 1 := by rw [mul_comm]; exact hbn_z
  have ha0 : (a : ZMod p) ≠ 0 := by
    intro h; rw [h, zero_mul] at hab_z; exact zero_ne_one hab_z
  have hb0 : (b : ZMod p) ≠ 0 := by
    intro h; rw [h, zero_mul] at hbn_z; exact zero_ne_one hbn_z
  have ha_z : (a : ZMod p) = (n : ZMod p) := by
    apply mul_right_cancel₀ hb0
    rw [hab_z, hbn_z']
  have hb_z : (b : ZMod p) = (m : ZMod p) := by
    apply mul_left_cancel₀ ha0
    rw [hab_z, ham_z]
  -- integral parameters `u`, `t`
  have h1z : (((a : ℤ) - (n : ℤ) : ℤ) : ZMod p) = 0 := by
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, ha_z, sub_self]
  obtain ⟨u, hu⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd ((a : ℤ) - (n : ℤ)) p).mp h1z
  have hua : (a : ℤ) = (n : ℤ) + u * (p : ℤ) := by
    have : (a : ℤ) = (n : ℤ) + (p : ℤ) * u := by linarith
    rwa [mul_comm] at this
  have h2z : (((m : ℤ) - (b : ℤ) : ℤ) : ZMod p) = 0 := by
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, hb_z, sub_self]
  obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd ((m : ℤ) - (b : ℤ)) p).mp h2z
  have hmt : (m : ℤ) = (b : ℤ) + t * (p : ℤ) := by
    have : (m : ℤ) = (b : ℤ) + (p : ℤ) * t := by linarith
    rwa [mul_comm] at this
  -- bounds on `u` and `t`
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have ha1 : (1 : ℤ) ≤ (a : ℤ) := by omega
  have hb1z : (1 : ℤ) ≤ (b : ℤ) := by omega
  have hn1z : (1 : ℤ) ≤ (n : ℤ) := by omega
  have hm1z : (1 : ℤ) ≤ (m : ℤ) := by omega
  have hnz_le : (n : ℤ) ≤ (p : ℤ) + 1 := by
    have hnb : n * b = p + 1 := by rw [mul_comm]; exact hbn
    have h : n ≤ p + 1 := by
      have hh := Nat.mul_le_mul_left n (show 1 ≤ b from hb_pos)
      rwa [mul_one, hnb] at hh
    exact_mod_cast h
  have hu_ge : -1 ≤ u := by
    have hkey : u * (p : ℤ) ≥ -(p : ℤ) := by linarith [hua, ha1, hnz_le]
    nlinarith [hkey, hpz]
  have hb_odd : Odd b := by
    by_contra hbo
    have hbe : Even b := Nat.not_odd_iff_even.mp hbo
    have hE : Even (a * b) := hbe.mul_left a
    rw [← hab] at hE
    exact Nat.not_even_iff_odd.mpr hdodd hE
  have h2b : 2 * b ≤ p + 1 := by
    obtain ⟨k, hk⟩ := hb
    have hk0 : k ≠ 0 := by rintro rfl; omega
    have hk1 : k ≠ 1 := by
      rintro rfl
      have : b = p + 1 := by omega
      rw [this] at hb_odd
      exact Nat.not_odd_iff_even.mpr (hpodd.add_odd odd_one) hb_odd
    have hk2 : 2 ≤ k := by omega
    nlinarith [hk, hk2]
  have h2bz : (2 : ℤ) * (b : ℤ) ≤ (p : ℤ) + 1 := by exact_mod_cast h2b
  have ht_gt : t * (p : ℤ) > -(p : ℤ) := by nlinarith [hmt, hm1z, h2bz, hpz]
  have ht_ge : 0 ≤ t := by
    by_contra h
    have htle : t ≤ -1 := by omega
    nlinarith [ht_gt, htle, hpz]
  -- the key arithmetic identity
  have h1zi : (a : ℤ) * (m : ℤ) = (((p - 1) ^ 2 : ℕ) : ℤ) := by exact_mod_cast ham
  have h2zi : (n : ℤ) * (b : ℤ) = (p : ℤ) + 1 := by
    have hh : ((b * n : ℕ) : ℤ) = ((p + 1 : ℕ) : ℤ) := by exact_mod_cast hbn
    push_cast at hh
    linarith
  have hpp : (((p - 1) ^ 2 : ℕ) : ℤ) = (p : ℤ) ^ 2 - 2 * (p : ℤ) + 1 := by
    rw [Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ p)]
    push_cast
    ring
  have hexp : ((n : ℤ) + u * (p : ℤ)) * ((b : ℤ) + t * (p : ℤ)) =
      (p : ℤ) ^ 2 - 2 * (p : ℤ) + 1 := by
    rw [← hua, ← hmt]
    exact h1zi.trans hpp
  have hfact : ((n : ℤ) + u * (p : ℤ)) * ((b : ℤ) + t * (p : ℤ)) =
      (n : ℤ) * (b : ℤ) + (p : ℤ) * ((n : ℤ) * t + u * (b : ℤ) + u * t * (p : ℤ)) := by
    ring
  have hrhs : (p : ℤ) ^ 2 - 2 * (p : ℤ) + 1 = (n : ℤ) * (b : ℤ) + (p : ℤ) * ((p : ℤ) - 3) := by
    rw [h2zi]
    ring
  have keyp : (p : ℤ) * ((n : ℤ) * t + u * (b : ℤ) + u * t * (p : ℤ)) =
      (p : ℤ) * ((p : ℤ) - 3) := by
    have h := hexp
    rw [hfact, hrhs] at h
    linarith [h]
  have key : (n : ℤ) * t + u * (b : ℤ) + u * t * (p : ℤ) = (p : ℤ) - 3 := by
    apply mul_left_cancel₀ (a := (p : ℤ))
    · exact ne_of_gt hpz
    · exact keyp
  rcases eq_or_lt_of_le ht_ge with ht0 | htpos
  · -- `t = 0` forces `d = (p-1)^2`, which is even
    have hmeqz : (m : ℤ) = (b : ℤ) := by rw [hmt, ← ht0]; ring
    have hmeb : m = b := by exact_mod_cast hmeqz
    have hd_sq : d = (p - 1) ^ 2 := by rw [hab, ← hmeb, ham]
    have hpe : Even (p - 1) := by
      obtain ⟨k, hk⟩ := hpodd
      exact ⟨k, by omega⟩
    have hev : Even d := by
      rw [hd_sq, pow_two]
      exact hpe.mul_left (p - 1)
    exact absurd hev (Nat.not_even_iff_odd.mpr hdodd)
  · by_cases hu_pos : (1 : ℤ) ≤ u
    · -- `u ≥ 1` and `t ≥ 1` contradict the key identity
      have hge : (n : ℤ) * t + u * (b : ℤ) + u * t * (p : ℤ) ≥ (p : ℤ) := by
        nlinarith [hn1z, hb1z, htpos, hu_pos]
      linarith [key, hge]
    · have hu_le0 : u ≤ 0 := by omega
      have hu_cases : u = -1 ∨ u = 0 := by omega
      rcases hu_cases with hu_neg | hu_zero
      · -- `u = -1` forces `a = b = 1`, hence `d = 1`
        have hn_eq : (n : ℤ) = (a : ℤ) + (p : ℤ) := by rw [hua, hu_neg]; ring
        have hn_val : (n : ℤ) = (p : ℤ) + 1 := by linarith [hn_eq, ha1, hnz_le]
        have ha_val : (a : ℤ) = 1 := by linarith [hn_eq, hn_val]
        have hn_nat : n = p + 1 := by exact_mod_cast hn_val
        have ha_nat : a = 1 := by exact_mod_cast ha_val
        have hb_one : b = 1 := by
          have hbn' : b * (p + 1) = p + 1 := by
            calc b * (p + 1) = b * n := by rw [hn_nat]
              _ = p + 1 := hbn
          have h1 : b * (p + 1) = 1 * (p + 1) := by rw [one_mul]; exact hbn'
          exact Nat.mul_right_cancel (by omega : 0 < p + 1) h1
        rw [hab, ha_nat, hb_one, one_mul]
      · -- `u = 0` forces `d = p+1`, which is even
        have ha_val : (a : ℤ) = (n : ℤ) := by rw [hua, hu_zero]; ring
        have ha_nat : a = n := by exact_mod_cast ha_val
        have hd_pp1 : d = p + 1 := by
          calc d = a * b := hab
            _ = n * b := by rw [ha_nat]
            _ = b * n := by rw [mul_comm]
            _ = p + 1 := hbn
        have hev : Even d := by rw [hd_pp1]; exact hpodd.add_odd odd_one
        exact absurd hev (Nat.not_even_iff_odd.mpr hdodd)

end Work.GL2odd
