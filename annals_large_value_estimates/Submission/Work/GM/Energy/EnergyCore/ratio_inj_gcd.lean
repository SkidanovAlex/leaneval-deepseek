import Mathlib

namespace Work.GM.Energy.EnergyCore

/-- Two fractions in lowest terms (with a common gcd `d`) that are equal as reals are equal
termwise: `a/b = c/e` with `gcd a b = gcd c e = d > 0` forces `a = c` and `b = e`. -/
theorem ratio_inj_gcd {a b c e d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (he : 0 < e)
    (h1 : Nat.gcd a b = d) (h2 : Nat.gcd c e = d)
    (h : (a : ℝ) / (b : ℝ) = (c : ℝ) / (e : ℝ)) : a = c ∧ b = e := by
  have hbR : (b : ℝ) ≠ 0 := by positivity
  have heR : (e : ℝ) ≠ 0 := by positivity
  have hcrossR : (a : ℝ) * e = (c : ℝ) * b := (div_eq_div_iff hbR heR).mp h
  have hcross : a * e = c * b := by exact_mod_cast hcrossR
  have hd : 0 < d := by rw [← h1]; exact Nat.gcd_pos_of_pos_left b ha
  have hda : d ∣ a := by rw [← h1]; exact Nat.gcd_dvd_left a b
  have hdb : d ∣ b := by rw [← h1]; exact Nat.gcd_dvd_right a b
  have hdc : d ∣ c := by rw [← h2]; exact Nat.gcd_dvd_left c e
  have hde : d ∣ e := by rw [← h2]; exact Nat.gcd_dvd_right c e
  have ha' : d * (a / d) = a := Nat.mul_div_cancel' hda
  have hb' : d * (b / d) = b := Nat.mul_div_cancel' hdb
  have hc' : d * (c / d) = c := Nat.mul_div_cancel' hdc
  have he' : d * (e / d) = e := Nat.mul_div_cancel' hde
  have hcop1 : Nat.Coprime (a / d) (b / d) := by
    have hh := Nat.coprime_div_gcd_div_gcd (m := a) (n := b) (by rw [h1]; exact hd)
    rwa [h1] at hh
  have hcop2 : Nat.Coprime (c / d) (e / d) := by
    have hh := Nat.coprime_div_gcd_div_gcd (m := c) (n := e) (by rw [h2]; exact hd)
    rwa [h2] at hh
  have hg1 : Nat.gcd (a / d) (b / d) = 1 := Nat.coprime_iff_gcd_eq_one.mp hcop1
  -- cross-multiplied form of the equality, after cancelling the common factor `d`
  have hmid : (d * (a / d)) * (d * (e / d)) = (d * (c / d)) * (d * (b / d)) := by
    rw [ha', he', hc', hb']; exact hcross
  have hxw : (a / d) * (e / d) = (c / d) * (b / d) := by
    have key : (d * d) * ((a / d) * (e / d)) = (d * d) * ((c / d) * (b / d)) := by
      nlinarith [hmid]
    exact Nat.mul_left_cancel (by positivity) key
  have hxpos : 0 < a / d := by
    rcases Nat.eq_zero_or_pos (a / d) with h0 | hpos
    · rw [h0, mul_zero] at ha'; omega
    · exact hpos
  -- coprimality of `a/d` and `b/d` forces `a/d ∣ c/d`
  have hxz : (a / d) ∣ (c / d) := hcop1.dvd_of_dvd_mul_right ⟨e / d, hxw.symm⟩
  obtain ⟨k, hk⟩ := hxz
  have hwy : e / d = k * (b / d) := by
    have h1' : (a / d) * (e / d) = ((a / d) * k) * (b / d) := by rw [← hk]; exact hxw
    have key : (a / d) * (e / d) = (a / d) * (k * (b / d)) := by rw [h1', mul_assoc]
    exact Nat.mul_left_cancel hxpos key
  -- now coprimality of `c/d` and `e/d` forces `k = 1`
  have hk1 : k = 1 := by
    have hzw : Nat.gcd ((a / d) * k) (k * (b / d)) = 1 := by
      simpa [hk, hwy] using hcop2
    rw [mul_comm k (b / d), Nat.gcd_mul_right (a / d) k (b / d), hg1, one_mul] at hzw
    exact hzw
  have hxz_eq : a / d = c / d := by rw [hk, hk1, mul_one]
  have hyw_eq : b / d = e / d := by rw [hwy, hk1, one_mul]
  constructor
  · rw [← ha', ← hc', hxz_eq]
  · rw [← hb', ← he', hyw_eq]

end Work.GM.Energy.EnergyCore
