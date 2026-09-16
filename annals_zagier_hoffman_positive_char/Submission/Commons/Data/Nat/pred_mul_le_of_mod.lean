import Mathlib

namespace Commons.Data.Nat

/-- If `a` is a positive multiple of `q` with `a < 2 * q`, then `a = q`. -/
lemma eq_of_dvd_of_pos_of_lt_two_mul {q a : ℕ} (ha0 : 0 < a) (ha : a < 2 * q)
    (hd : q ∣ a) : a = q := by
  obtain ⟨t, ht⟩ := hd
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h
      simp at ht
      omega
    · exact h
  have htlt : t < 2 := by
    rw [ht, Nat.mul_comm 2 q] at ha
    exact Nat.lt_of_mul_lt_mul_left ha
  have ht1 : t = 1 := by omega
  subst ht1
  simpa using ht

theorem pred_mul_le_of_mod {q x u : ℕ} (hq : 2 ≤ q) (hx : 1 ≤ x) (hxq : x ≤ q)
    (hu : 1 ≤ u) (hdvd : (q - 1) ∣ u) (hmod : u % q ≤ q - x) :
    (q - 1) * x ≤ u := by
  obtain ⟨k, rfl⟩ := hdvd
  have hqpos : 0 < q := by omega
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      simp only [mul_zero] at hu
      omega
    · exact h
  suffices hkx : x ≤ k by
    exact Nat.mul_le_mul_left (q - 1) hkx
  set s := ((q - 1) * k) % q with hs
  set r := k % q with hr
  have hrq : r < q := by rw [hr]; exact Nat.mod_lt _ hqpos
  have hslt : s < q := by rw [hs]; exact Nat.mod_lt _ hqpos
  have hrk : r ≤ k := by rw [hr]; exact Nat.mod_le _ _
  have hsx : s ≤ q - x := by rw [hs]; exact hmod
  have hsum : (q - 1) * k + k = q * k := by
    have hq1 : q - 1 + 1 = q := Nat.succ_pred_eq_of_pos hqpos
    calc (q - 1) * k + k = (q - 1) * k + 1 * k := by rw [one_mul]
      _ = ((q - 1) + 1) * k := by rw [Nat.add_mul]
      _ = q * k := by rw [hq1]
  have hkey : (s + r) % q = 0 := by
    rw [hs, hr, ← Nat.add_mod, hsum]
    exact Nat.mul_mod_right q k
  by_cases hr0 : r = 0
  · rw [hr] at hr0
    have hqk : q ∣ k := Nat.dvd_of_mod_eq_zero hr0
    have hqle : q ≤ k := Nat.le_of_dvd (by omega) hqk
    omega
  · have hspos : 0 < s + r := by omega
    have hdvd' : q ∣ s + r := Nat.dvd_of_mod_eq_zero hkey
    have hlt : s + r < 2 * q := by omega
    have hsr : s + r = q := eq_of_dvd_of_pos_of_lt_two_mul hspos hlt hdvd'
    omega

end Commons.Data.Nat
