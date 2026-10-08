import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Frobenius.Complement

/-- If a prime `q` divides `s ^ p - 1` but not `s - 1` (with `p` prime), then
`p` is the multiplicative order of `s` modulo `q`; in particular if also
`q ∣ s ^ k - 1` then `p ∣ k`. -/
theorem ord_mod_eq_prime {p q s k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hsp : q ∣ s ^ p - 1) (hs : ¬ q ∣ s - 1) (hk : q ∣ s ^ k - 1) : p ∣ k := by
  -- `q ∤ s - 1` forces `s ≠ 0`, hence `s ≥ 1`.
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs (by simp)
  have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs0
  have hpos : 0 < s := Nat.pos_of_ne_zero hs0
  -- `(s : ZMod q) ^ p = 1`
  have hap : (s : ZMod q) ^ p = 1 := by
    have hle : 1 ≤ s ^ p := Nat.one_le_pow p s hpos
    have hmod : s ^ p ≡ 1 [MOD q] := ((Nat.modEq_iff_dvd' hle).mpr hsp).symm
    have h0 := (ZMod.natCast_eq_natCast_iff (s ^ p) 1 q).mpr hmod
    simpa only [Nat.cast_pow, Nat.cast_one] using h0
  -- `(s : ZMod q) ^ k = 1`
  have hak : (s : ZMod q) ^ k = 1 := by
    have hle : 1 ≤ s ^ k := Nat.one_le_pow k s hpos
    have hmod : s ^ k ≡ 1 [MOD q] := ((Nat.modEq_iff_dvd' hle).mpr hk).symm
    have h0 := (ZMod.natCast_eq_natCast_iff (s ^ k) 1 q).mpr hmod
    simpa only [Nat.cast_pow, Nat.cast_one] using h0
  -- `(s : ZMod q) ≠ 1`, since `q ∤ s - 1`
  have hne : (s : ZMod q) ≠ 1 := by
    intro hcon
    apply hs
    have hcon' : (s : ZMod q) = ((1 : ℕ) : ZMod q) := by simpa using hcon
    have hmod : s ≡ 1 [MOD q] := (ZMod.natCast_eq_natCast_iff s 1 q).mp hcon'
    exact (Nat.modEq_iff_dvd' hs1).mp hmod.symm
  -- The order divides `p`; it is not `1`; `p` is prime, so the order is `p`.
  have hpdvd : orderOf ((s : ZMod q)) ∣ p := orderOf_dvd_of_pow_eq_one hap
  have hkdvd : orderOf ((s : ZMod q)) ∣ k := orderOf_dvd_of_pow_eq_one hak
  have hne1 : orderOf ((s : ZMod q)) ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  have hord : orderOf ((s : ZMod q)) = p := by
    rcases hp.eq_one_or_self_of_dvd (orderOf ((s : ZMod q))) hpdvd with h | h
    · exact absurd h hne1
    · exact h
  rw [hord] at hkdvd
  exact hkdvd

end Work.Frobenius.Complement
