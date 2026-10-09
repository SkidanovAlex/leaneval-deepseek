import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.TameStructureDeep.Degree

/-- For `q` coprime to `n`, the multiplicative order of `q` in `ZMod n` is positive
and `n` divides `q ^ orderOf (q : ZMod n) - 1`.

This is the elementary content of Fermat–Euler: `q` is a unit modulo `n`, so some
positive power of `q` is `1` in `ZMod n` (Euler's theorem, with exponent
`Nat.totient n`); hence `orderOf (q : ZMod n) > 0`, and `pow_orderOf_eq_one`
combined with `Nat.ModEq.dvd'` gives the stated divisibility. -/
theorem dvd_pow_orderOf_sub_one {q n : ℕ} (hn : n ≠ 0) (h : q.Coprime n) :
    n ∣ q ^ orderOf (q : ZMod n) - 1 ∧ 0 < orderOf (q : ZMod n) := by
  have hφ : ((q : ZMod n)) ^ Nat.totient n = 1 := by
    have hthis := Nat.ModEq.pow_totient h
    rw [← ZMod.natCast_eq_natCast_iff] at hthis
    simp only [Nat.cast_pow, Nat.cast_one] at hthis
    exact hthis
  have hfin : IsOfFinOrder (q : ZMod n) :=
    isOfFinOrder_iff_pow_eq_one.mpr
      ⟨Nat.totient n, Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn), hφ⟩
  constructor
  · have hpow : (q : ZMod n) ^ orderOf (q : ZMod n) = 1 := pow_orderOf_eq_one _
    have hmod : 1 ≡ q ^ orderOf (q : ZMod n) [MOD n] := by
      rw [Nat.ModEq.comm, ← ZMod.natCast_eq_natCast_iff]
      simp only [Nat.cast_pow, Nat.cast_one]
      exact hpow
    exact hmod.dvd'
  · exact orderOf_pos_iff.mpr hfin

end NK.TameStructureDeep.Degree
