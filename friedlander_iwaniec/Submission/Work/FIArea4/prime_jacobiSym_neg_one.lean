import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4

/-- For an odd prime `p` there is an odd `u` with `u ≡ 1 (mod 8)` and Jacobi symbol `J(p | u) = -1`.
Proof sketch: pick a quadratic non-residue `v` modulo `p` (`FiniteField.exists_nonsquare`, valid since
`ringChar (ZMod p) = p ≠ 2`), and let `u` be given by CRT with `u ≡ v (mod p)`, `u ≡ 1 (mod 8)`
(`Nat.chineseRemainder`, moduli `p` and `8` coprime). Then `u` is odd and coprime to `p`; quadratic
reciprocity `J(p|u) = qrSign u p * J(u|p)` (both arguments odd) has `qrSign u p = J(χ₄ u | p) = J(1|p) = 1`
because `u ≡ 1 mod 4`, and `J(u|p) = J(u % p | p) = J(v|p) = legendreSym p v = -1`. -/
theorem prime_jacobiSym_neg_one (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ u : ℕ, Odd u ∧ u % 8 = 1 ∧ Nat.Coprime u p ∧ jacobiSym (p : ℤ) u = -1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  obtain ⟨v, hv⟩ := FiniteField.exists_nonsquare (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  have hv0 : v ≠ 0 := by
    intro h
    exact hv ⟨0, by rw [h]; simp⟩
  set v₀ : ℕ := v.val with hv₀
  have hv₀_lt : v₀ < p := by rw [hv₀]; exact ZMod.val_lt v
  have hv₀_cast : (v₀ : ZMod p) = v := by rw [hv₀]; exact ZMod.natCast_zmod_val v
  have hv₀_ne : v₀ ≠ 0 := by
    intro h
    exact hv0 (by rw [← hv₀_cast, h]; simp)
  have hcop : Nat.Coprime 8 p := by
    have : Nat.Coprime (2 ^ 3) p :=
      Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hpodd)
    simpa using this
  obtain ⟨u, hu8, hup⟩ := Nat.chineseRemainder hcop 1 v₀
  have hu8' : u % 8 = 1 := by
    have : u % 8 = 1 % 8 := hu8
    simpa using this
  have hup' : u % p = v₀ := by
    have : u % p = v₀ % p := hup
    rw [this, Nat.mod_eq_of_lt hv₀_lt]
  refine ⟨u, ?_, hu8', ?_, ?_⟩
  · -- `u` is odd
    exact Nat.odd_iff.mpr (by omega)
  · -- `u` is coprime to `p`
    have hpu : Nat.Coprime p u := by
      rw [hp.coprime_iff_not_dvd, Nat.dvd_iff_mod_eq_zero, hup']
      exact hv₀_ne
    exact hpu.symm
  · -- the Jacobi symbol is `-1`
    have hu4 : u % 4 = 1 := by omega
    have hqr : jacobiSym (p : ℤ) u = jacobiSym (u : ℤ) p :=
      jacobiSym.quadratic_reciprocity_one_mod_four' hpodd hu4
    have hmod1 : jacobiSym (u : ℤ) p = jacobiSym ((u % p : ℕ) : ℤ) p := by
      rw [jacobiSym.mod_left, ← Int.natCast_mod]
    have hmod2 : jacobiSym ((u % p : ℕ) : ℤ) p = jacobiSym (v₀ : ℤ) p := by
      rw [hup']
    have hnonsq : jacobiSym (v₀ : ℤ) p = -1 := by
      rw [ZMod.nonsquare_iff_jacobiSym_eq_neg_one]
      have hcast : ((v₀ : ℤ) : ZMod p) = v := by rw [Int.cast_natCast, hv₀_cast]
      rwa [hcast]
    rw [hqr, hmod1, hmod2, hnonsq]

end Work.FIArea4
