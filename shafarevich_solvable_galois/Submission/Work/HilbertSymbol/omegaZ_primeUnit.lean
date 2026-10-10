import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-!
# The value of `omegaZ` on the unit part of an odd prime

`omegaZ u` (for `u : ℤ_[2]ˣ`) is `0` when the reduction of `u` modulo `8` lies in `{1, 7}` (i.e.
`u ≡ ±1 (mod 8)`) and `1` otherwise.  The main result of this file is the classical identity

`omegaZ (unitPart 2 (primeUnit p)) = ((p^2 - 1) / 8 : ℕ)` in `ZMod 2`

for an odd prime `p`: the residue of `p` modulo `8` is `1` or `7` exactly when `(p^2 - 1)/8`
is even.

The proof reduces the statement to a statement about the residue of `p` modulo `8`.  The
arithmetic core is `omegaZ_primeUnit_arith`: for odd `n`, the parity of `(n^2 - 1)/8` is `0`
exactly when `n % 8 ∈ {1, 7}`.
-/

/-- Numerical core: for odd `r`, `((8q + r)^2 - 1)/8 = 8q^2 + 2qr + (r^2 - 1)/8`. -/
lemma omegaZ_primeUnit_div8 (q r : ℕ) (hodd : r % 2 = 1) :
    ((8*q + r)^2 - 1)/8 = 8*q^2 + 2*q*r + (r^2 - 1)/8 := by
  obtain ⟨J, hJ⟩ := Nat.eight_dvd_sq_sub_one_of_odd (Nat.odd_iff.mpr hodd)
  have hJ' : (r^2 - 1)/8 = J := by rw [hJ, Nat.mul_div_right _ (by norm_num)]
  rw [hJ']
  have hle : 1 ≤ r^2 := by
    have : 0 < r := by omega
    exact Nat.one_le_pow 2 r this
  have hsq : (8*q + r)^2 = 8*(8*q^2 + 2*q*r) + r^2 := by ring
  rw [hsq, Nat.add_sub_assoc hle, hJ, ← Nat.mul_add, Nat.mul_div_right _ (by norm_num)]

/-- Arithmetic core: for odd `n`, `(n^2 - 1)/8` is even exactly when `n ≡ ±1 (mod 8)`. -/
lemma omegaZ_primeUnit_arith {n : ℕ} (hodd : n % 2 = 1) :
    ((n^2 - 1)/8) % 2 = if n % 8 = 1 ∨ n % 8 = 7 then 0 else 1 := by
  set q := n / 8 with hq
  set r := n % 8 with hr
  have hnr : n = 8*q + r := by
    rw [hq, hr]; exact (Nat.div_add_mod n 8).symm
  have hr_lt : r < 8 := by rw [hr]; exact Nat.mod_lt _ (by norm_num)
  have hr_odd : r % 2 = 1 := by
    have hh := hodd
    rw [hnr] at hh
    omega
  rw [hnr, omegaZ_primeUnit_div8 q r hr_odd]
  interval_cases r <;> norm_num <;> omega

/-- The cast to `ZMod 2` of the arithmetic core. -/
lemma omegaZ_primeUnit_cast (p : ℕ) (hodd : p % 2 = 1) :
    (((p^2 - 1)/8 : ℕ) : ZMod 2) =
      (if p % 8 = 1 ∨ p % 8 = 7 then 0 else 1 : ZMod 2) := by
  have h := omegaZ_primeUnit_arith (n := p) hodd
  rw [show (((p^2 - 1)/8 : ℕ) : ZMod 2) = ((((p^2 - 1)/8) % 2 : ℕ) : ZMod 2) from by
        rw [ZMod.natCast_eq_natCast_iff]; exact (Nat.mod_modEq _ 2).symm]
  rw [h]
  by_cases hc : p % 8 = 1 ∨ p % 8 = 7
  · rw [if_pos hc, if_pos hc]; norm_num
  · rw [if_neg hc, if_neg hc]; norm_num

/-- `omegaZ` of the `2`-adic unit part of an odd prime `p` sees only the residue of `p` mod `8`:
it is `0` exactly when `p ≡ ±1 (mod 8)`. -/
lemma omegaZ_primeUnit_indicator (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    omegaZ (unitPart 2 (primeUnit p)) =
      (if p % 8 = 1 ∨ p % 8 = 7 then 0 else 1 : ZMod 2) := by
  have hodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp
    · exact h
  -- `p` is `2`-adically a unit, hence its unit part is `p` itself.
  have hpv : padicVal 2 (primeUnit p) = 0 := by
    rw [padicVal, primeUnit_coe, padicValRat.of_nat]
    have h2 : padicValNat 2 p = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    rw [h2]
    norm_num
  have hunit : (unitPart 2 (primeUnit p) : ℤ_[2]) = (p : ℤ_[2]) := by
    apply PadicInt.ext
    rw [unitPart_of_padicVal_eq_zero hpv]
    simp [primeUnit_coe]
  have hmap : PadicInt.toZModPow (p := 2) 3 (unitPart 2 (primeUnit p) : ℤ_[2])
      = (p : ZMod (2^3)) := by
    rw [hunit, map_natCast]
  rw [omegaZ, hmap, ZMod.val_natCast]
  norm_num

theorem omegaZ_primeUnit (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    omegaZ (unitPart 2 (primeUnit p)) = (((p ^ 2 - 1) / 8 : ℕ) : ZMod 2) := by
  have hodd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp
    · exact h
  rw [omegaZ_primeUnit_indicator p hp, ← omegaZ_primeUnit_cast p hodd]

end Work.HilbertSymbol
