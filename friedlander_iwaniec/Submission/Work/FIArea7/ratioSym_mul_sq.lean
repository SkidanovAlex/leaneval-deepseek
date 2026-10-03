import Mathlib
import Submission.Work.FIArea7.ReSymbolTwist

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

/-- Auxiliary: if `N` is coprime to `n = d * t ^ 2` and `m ∣ n`, then the canonical representative
of the residue `a * N⁻¹ (mod n)` reduces, modulo `m`, to the canonical representative of
`a * N⁻¹ (mod m)`.  This is the `ZMod.castHom` computation underlying the square-factor rule. -/
private lemma zmod_val_mul_inv_cast {a : ℤ} {N : ℕ} {d t m : ℕ} [NeZero d] [NeZero t] [NeZero m]
    (hm : m ∣ d * t ^ 2) (hN : Nat.Coprime N (d * t ^ 2)) :
    ((((a : ZMod (d * t ^ 2)) * ((N : ℕ) : ZMod (d * t ^ 2))⁻¹).val : ℕ) : ZMod m)
      = (a : ZMod m) * ((N : ℕ) : ZMod m)⁻¹ := by
  have hn : NeZero (d * t ^ 2) := ⟨Nat.mul_ne_zero (NeZero.ne d) (pow_ne_zero 2 (NeZero.ne t))⟩
  have hunit : IsUnit ((N : ℕ) : ZMod (d * t ^ 2)) :=
    (ZMod.isUnit_iff_coprime N (d * t ^ 2)).mpr hN
  have hcastinv : (ZMod.castHom hm (ZMod m)) (((N : ℕ) : ZMod (d * t ^ 2))⁻¹)
      = ((N : ℕ) : ZMod m)⁻¹ := by
    have h1 : (ZMod.castHom hm (ZMod m)) ((N : ℕ) : ZMod (d * t ^ 2)) *
        (ZMod.castHom hm (ZMod m)) (((N : ℕ) : ZMod (d * t ^ 2))⁻¹) = 1 := by
      rw [← map_mul, ZMod.mul_inv_of_unit _ hunit, map_one]
    exact (ZMod.inv_eq_of_mul_eq_one m _ _ h1).symm.trans (by rw [map_natCast])
  rw [show ((((a : ZMod (d * t ^ 2)) * ((N : ℕ) : ZMod (d * t ^ 2))⁻¹).val : ℕ) : ZMod m)
      = (ZMod.castHom hm (ZMod m))
          ((a : ZMod (d * t ^ 2)) * ((N : ℕ) : ZMod (d * t ^ 2))⁻¹) from by
        rw [ZMod.castHom_apply]; exact (ZMod.cast_eq_val _).symm]
  rw [map_mul, hcastinv, map_intCast]

/-- Auxiliary (the square-factor rule, in the raw `jacobiSym`/`ZMod` form): for `(N, d t²) = 1`
and `(a, t) = 1`, the symbol of the canonical representative of `a · N⁻¹` agrees for the two
moduli `d · t²` and `d`. -/
private lemma val_ratioSym_mul_sq (a : ℤ) (N : ℕ) {d t : ℕ} [NeZero d] [NeZero t]
    (h1 : Nat.Coprime N (d * t ^ 2)) (h2 : Nat.Coprime a.natAbs t) :
    jacobiSym ((((a : ZMod (d * t ^ 2)) * ((N : ℕ) : ZMod (d * t ^ 2))⁻¹).val : ℤ)) (d * t ^ 2)
      = jacobiSym ((((a : ZMod d) * ((N : ℕ) : ZMod d)⁻¹).val : ℤ)) d := by
  have ht2 : NeZero (t ^ 2) := ⟨pow_ne_zero 2 (NeZero.ne t)⟩
  set Av : ℕ := ((a : ZMod (d * t ^ 2)) * ((N : ℕ) : ZMod (d * t ^ 2))⁻¹).val with hAv
  set Bv : ℕ := ((a : ZMod d) * ((N : ℕ) : ZMod d)⁻¹).val with hBv
  -- the representative modulo `t` is the rational residue `a · N⁻¹`, hence coprime to `t`
  have hAv_t : (Av : ZMod t) = (a : ZMod t) * ((N : ℕ) : ZMod t)⁻¹ := by
    rw [hAv]
    exact zmod_val_mul_inv_cast (a := a) (N := N) (d := d) (t := t) (m := t) ⟨d * t, by ring⟩ h1
  -- and the representative modulo `d` is the rational residue `a · N⁻¹`
  have hAv_d : (Av : ZMod d) = (a : ZMod d) * ((N : ℕ) : ZMod d)⁻¹ := by
    rw [hAv]
    exact zmod_val_mul_inv_cast (a := a) (N := N) (d := d) (t := t) (m := d)
      (dvd_mul_right d (t ^ 2)) h1
  have hNt : Nat.Coprime N t := Nat.Coprime.coprime_dvd_right ⟨d * t, by ring⟩ h1
  have hunitN : IsUnit ((N : ℕ) : ZMod t) := (ZMod.isUnit_iff_coprime N t).mpr hNt
  have hunita : IsUnit ((a : ℤ) : ZMod t) := by
    have hna : IsUnit ((a.natAbs : ℕ) : ZMod t) := (ZMod.isUnit_iff_coprime a.natAbs t).mpr h2
    rcases Int.natAbs_eq a with h | h
    · rw [h, Int.cast_natCast]; exact hna
    · rw [h, Int.cast_neg, Int.cast_natCast]; exact hna.neg
  have hmulN_t : (Av : ZMod t) * ((N : ℕ) : ZMod t) = (a : ZMod t) := by
    rw [hAv_t, mul_assoc, ZMod.inv_mul_of_unit _ hunitN, mul_one]
  have hmul_iff : IsUnit ((Av : ZMod t) * ((N : ℕ) : ZMod t)) ↔ IsUnit (Av : ZMod t) :=
    IsUnit.mul_right_iff (a := (Av : ZMod t)) (b := ((N : ℕ) : ZMod t)) hunitN
  have hAvUnit : IsUnit (Av : ZMod t) := hmul_iff.mp (by rw [hmulN_t]; exact hunita)
  have hcopAvt : Nat.Coprime Av t := (ZMod.isUnit_iff_coprime Av t).mp hAvUnit
  have hgcdAv : ((Av : ℕ) : ℤ).gcd (t : ℤ) = 1 := by
    rw [Int.gcd_eq_natAbs]
    simp only [Int.natAbs_natCast]
    exact Nat.coprime_iff_gcd_eq_one.mp hcopAvt
  have hsq : jacobiSym ((Av : ℕ) : ℤ) (t ^ 2) = 1 := by
    rw [jacobiSym.pow_right]
    exact jacobiSym.sq_one hgcdAv
  -- the two canonical representatives agree modulo `d`
  have hcast : (Av : ZMod d) = (Bv : ZMod d) := by
    rw [hAv_d, hBv, ZMod.natCast_zmod_val]
  have hXY : ((Av : ℕ) : ℤ) % (d : ℤ) = ((Bv : ℕ) : ℤ) % (d : ℤ) := by
    refine (ZMod.intCast_eq_intCast_iff' ((Av : ℕ) : ℤ) ((Bv : ℕ) : ℤ) d).mp ?_
    push_cast
    exact hcast
  calc jacobiSym ((Av : ℕ) : ℤ) (d * t ^ 2)
      = jacobiSym ((Av : ℕ) : ℤ) d * jacobiSym ((Av : ℕ) : ℤ) (t ^ 2) :=
        jacobiSym.mul_right _ d (t ^ 2)
    _ = jacobiSym ((Av : ℕ) : ℤ) d * 1 := by rw [hsq]
    _ = jacobiSym ((Av : ℕ) : ℤ) d := by rw [mul_one]
    _ = jacobiSym ((Bv : ℕ) : ℤ) d := jacobiSym.mod_left' hXY

/-- ***FI* §17 bookkeeping at the round-6 ratio symbol (the "square-factor rule").**

`Work.FIArea7.ratioSym z₁ z₂ d = (z₂/z₁|d)` is the Jacobi symbol of the *rational* residue of
`z₂/z₁` modulo `d`: the canonical representative of `Re(z̄₁z₂)·|z₁|²⁻¹` in `ZMod d`
(`ReSymbolTwist.ratioSym`).  Multiplying the modulus by a square does not change the symbol:

  `ratioSym z₁ z₂ (d·t²) = ratioSym z₁ z₂ d`.

This is the identity by which *FI* §17 reflects the large modulus `d = |Δ|/(4e)` of the `W`-cut
to the small divisor `e < X`: `|Δ|/(4e) · (2e)² = |Δ|·e`, so the symbol `sym (M/(4e))` of the
(17.1) form `WBcutExpandedInner` is the symbol of modulus `|Δ|·e`.  The hypotheses make the two
ratios well defined: `|z₁|²` is invertible modulo `d t²`, and the numerator is coprime to `t`.

Mathematically: the two canonical representatives agree modulo `d`, so the Jacobi symbols agree
there (`jacobiSym.mod_left'`); the extra factor is `jacobiSym a t ^ 2 = 1` because `a` is
coprime to `t` (`jacobiSym.sq_one`). -/
theorem ratioSym_mul_sq (z1 z2 : GaussianInt) {d t : ℕ} [NeZero d] [NeZero t]
    (h1 : Nat.Coprime (Work.FIPlan.gnorm z1) (d * t ^ 2))
    (h2 : Nat.Coprime (((star z1 * z2).re).natAbs) t) :
    Work.FIArea7.ratioSym z1 z2 (d * t ^ 2) = Work.FIArea7.ratioSym z1 z2 d := by
  have h := val_ratioSym_mul_sq ((star z1 * z2).re) (Work.FIPlan.gnorm z1) (d := d) (t := t) h1 h2
  simpa only [ratioSym] using h

end Work.FIArea7
