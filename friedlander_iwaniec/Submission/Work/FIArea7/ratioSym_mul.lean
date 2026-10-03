import Mathlib
import Submission.Work.FIArea7.ReSymbolTwist

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section

/-! ## Auxiliary material: the canonical representative `ratioRes`

`ratioSym z₁ z₂ d` is by definition the Jacobi symbol of the canonical representative in `ZMod d`
of `Re(z̄₁z₂)·|z₁|²⁻¹`.  It is convenient to name that representative and to know how it behaves
under the reduction `ZMod n → ZMod d` for `d ∣ n`: the class of the representative modulo `d`
agrees with the representative computed modulo `d`.  From that, multiplicativity of the symbol in
the modulus is immediate.
-/

/-- The canonical representative in `ZMod d` of `Re(z̄₁z₂)·|z₁|²⁻¹`, as a natural number.  By
definition `ratioSym z₁ z₂ d = jacobiSym (ratioRes z₁ z₂ d) d`. -/
def ratioRes (z1 z2 : GaussianInt) (d : ℕ) : ℕ :=
  ((((star z1 * z2).re : ZMod d) * ((((Work.FIPlan.gnorm z1 : ℕ)) : ZMod d))⁻¹).val)

/-- `ratioSym` is the Jacobi symbol of `ratioRes`. -/
lemma ratioSym_eq_jacobi (z1 z2 : GaussianInt) (d : ℕ) :
    ratioSym z1 z2 d = jacobiSym ((ratioRes z1 z2 d : ℕ) : ℤ) d := rfl

/-- The class of `ratioRes z₁ z₂ m` in `ZMod m` is `Re(z̄₁z₂)·|z₁|²⁻¹`. -/
lemma ratioRes_cast_self (z1 z2 : GaussianInt) {m : ℕ} [NeZero m] :
    ((ratioRes z1 z2 m : ℕ) : ZMod m)
      = ((star z1 * z2).re : ZMod m) * ((((Work.FIPlan.gnorm z1 : ℕ)) : ZMod m))⁻¹ := by
  rw [ratioRes]
  exact ZMod.natCast_zmod_val _

/-- The inverse of `(g : ZMod n)` transports along the reduction `ZMod n → ZMod d` (`d ∣ n`),
because the reduction is a ring homomorphism and `g` is a unit modulo `n` hence modulo `d`. -/
lemma castHom_inv_natCast {n d g : ℕ} (hd : d ∣ n) (h : Nat.Coprime g n) :
    (ZMod.castHom hd (ZMod d)) (((g : ℕ) : ZMod n)⁻¹) = (((g : ℕ) : ZMod d))⁻¹ := by
  have hunit : IsUnit (((g : ℕ) : ZMod n)) := (ZMod.isUnit_iff_coprime g n).mpr h
  have hh := congrArg (ZMod.castHom hd (ZMod d)) (ZMod.mul_inv_of_unit ((g : ZMod n)) hunit)
  rw [map_mul, map_natCast, map_one] at hh
  exact (ZMod.inv_eq_of_mul_eq_one d _ _ hh).symm

/-- The canonical representative of a rational residue modulo `n` reduces modulo `d ∣ n` to the
canonical representative modulo `d`: `ratioRes z₁ z₂ n ≡ ratioRes z₁ z₂ d (mod d)`. -/
lemma ratioRes_cast {z1 z2 : GaussianInt} {d n : ℕ} [NeZero d] [NeZero n]
    (hd : d ∣ n) (h1 : Nat.Coprime (Work.FIPlan.gnorm z1) n) :
    ((ratioRes z1 z2 n : ℕ) : ZMod d) = ((ratioRes z1 z2 d : ℕ) : ZMod d) := by
  rw [← map_natCast (ZMod.castHom hd (ZMod d)) (ratioRes z1 z2 n), ratioRes_cast_self z1 z2,
    map_mul, map_intCast, castHom_inv_natCast hd h1, ratioRes_cast_self z1 z2]

/-- ***FI* §17 bookkeeping at the round-6 ratio symbol: multiplicativity in the modulus.**

`Work.FIArea7.ratioSym z₁ z₂ d = (z₂/z₁|d)` is the Jacobi symbol of the rational residue of
`z₂/z₁` modulo `d` (`ReSymbolTwist.ratioSym`, the canonical representative of
`Re(z̄₁z₂)·|z₁|²⁻¹` in `ZMod d`).  For a modulus that factors as `d·e`, with `|z₁|²` invertible
modulo `d e`, the symbol factors:

  `ratioSym z₁ z₂ (d·e) = ratioSym z₁ z₂ d · ratioSym z₁ z₂ e`.

This splits the symbol of the reflected modulus `|Δ|·e` (see `ratioSym_mul_sq`) into the symbol
of modulus `|Δ|` — which *FI* Lemma 17.1 (17.5) evaluates, cf. `Work.FIArea7.ratioSym_absDelta_eq`
— and the symbol of the *small* modulus `e ≤ X`, which is the character `(ω|e)` of
(17.9)/(17.10).

Mathematically: the canonical representative of a rational residue modulo `d e` reduces modulo
`d` and modulo `e` to the canonical representatives for those moduli; `jacobiSym` is
multiplicative in the modulus (`jacobiSym.mul_right`) and depends on its numerator only through
the residue class (`jacobiSym.mod_left'`). -/
theorem ratioSym_mul (z1 z2 : GaussianInt) {d e : ℕ} [NeZero d] [NeZero e]
    (h1 : Nat.Coprime (Work.FIPlan.gnorm z1) (d * e)) :
    Work.FIArea7.ratioSym z1 z2 (d * e)
      = Work.FIArea7.ratioSym z1 z2 d * Work.FIArea7.ratioSym z1 z2 e := by
  rw [ratioSym_eq_jacobi, ratioSym_eq_jacobi, ratioSym_eq_jacobi, jacobiSym.mul_right]
  congr 1
  · apply jacobiSym.mod_left'
    rw [← ZMod.intCast_eq_intCast_iff']
    push_cast
    exact ratioRes_cast (z1 := z1) (z2 := z2) (dvd_mul_right d e) h1
  · apply jacobiSym.mod_left'
    rw [← ZMod.intCast_eq_intCast_iff']
    push_cast
    exact ratioRes_cast (z1 := z1) (z2 := z2) (dvd_mul_left e d) h1

end

end Work.FIArea7
