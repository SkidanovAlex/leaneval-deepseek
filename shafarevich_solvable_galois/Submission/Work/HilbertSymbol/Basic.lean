import Mathlib.GroupTheory.Nilpotent
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Classical

namespace Work.HilbertSymbol

/-! ## Signs -/

/-- The element `±1` of `ℤˣ` attached to an integer `n`: `-1` when `n = -1`, and `1` otherwise.
For `n = ±1` this is the image of `n` under the canonical identification `{±1} ≅ ℤˣ`. -/
def intUnitOf (n : ℤ) : ℤˣ := if n = -1 then -1 else 1

@[simp] theorem intUnitOf_one : intUnitOf 1 = 1 := by simp [intUnitOf]

@[simp] theorem intUnitOf_neg_one : intUnitOf (-1) = -1 := by simp [intUnitOf]

theorem intUnitOf_eq_neg_one_iff {n : ℤ} : intUnitOf n = -1 ↔ n = -1 := by
  rw [intUnitOf]; split_ifs with h <;> simp [h]

theorem intUnitOf_eq_one_iff {n : ℤ} : intUnitOf n = 1 ↔ n ≠ -1 := by
  rw [intUnitOf]; split_ifs with h <;> simp [h]

theorem intUnitOf_mul {m n : ℤ} (hm : m = 1 ∨ m = -1) (hn : n = 1 ∨ n = -1) :
    intUnitOf (m * n) = intUnitOf m * intUnitOf n := by
  rcases hm with rfl | rfl <;> rcases hn with rfl | rfl <;> decide

theorem intUnitOf_sq (n : ℤ) : intUnitOf (n ^ 2) = 1 := by
  rw [intUnitOf, if_neg]
  intro h
  nlinarith [sq_nonneg n]

/-- The group isomorphism `(ZMod 2, +) ≅ ({±1}, *)`, written multiplicatively. -/
def signOf (n : ZMod 2) : ℤˣ := if n = 0 then 1 else -1

@[simp] theorem signOf_zero : signOf 0 = 1 := by simp [signOf]

@[simp] theorem signOf_one : signOf 1 = -1 := by
  rw [signOf]; simp

theorem signOf_add (m n : ZMod 2) : signOf (m + n) = signOf m * signOf n := by
  fin_cases m <;> fin_cases n <;> decide

theorem signOf_neg (m : ZMod 2) : signOf (-m) = signOf m := by
  fin_cases m <;> decide

/-! ## Rational numbers as units of `ℚ` -/

/-- The nonzero rational number `q`, as a unit of `ℚ`. -/
def ratUnit (q : ℚ) (hq : q ≠ 0) : ℚˣ := Units.mk0 q hq

@[simp] theorem ratUnit_coe (q : ℚ) (hq : q ≠ 0) : ((ratUnit q hq : ℚˣ) : ℚ) = q := rfl

/-- The nonzero integer `m`, as a unit of `ℚ`. -/
def intUnit (m : ℤ) (hm : m ≠ 0) : ℚˣ := ratUnit (m : ℚ) (Int.cast_ne_zero.mpr hm)

@[simp] theorem intUnit_coe (m : ℤ) (hm : m ≠ 0) : ((intUnit m hm : ℚˣ) : ℚ) = (m : ℚ) := rfl

/-- The prime `p`, as a unit of `ℚ`. -/
def primeUnit (p : ℕ) [Fact p.Prime] : ℚˣ :=
  ratUnit (p : ℚ) (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

@[simp] theorem primeUnit_coe (p : ℕ) [Fact p.Prime] : ((primeUnit p : ℚˣ) : ℚ) = p := rfl

/-! ## The `p`-adic valuation and the `p`-adic unit part of a rational number -/

/-- `v_p(a)`, the `p`-adic valuation of a nonzero rational number `a`, as an integer. -/
def padicVal (p : ℕ) (a : ℚˣ) : ℤ := padicValRat p (a : ℚ)

@[simp] theorem padicVal_one (p : ℕ) : padicVal p 1 = 0 := by
  simp [padicVal]

theorem padicVal_mul (p : ℕ) [Fact p.Prime] (a b : ℚˣ) :
    padicVal p (a * b) = padicVal p a + padicVal p b := by
  simp only [padicVal, Units.val_mul]
  rw [padicValRat.mul a.ne_zero b.ne_zero]

theorem padicVal_neg (p : ℕ) (a : ℚˣ) : padicVal p (-a) = padicVal p a := by
  simp only [padicVal, Units.val_neg]
  exact padicValRat.neg _

theorem padicVal_zpow (p : ℕ) [Fact p.Prime] (a : ℚˣ) (n : ℤ) :
    padicVal p (a ^ n) = n * padicVal p a := by
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg n
  · rw [hk, padicVal, padicVal, Units.val_zpow_eq_zpow_val, zpow_natCast, padicValRat.pow]
  · rw [hk, padicVal, padicVal, Units.val_zpow_eq_zpow_val, zpow_neg, zpow_natCast,
      padicValRat.inv, padicValRat.pow]
    ring

/-- The `p`-adic unit part `p ^ (-v_p a) * a` of a nonzero rational number, viewed inside the
completion `ℚ_[p]`. -/
def unitVal (p : ℕ) [Fact p.Prime] (a : ℚˣ) : ℚ_[p] :=
  (p : ℚ_[p]) ^ (-(padicVal p a)) * (a : ℚ_[p])

theorem p_cast_ne_zero (p : ℕ) [Fact p.Prime] : (p : ℚ_[p]) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  exact (Fact.out : p.Prime).ne_zero

theorem ratCast_ne_zero {p : ℕ} [Fact p.Prime] (a : ℚˣ) : (a : ℚ_[p]) ≠ 0 := by
  rw [Rat.cast_ne_zero]
  exact a.ne_zero

theorem unitVal_ne_zero (p : ℕ) [Fact p.Prime] (a : ℚˣ) : unitVal p a ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (p_cast_ne_zero p)) (ratCast_ne_zero a)

theorem valuation_unitVal (p : ℕ) [Fact p.Prime] (a : ℚˣ) :
    (unitVal p a).valuation = 0 := by
  rw [unitVal, Padic.valuation_mul (zpow_ne_zero _ (p_cast_ne_zero p)) (ratCast_ne_zero a),
    Padic.valuation_zpow, Padic.valuation_p, Padic.valuation_ratCast]
  simp only [padicVal]
  ring

theorem norm_unitVal (p : ℕ) [Fact p.Prime] (a : ℚˣ) : ‖unitVal p a‖ = 1 := by
  rw [Padic.norm_eq_zpow_neg_valuation (unitVal_ne_zero p a), valuation_unitVal, neg_zero,
    zpow_zero]

/-- The `p`-adic unit part of a nonzero rational number, as a unit of the `p`-adic integers
`ℤ_[p]`. -/
def unitPart (p : ℕ) [Fact p.Prime] (a : ℚˣ) : ℤ_[p]ˣ :=
  PadicInt.mkUnits (norm_unitVal p a)

@[simp] theorem unitPart_coe (p : ℕ) [Fact p.Prime] (a : ℚˣ) :
    ((unitPart p a : ℤ_[p]) : ℚ_[p]) = unitVal p a :=
  PadicInt.mkUnits_eq _

theorem unitVal_of_padicVal_eq_zero {p : ℕ} [Fact p.Prime] {a : ℚˣ}
    (h : padicVal p a = 0) : unitVal p a = (a : ℚ_[p]) := by
  rw [unitVal, h, neg_zero, zpow_zero, one_mul]

theorem unitPart_of_padicVal_eq_zero {p : ℕ} [Fact p.Prime] {a : ℚˣ}
    (h : padicVal p a = 0) :
    ((unitPart p a : ℤ_[p]) : ℚ_[p]) = (a : ℚ_[p]) := by
  rw [unitPart_coe, unitVal_of_padicVal_eq_zero h]

@[simp] theorem unitPart_one (p : ℕ) [Fact p.Prime] : unitPart p 1 = 1 := by
  apply Units.ext
  apply PadicInt.ext
  change unitVal p 1 = 1
  simp [unitVal, padicVal_one]

theorem unitPart_mul (p : ℕ) [Fact p.Prime] (a b : ℚˣ) :
    unitPart p (a * b) = unitPart p a * unitPart p b := by
  apply Units.ext
  apply PadicInt.ext
  change unitVal p (a * b) = unitVal p a * unitVal p b
  simp only [unitVal, padicVal_mul p a b, Units.val_mul, Rat.cast_mul]
  rw [show -(padicVal p a + padicVal p b) = -(padicVal p a) + -(padicVal p b) by ring,
    zpow_add₀ (p_cast_ne_zero p)]
  ring

/-! ## The Legendre symbol of a `p`-adic unit, as an element of `ℤˣ = {±1}` -/

/-- The quadratic (Legendre) character of a unit of the residue field `ZMod p`, as an element
of `ℤˣ = {±1}`. -/
def quadCharUnit (p : ℕ) [Fact p.Prime] (x : (ZMod p)ˣ) : ℤˣ :=
  intUnitOf (quadraticChar (ZMod p) (x : ZMod p))

theorem quadCharUnit_mul (p : ℕ) [Fact p.Prime] (x y : (ZMod p)ˣ) :
    quadCharUnit p (x * y) = quadCharUnit p x * quadCharUnit p y := by
  rcases quadraticChar_dichotomy (Units.ne_zero x) with hx | hx <;>
    rcases quadraticChar_dichotomy (Units.ne_zero y) with hy | hy <;>
    simp [quadCharUnit, Units.val_mul, map_mul, hx, hy]

@[simp] theorem quadCharUnit_one (p : ℕ) [Fact p.Prime] : quadCharUnit p 1 = 1 := by
  simp [quadCharUnit]

theorem quadCharUnit_eq_neg_one_iff (p : ℕ) [Fact p.Prime] (x : (ZMod p)ˣ) :
    quadCharUnit p x = -1 ↔ quadraticChar (ZMod p) (x : ZMod p) = -1 := by
  simp only [quadCharUnit, intUnitOf_eq_neg_one_iff]

/-- The Legendre symbol `(u / p)` of a `p`-adic unit `u : ℤ_[p]ˣ`, as an element of `ℤˣ`. -/
def legendreUnit (p : ℕ) [Fact p.Prime] (u : ℤ_[p]ˣ) : ℤˣ :=
  quadCharUnit p (Units.map (PadicInt.toZMod (p := p)) u)

theorem legendreUnit_mul (p : ℕ) [Fact p.Prime] (u v : ℤ_[p]ˣ) :
    legendreUnit p (u * v) = legendreUnit p u * legendreUnit p v := by
  rw [legendreUnit, map_mul, quadCharUnit_mul, ← legendreUnit, ← legendreUnit]

@[simp] theorem legendreUnit_one (p : ℕ) [Fact p.Prime] : legendreUnit p 1 = 1 := by
  simp [legendreUnit, quadCharUnit]

/-- The Legendre symbol of the `p`-adic unit part of the rational number `a`, as a `ℤˣ`-valued
multiplicative character of `ℚˣ`. -/
def legendreOf (p : ℕ) [Fact p.Prime] (a : ℚˣ) : ℤˣ :=
  legendreUnit p (unitPart p a)

theorem legendreOf_mul (p : ℕ) [Fact p.Prime] (a b : ℚˣ) :
    legendreOf p (a * b) = legendreOf p a * legendreOf p b := by
  rw [legendreOf, unitPart_mul, legendreUnit_mul, ← legendreOf, ← legendreOf]

@[simp] theorem legendreOf_one (p : ℕ) [Fact p.Prime] : legendreOf p 1 = 1 := by
  simp [legendreOf]

/-! ## The Hilbert symbol at the finite places -/

/-- The Hilbert symbol `(a,b)_p` at an odd prime `p`: with `a = p ^ α u`, `b = p ^ β v`
(`u, v ∈ ℤ_[p]ˣ`, `α = v_p(a)`, `β = v_p(b)`),
`(a,b)_p = (-1) ^ (α β (p-1)/2) * (u/p) ^ β * (v/p) ^ α`. -/
def hilbertSymbolOdd (p : ℕ) [Fact p.Prime] (a b : ℚˣ) : ℤˣ :=
  (-1 : ℤˣ) ^ (padicVal p a * padicVal p b * (((p - 1) / 2 : ℕ) : ℤ))
    * legendreOf p a ^ (padicVal p b)
    * legendreOf p b ^ (padicVal p a)

/-- `ε(u) = (u-1)/2 mod 2 ∈ ZMod 2` for a unit `u` of `ℤ_[2]`, i.e. `u ≡ 1 + 2 ε(u) (mod 4)`. -/
def epsZ (u : ℤ_[2]ˣ) : ZMod 2 :=
  ((PadicInt.toZModPow 2 (u : ℤ_[2])).val / 2 : ℕ)

/-- `ω(u) = (u²-1)/8 mod 2 ∈ ZMod 2` for a unit `u` of `ℤ_[2]`. -/
def omegaZ (u : ℤ_[2]ˣ) : ZMod 2 :=
  if (PadicInt.toZModPow 3 (u : ℤ_[2])).val = 1
      ∨ (PadicInt.toZModPow 3 (u : ℤ_[2])).val = 7 then 0 else 1

/-- The Hilbert symbol `(a,b)_2` at the prime `2`: with `a = 2 ^ α u`, `b = 2 ^ β v`
(`u, v ∈ ℤ_[2]ˣ`, `α = v_2(a)`, `β = v_2(b)`),
`(a,b)_2 = (-1) ^ (ε(u) ε(v) + α ω(v) + β ω(u))`. -/
def hilbertSymbolTwo (a b : ℚˣ) : ℤˣ :=
  signOf (epsZ (unitPart 2 a) * epsZ (unitPart 2 b)
    + (padicVal 2 a : ZMod 2) * omegaZ (unitPart 2 b)
    + (padicVal 2 b : ZMod 2) * omegaZ (unitPart 2 a))

/-- The Hilbert symbol `(a,b)_p` at a finite place `p` of `ℚ`. -/
def hilbertSymbolAtPrime (p : ℕ) [Fact p.Prime] (a b : ℚˣ) : ℤˣ :=
  if p = 2 then hilbertSymbolTwo a b else hilbertSymbolOdd p a b

@[simp] theorem hilbertSymbolAtPrime_two (a b : ℚˣ) :
    hilbertSymbolAtPrime 2 a b = hilbertSymbolTwo a b := by
  rw [hilbertSymbolAtPrime, if_pos rfl]

theorem hilbertSymbolAtPrime_eq_odd {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (a b : ℚˣ) :
    hilbertSymbolAtPrime p a b = hilbertSymbolOdd p a b := by
  rw [hilbertSymbolAtPrime, if_neg hp]

/-! ## The Hilbert symbol at the archimedean place -/

/-- The Hilbert symbol `(a,b)_∞` at the archimedean place:
`(a,b)_∞ = -1` if and only if `a < 0` and `b < 0`. -/
def hilbertSymbolReal (a b : ℚˣ) : ℤˣ :=
  if (a : ℚ) < 0 ∧ (b : ℚ) < 0 then -1 else 1

theorem hilbertSymbolReal_eq_neg_one_iff (a b : ℚˣ) :
    hilbertSymbolReal a b = -1 ↔ (a : ℚ) < 0 ∧ (b : ℚ) < 0 := by
  rw [hilbertSymbolReal]
  by_cases h : (a : ℚ) < 0 ∧ (b : ℚ) < 0
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨fun h1 => absurd h1 (by decide), fun h1 => absurd h1 h⟩

theorem hilbertSymbolReal_eq_one_iff (a b : ℚˣ) :
    hilbertSymbolReal a b = 1 ↔ ¬((a : ℚ) < 0 ∧ (b : ℚ) < 0) := by
  rw [hilbertSymbolReal]
  by_cases h : (a : ℚ) < 0 ∧ (b : ℚ) < 0
  · rw [if_pos h]
    exact ⟨fun h1 => absurd h1 (by decide), fun h1 => absurd h h1⟩
  · rw [if_neg h]
    exact ⟨fun _ => h, fun _ => rfl⟩

/-! ## Places of `ℚ` -/

/-- A place of `ℚ`: `none` is the archimedean place, `some p` the `p`-adic place at the prime
`p`. -/
abbrev Place : Type := Option ℕ

/-- The Hilbert symbol `(a,b)_v` at the place `v` of `ℚ`. -/
def hilbertSymbol (v : Place) (a b : ℚˣ) : ℤˣ :=
  match v with
  | none => hilbertSymbolReal a b
  | some p => if h : p.Prime then @hilbertSymbolAtPrime p ⟨h⟩ a b else 1

@[simp] theorem hilbertSymbol_none (a b : ℚˣ) :
    hilbertSymbol none a b = hilbertSymbolReal a b := rfl

theorem hilbertSymbol_some {p : ℕ} [Fact p.Prime] (a b : ℚˣ) :
    hilbertSymbol (some p) a b = hilbertSymbolAtPrime p a b := by
  simp only [hilbertSymbol]
  rw [dif_pos (Fact.out : p.Prime)]

end Work.HilbertSymbol
