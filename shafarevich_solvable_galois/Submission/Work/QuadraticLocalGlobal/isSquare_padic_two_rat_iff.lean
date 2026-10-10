import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.QuadraticLocalGlobal.isSquare_padic_two_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Squares in `ℚ_[2]`: the rational criterion

This file proves `Work.QuadraticLocalGlobal.isSquare_padic_two_rat_iff`: for a nonzero rational
number `x : ℚˣ`, the image of `x` in `ℚ_[2]` is a square if and only if

* `v_2(x)` is even,
* `ε(u) = 0`, and
* `ω(u) = 0`,

where `u = unitPart 2 x : ℤ_[2]ˣ` is the `2`-adic unit part of `x` and
`ε(u) = (u-1)/2 mod 2`, `ω(u) = (u^2-1)/8 mod 2` are the two `2`-adic characters appearing in the
definition of the Hilbert symbol at `2`.

The mathematics is the classical description of the square classes of `ℚ_2`: the unit group of
`ℤ_[2]` is `{±1} × (1 + 4ℤ_[2])` up to squares, and a `2`-adic unit is a square iff it is `≡ 1`
modulo `8`.  In the notation of the library the last condition is exactly
`toZModPow 3 u = 1`, so the statement is the conjunction of

* `isSquare_padic_two_iff` (a `2`-adic number `x` is a square iff `v_2(x)` is even and its unit
  part is a square), together with
* `toZModPow_three_eq_one_iff` below, which unravels `toZModPow 3 u = 1` as `ε(u) = 0 ∧ ω(u) = 0`
  via the compatibilities `ZMod.cast` of the reductions mod `4` and mod `8`.
-/

namespace Work.QuadraticLocalGlobal

open Work.HilbertSymbol

/-- A `2`-adic unit `u : ℤ_[2]ˣ` is `≡ 1 (mod 8)` (i.e. `toZModPow 3 u = 1`) exactly when
`ε(u) = 0` and `ω(u) = 0`.  Here `ε(u) = 0` says `u ≡ 1 (mod 4)` and `ω(u) = 0` says
`u ≡ ±1 (mod 8)`; their conjunction forces `u ≡ 1 (mod 8)`. -/
theorem toZModPow_three_eq_one_iff (u : ℤ_[2]ˣ) :
    PadicInt.toZModPow 3 (u : ℤ_[2]) = 1 ↔ epsZ u = 0 ∧ omegaZ u = 0 := by
  set A := PadicInt.toZModPow 3 (u : ℤ_[2]) with hA
  -- The reduction mod `4` is the reduction mod `8` followed by `ZMod.cast`.
  have hcast : (A.cast : ZMod (2 ^ 2)) = PadicInt.toZModPow 2 (u : ℤ_[2]) := by
    rw [hA]; exact PadicInt.cast_toZModPow 2 3 (by norm_num) (u : ℤ_[2])
  -- Unravel `epsZ u` as the parity of the residue of `A` mod `4`.
  have heps : epsZ u = (((A.val % 4) / 2 : ℕ) : ZMod 2) := by
    rw [epsZ, ← hcast, ZMod.cast_eq_val, ZMod.val_natCast]
    norm_num
  -- `omegaZ u` only sees `A.val`, i.e. the residue of `A` mod `8`.
  have homega : omegaZ u = (if A.val = 1 ∨ A.val = 7 then (0 : ZMod 2) else 1) := by
    rw [omegaZ, ← hA]
  rw [heps, homega]
  -- `A = 1` is equivalent to `A.val = 1` by injectivity of `ZMod.val`.
  have hone : (1 : ZMod (2 ^ 3)).val = 1 := by
    have h1 : ((1 : ℕ) : ZMod (2 ^ 3)) = 1 := by norm_num
    rw [← h1, ZMod.val_natCast]
    norm_num
  have hA1 : A = 1 ↔ A.val = 1 := by
    constructor
    · intro h; rw [h, hone]
    · intro h; exact ZMod.val_injective _ (by rw [h, hone])
  rw [hA1]
  have homega' : ((if A.val = 1 ∨ A.val = 7 then (0 : ZMod 2) else 1) = 0) ↔
      (A.val = 1 ∨ A.val = 7) := by
    by_cases h : A.val = 1 ∨ A.val = 7 <;> simp [h]
  rw [homega']
  -- It remains to check the statement for the residue classes `0, …, 7`.
  have hfin : ∀ k : ℕ, k < 8 →
      (k = 1 ↔ (((k % 4) / 2 : ℕ) : ZMod 2) = 0 ∧ (k = 1 ∨ k = 7)) := by
    intro k hk
    interval_cases k <;> decide
  have hlt8 : A.val < 8 := by simpa using ZMod.val_lt A
  exact hfin A.val hlt8

theorem isSquare_padic_two_rat_iff (x : ℚˣ) : IsSquare ((x : ℚ_[2])) ↔ Even (Work.HilbertSymbol.padicVal 2 x) ∧ Work.HilbertSymbol.epsZ (Work.HilbertSymbol.unitPart 2 x) = 0 ∧ Work.HilbertSymbol.omegaZ (Work.HilbertSymbol.unitPart 2 x) = 0 := by
  set y : ℚ_[2] := (x : ℚ_[2]) with hy
  have hy0 : y ≠ 0 := by
    rw [hy]; exact ratCast_ne_zero x
  -- The valuation of the image of `x` in `ℚ_[2]` is `v_2(x)`.
  have hval : y.valuation = padicVal 2 x := by
    rw [hy]
    exact Padic.valuation_ratCast (p := 2) (x : ℚ)
  -- The `2`-adic unit part of the image of `x` agrees with `unitPart 2 x`.
  have hunit : (padicUnitOf 2 y hy0 : ℤ_[2]) = (unitPart 2 x : ℤ_[2]) := by
    apply PadicInt.ext
    rw [padicUnitOf_coe, unitPart_coe, unitVal, hval, hy]
  have hkey : PadicInt.toZModPow 3 (padicUnitOf 2 y hy0 : ℤ_[2]) = 1 ↔
      epsZ (unitPart 2 x) = 0 ∧ omegaZ (unitPart 2 x) = 0 := by
    rw [hunit]
    exact toZModPow_three_eq_one_iff (unitPart 2 x)
  rw [isSquare_padic_two_iff hy0, hval]
  exact and_congr_right (fun _ => hkey)

end Work.QuadraticLocalGlobal
