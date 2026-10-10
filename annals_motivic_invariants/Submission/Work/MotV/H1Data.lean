/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotV

# Root H1: the input bundle of the Hurwitz count

`H1Data N E` collects, as a structure, all the local and global facts about the function field
`N(E)` of an elliptic curve that the proof of `Work.MotV.hurwitz_five` uses:

* the order of vanishing `ordOfPlace` at a rational place and its basic laws
  (multiplicativity, inverse, sign criterion, ultrametric inequality);
* the fifth-power transfer `FifthPowerValued N g → 5 ∣ ord_Q g`;
* the local structure at an affine point (uniformiser dichotomy);
* the local structure at the point at infinity;
* the invariant derivation and its two local bounds.
-/

import Mathlib
import Submission.Work.MotV.PlaceDefs
import Submission.Work.MotV.Machinery
import Submission.Work.MotC2.AffPlace

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

namespace Work.MotV

noncomputable section

variable {N : Type*} [Field N]

/-- The input bundle of the Hurwitz count: everything about the function field `N(E)` that is
proved elsewhere. -/
structure H1Data (N : Type*) [Field N] (E : WeierstrassCurve N) [E.IsElliptic] where
  /-- the point at infinity is a rational place -/
  infRat : MotC2.IsRatPlace E (MotC2.infPlace E)
  /-- multiplicativity of the order at a place -/
  ord_mul : ∀ (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S) (f g : MotC2.Func E),
    f ≠ 0 → g ≠ 0 →
      ordOfPlace E S hS (f * g) = ordOfPlace E S hS f + ordOfPlace E S hS g
  /-- the order of an inverse -/
  ord_inv : ∀ (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S) (f : MotC2.Func E),
    f ≠ 0 → ordOfPlace E S hS f⁻¹ = - ordOfPlace E S hS f
  /-- the sign criterion -/
  ord_nonneg : ∀ (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S) (f : MotC2.Func E),
    0 ≤ ordOfPlace E S hS f ↔ f ∈ S
  /-- the ultrametric inequality -/
  ord_add : ∀ (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S) (f g : MotC2.Func E),
    f + g ≠ 0 → min (ordOfPlace E S hS f) (ordOfPlace E S hS g) ≤ ordOfPlace E S hS (f + g)
  /-- fifth-power-valued elements have order divisible by five at every place -/
  fifth : ∀ (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S) (g : MotC2.Func E),
    FifthPowerValued N g → 5 ∣ ordOfPlace E S hS g
  /-- the local structure at an affine point, first case -/
  aff_ne : ∀ (a b : N) (h : Nonsingular E a b), 2 * b + E.a₁ * a + E.a₃ ≠ 0 →
    ordOfPlace E (MotC2.affPlaceAt E a b) (MotC2.AffPlace N E a b h).1
        (MotC2.genX E - algebraMap N (MotC2.Func E) a) = 1 ∧
      ordOfPlace E (MotC2.affPlaceAt E a b) (MotC2.AffPlace N E a b h).1
        (2 * MotC2.genY E + algebraMap N (MotC2.Func E) E.a₁ * MotC2.genX E +
          algebraMap N (MotC2.Func E) E.a₃) = 0
  /-- the local structure at an affine point, second case -/
  aff_eq : ∀ (a b : N) (h : Nonsingular E a b), 2 * b + E.a₁ * a + E.a₃ = 0 →
    ordOfPlace E (MotC2.affPlaceAt E a b) (MotC2.AffPlace N E a b h).1
        (MotC2.genX E - algebraMap N (MotC2.Func E) a) = 2 ∧
      ordOfPlace E (MotC2.affPlaceAt E a b) (MotC2.AffPlace N E a b h).1
        (MotC2.genY E - algebraMap N (MotC2.Func E) b) = 1 ∧
      ordOfPlace E (MotC2.affPlaceAt E a b) (MotC2.AffPlace N E a b h).1
        (3 * (MotC2.genX E) ^ 2 + 2 * algebraMap N (MotC2.Func E) E.a₂ * MotC2.genX E +
          algebraMap N (MotC2.Func E) E.a₄ - algebraMap N (MotC2.Func E) E.a₁ * MotC2.genY E) = 0
  /-- the local structure at the point at infinity -/
  inf_local : ordOfPlace E (MotC2.infPlace E) infRat (MotC2.genX E) = -2 ∧
    ordOfPlace E (MotC2.infPlace E) infRat (MotC2.infU E) = 2 ∧
    ordOfPlace E (MotC2.infPlace E) infRat (MotC2.infW E) = 1 ∧
    ordOfPlace E (MotC2.infPlace E) infRat (MotC2.genY E) = -3
  /-- the invariant derivation, its values on the coordinates, and its two local bounds -/
  deriv : ∃ D : Derivation N (MotC2.Func E) (MotC2.Func E),
    D (MotC2.genX E) = 2 * MotC2.genY E +
        algebraMap N (MotC2.Func E) E.a₁ * MotC2.genX E + algebraMap N (MotC2.Func E) E.a₃ ∧
    D (MotC2.genY E) = 3 * (MotC2.genX E) ^ 2 +
        2 * algebraMap N (MotC2.Func E) E.a₂ * MotC2.genX E +
        algebraMap N (MotC2.Func E) E.a₄ - algebraMap N (MotC2.Func E) E.a₁ * MotC2.genY E ∧
    (∀ (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S) (f : MotC2.Func E),
      D f ≠ 0 → ordOfPlace E S hS f - 1 ≤ ordOfPlace E S hS (D f)) ∧
    (∀ (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S) (f : MotC2.Func E),
      ordOfPlace E S hS f = 0 → 0 ≤ ordOfPlace E S hS (D f)) ∧
    (∀ a : CoordinateRing E, ∃ b : CoordinateRing E,
      algebraMap (CoordinateRing E) (MotC2.Func E) b =
        D (algebraMap (CoordinateRing E) (MotC2.Func E) a))

end

end Work.MotV
