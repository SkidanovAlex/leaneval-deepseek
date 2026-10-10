/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotV

# Root H1: the order of vanishing at a rational place of the function field of an elliptic curve

This file fixes the vocabulary used by the proof of `Work.MotV.hurwitz_five` (node H1 of route V):
the order of vanishing `ordOfPlace E S hS f : ℤ` of an element of the function field `N(E)` at a
rational place `S` of `N(E)/N`, and the associated `ℤᵐ⁰`-valued valuation `placeVal`.

A *rational place* is a `Subalgebra N (Func E)` satisfying `MotC2.IsRatPlace E S` (discrete
valuation ring, residue field `N`, fraction field `N(E)`); by `MotC2.Classification` every rational
place is `infPlace E` (the point at infinity) or `affPlaceAt E a b` for a unique nonsingular
affine point `(a,b)`.

## Main definitions

* `ordOfPlace E S hS f`: the order of `f` at the place `S` (positive = zero, negative = pole);
* `placeVal E S hS`: the corresponding valuation `N(E) → ℤᵐ⁰`.

## Main results

* `ordOfPlace_mul`, `ordOfPlace_inv`, `ordOfPlace_nonneg_iff`, `ordOfPlace_eq_zero_iff`;
* `placeVal_isTrivOn` and `fifth_dvd_ordOfPlace`: the `FifthPowerValued` hypothesis at a place
  gives the divisibility of the order by `5`.

## Tags

elliptic curve, function field, place, discrete valuation ring, order of vanishing
-/

import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.AffPlace
import Submission.Work.MotC2.Classification
import Submission.Work.MotC2.Negation
import Submission.Work.MotC2.Translation

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

set_option autoImplicit false
open scoped Classical

variable {N : Type*} [Field N]

/-- The order of vanishing of `f` at the rational place `S` of `N(E)/N`: the exponent `n ≥ 0` with
`f = u·π^n` (`u` a unit of `S`, `π` a uniformizer) if `f` is regular at `S`, and the negative of
the order of `f⁻¹` otherwise.  (The convention `ordOfPlace S 0 = 0` is used.) -/
def ordOfPlace (E : WeierstrassCurve N) (S : Subalgebra N (MotC2.Func E))
    (hS : MotC2.IsRatPlace E S) (f : MotC2.Func E) : ℤ :=
  letI : IsDiscreteValuationRing ↥S := hS.1.choose
  if hf : f ∈ S then ((IsDiscreteValuationRing.addVal ↥S ⟨f, hf⟩).untopD 0 : ℕ)
  else -(((IsDiscreteValuationRing.addVal ↥S
        ⟨f⁻¹, (MotC2.mem_or_inv_mem_of_isRatPlace hS f).resolve_left hf⟩).untopD 0 : ℕ) : ℤ)

/-- The `ℤᵐ⁰`-valued valuation of `N(E)` attached to a rational place. -/
def placeVal (E : WeierstrassCurve N) (S : Subalgebra N (MotC2.Func E))
    (hS : MotC2.IsRatPlace E S) : MotC2.Func E → ℤᵐ⁰ :=
  fun f => if f = 0 then 0 else WithZero.coe (Multiplicative.ofAdd (ordOfPlace E S hS f))

end

end Work.MotV
