/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The bridge between the places of a curve and the primes of `k[x]^int`

Let `C` be a smooth proper geometrically irreducible curve over a field `k`, let `x ∈ K(C)` be
transcendental over `k` and let `B` be the integral closure of `k[x]` in `K(C)`.

This file collects the elementary half of the dictionary between the places `Q` of `C` at which
`x` vanishes (i.e. `ord_Q x > 0`) and the primes of `B` lying over the prime `(x)` of `k[x]`:

* `kxClosure_le_valuationSubring`: `B` is contained in the valuation subring of every place at
  which `x` is regular;
* `kxPrimeOfPlace`: the prime `B ∩ 𝔪_Q` of `B` attached to such a place;
* `kxPrimeOfPlace_liesOver`: for `ord_Q x > 0` it lies over `(x)`;
* `kxPrimeOfPlace_surjective`: every prime of `B` over `(x)` is of this form (using the
  existence of the center of a valuation, `Place.exists_place_of_valuationSubring`).
-/
import Mathlib
import Submission.Work.CurveBasics.Order.Setup
import Submission.Work.CurveBasics.Order.div_algebraMap_eq_zero
import Submission.Work.CurveBasics.Order.ord_lem
import Submission.Work.CurveBasics.Place.mem_valuationSubring_iff
import Submission.Work.CurveBasics.Place.degree_eq_finrank

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Classical IntermediateField.algebraAdjoinAdjoin
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry Polynomial IntermediateField

universe u

namespace Work.CurveBasics

noncomputable section

variable {k : Type u} [Field k]

/-- The integral closure of `k[x]` in the function field, as a subalgebra. -/
abbrev kxInt (C : Curve k) (x : C.functionField) :
    Subalgebra ↥(Algebra.adjoin k ({x} : Set C.functionField)) C.functionField :=
  integralClosure _ _

namespace Curve.Place

/-- Constants of a curve are regular at every place. -/
theorem algebraMap_mem_valuationSubring (C : Curve k) (Q : C.Place) (c : k) :
    algebraMap k C.functionField c ∈ Q.valuationSubring := by
  rw [Place.mem_valuationSubring_iff]
  change 0 ≤ C.ordAt (algebraMap k C.functionField c) Q
  rw [Work.CurveBasics.Order.ordAt_algebraMap_eq_zero]

end Curve.Place

open Curve in
theorem kxClosure_le_valuationSubring (C : Curve k) (x : C.functionField) (Q : C.Place)
    (hQ : 0 ≤ C.ordAt x Q) :
    (kxInt C x).toSubring ≤ Q.valuationSubring.toSubring := by
  intro a ha
  rw [Subalgebra.mem_toSubring] at ha
  rw [ValuationSubring.mem_toSubring]
  have hAV : (Algebra.adjoin k ({x} : Set C.functionField)).toSubring ≤ Q.valuationSubring.toSubring := by
    intro c hc
    rw [Subalgebra.mem_toSubring] at hc
    rw [ValuationSubring.mem_toSubring]
    refine Algebra.adjoin_induction (p := fun y _ => y ∈ Q.valuationSubring) ?_ ?_ ?_ ?_ hc
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      rw [Place.mem_valuationSubring_iff]
      change 0 ≤ C.ordAt x Q
      exact hQ
    · exact fun r => Place.algebraMap_mem_valuationSubring C Q r
    · intro y z _ _ hy hz
      exact Subring.add_mem _ hy hz
    · intro y z _ _ hy hz
      exact Subring.mul_mem _ hy hz
  have hint : IsIntegral ↥(Algebra.adjoin k ({x} : Set C.functionField)) a :=
    (IsIntegralClosure.isIntegral_iff (A := kxInt C x)).mpr ⟨⟨a, ha⟩, rfl⟩
  have hintV : IsIntegral ↥(Q.valuationSubring) a := by
    have h1 : ((algebraMap ↥(Q.valuationSubring) C.functionField)).comp
        (Subring.inclusion hAV)
        = algebraMap ↥(Algebra.adjoin k ({x} : Set C.functionField)) C.functionField := by
      ext c
      exact Subring.coe_inclusion hAV c
    rw [_root_.IsIntegral] at hint ⊢
    rw [← h1] at hint
    exact hint.of_comp
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff (C.functionField)).mp
    (inferInstance : IsIntegrallyClosed ↥(Q.valuationSubring)) hintV
  rw [← hy]
  exact y.2

/-- Membership in the maximal ideal of the valuation subring at a place is positivity of the
order of vanishing (for nonzero elements). -/
theorem mem_maximalIdeal_iff_ord_pos (C : Curve k) (Q : C.Place) (a : ↥(Q.valuationSubring))
    (ha : (a : C.functionField) ≠ 0) :
    a ∈ IsLocalRing.maximalIdeal ↥(Q.valuationSubring) ↔ 0 < C.ordAt (a : C.functionField) Q := by
  have hv0 : Q.valuation (a : C.functionField) ≠ 0 := (Valuation.ne_zero_iff Q.valuation).mpr ha
  have h1 : a ∈ IsLocalRing.maximalIdeal ↥(Q.valuationSubring) ↔
      Q.valuation (a : C.functionField) < 1 :=
    Valuation.mem_maximalIdeal_iff (K := C.functionField) Q.valuation
  rw [h1]
  rw [show C.ordAt (a : C.functionField) Q = -(Q.valuation (a : C.functionField)).log from
      Work.CurveBasics.Curve.Place.ord_eq_neg_log_valuation C Q (a : C.functionField), neg_pos]
  exact ((WithZero.log_lt_iff_lt_exp hv0).trans (by rw [WithZero.exp_zero])).symm

open Curve in
/-- The prime of the integral closure `k[x]^int` attached to a place at which `x` is regular:
the contraction of the maximal ideal of the valuation subring at that place. -/
noncomputable def kxPrimeOfPlace (C : Curve k) (x : C.functionField) (Q : C.Place)
    (hQ : 0 ≤ C.ordAt x Q) : Ideal (kxClosure C x) :=
  Ideal.comap (Subring.inclusion (kxClosure_le_valuationSubring C x Q hQ))
    (IsLocalRing.maximalIdeal ↥(Q.valuationSubring))

open Curve in
theorem kxPrimeOfPlace_isPrime (C : Curve k) (x : C.functionField) (Q : C.Place)
    (hQ : 0 ≤ C.ordAt x Q) : (kxPrimeOfPlace C x Q hQ).IsPrime := by
  exact Ideal.IsPrime.comap (f := Subring.inclusion (kxClosure_le_valuationSubring C x Q hQ))

end

end Work.CurveBasics
