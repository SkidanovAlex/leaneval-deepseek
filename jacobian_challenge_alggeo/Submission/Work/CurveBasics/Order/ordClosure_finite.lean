/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The integral closure of `k[h]` in `K(C)` is a finite `k[h]`-module

Let `C` be a smooth, proper, geometrically irreducible curve over a field `k` and let
`h ∈ K(C)` be transcendental over `k` with `[K(C) : k(h)]` finite.  This file proves that the
integral closure of `k[h]` in `K(C)` is a finite `k[h]`-module
(`Work.CurveBasics.Order.ordClosure_finite`).

The proof splits the finite extension `K(C)/k(h)` along its maximal separable subextension
`M := separableClosure k(h) K(C)`:

* `M/k(h)` is separable, so the integral closure `A_M` of `k[h]` in `M` is a finite `k[h]`-module
  by Mathlib's `IsIntegralClosure.finite` (this is `ordClosure_finite_of_separable`, and the
  corresponding instance is produced in the proof of the main theorem);
* `K(C)/M` is purely inseparable, and there the result is the geometric statement that the
  normalisation of `k[h]` in a purely inseparable extension of function fields is finite; this is
  `Work.CurveBasics.Order.integralClosure_finite_of_pureInseparable_relative`.
-/
import Mathlib
import Submission.Work.CurveBasics.Order.ordPosSetup
import Submission.Work.CurveBasics.Order.Setup
import Submission.Work.CurveBasics.Order.Bridge
import Submission.Work.CurveBasics.Order.integralClosure_finite_of_pureInseparable_relative

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
open scoped IntermediateField.algebraAdjoinAdjoin

namespace Work.CurveBasics.Order

open Work.CurveBasics

/-- **The separable case.** If `K(C)` is separable over `k(h)`, then the integral closure of
`k[h]` in `K(C)` is finite over `k[h]` by Mathlib's `IsIntegralClosure.finite`. -/
theorem ordClosure_finite_of_separable {k : Type*} [Field k] (C : Curve k) (h : C.functionField)
    (hh : Transcendental k h)
    [Algebra.IsSeparable (IntermediateField.adjoin k ({h} : Set C.functionField))
      C.functionField]
    [FiniteDimensional (IntermediateField.adjoin k ({h} : Set C.functionField))
      C.functionField] :
    Module.Finite (C.ordBase h) (C.ordClosure h) :=
  IsIntegralClosure.finite (C.ordBase h)
    (↥(IntermediateField.adjoin k ({h} : Set C.functionField)) : Type _) C.functionField
    (C.ordClosure h)

open Work.CurveBasics in
theorem ordClosure_finite {k : Type*} [Field k] (C : Curve k) (h : C.functionField)
    (hh : Transcendental k h)
    [FiniteDimensional (IntermediateField.adjoin k ({h} : Set C.functionField)) C.functionField] :
    Module.Finite (C.ordBase h) (C.ordClosure h) := by
  classical
  let F : IntermediateField k C.functionField :=
    IntermediateField.adjoin k ({h} : Set C.functionField)
  haveI hFfd : FiniteDimensional ↥F C.functionField := ‹FiniteDimensional
    (IntermediateField.adjoin k ({h} : Set C.functionField)) C.functionField›
  -- the maximal separable subextension of `K(C)/k(h)`
  let M : IntermediateField ↥F C.functionField := separableClosure ↥F C.functionField
  haveI hSep : Algebra.IsSeparable ↥F M := separableClosure.isSeparable ↥F C.functionField
  -- `M` is finite over `k(h)`
  haveI hFDM : FiniteDimensional M C.functionField :=
    Module.Finite.of_restrictScalars_finite (↥F) M C.functionField
  -- the integral closure of `k[h]` in `M` is a finite `k[h]`-module (separable case)
  haveI hFin : Module.Finite (C.ordBase h) (integralClosure (C.ordBase h) ↥M) :=
    IsIntegralClosure.finite (C.ordBase h) ↥F M (integralClosure (C.ordBase h) ↥M)
  -- `K(C)/M` is purely inseparable: every element has a `p ^ n`-th power in `M`
  haveI hAlgAlg : Algebra.IsAlgebraic ↥F C.functionField := Algebra.IsAlgebraic.of_finite _ _
  haveI hPI : IsPurelyInseparable M C.functionField :=
    separableClosure.isPurelyInseparable ↥F C.functionField
  have hpure : ∀ x : C.functionField, ∃ n : ℕ, x ^ ((ringChar k) ^ n) ∈ M := by
    intro x
    rcases CharP.exists' k with h0 | ⟨p, ⟨hpprime⟩, hCharp⟩
    · -- characteristic zero: take `n = 1`, then `x ^ (0 ^ 1) = 1`
      refine ⟨1, ?_⟩
      haveI : CharP k 0 := CharP.ofCharZero k
      rw [ringChar.eq k 0]
      simp
    · -- characteristic `p`
      haveI : CharP k p := hCharp
      haveI hECK : ExpChar k p := .prime hpprime
      haveI hECM : ExpChar M p :=
        expChar_of_injective_ringHom (f := algebraMap k M) (algebraMap k M).injective p
      have hz : ringChar k = p := ringChar.eq k p
      obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem M p x
      obtain ⟨y, hy⟩ := hn
      exact ⟨n, by rw [hz]; exact hy ▸ y.2⟩
  exact integralClosure_finite_of_pureInseparable_relative C h hh M hpure

end Work.CurveBasics.Order
