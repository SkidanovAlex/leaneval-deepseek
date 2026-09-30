/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The order of vanishing at a place: basic API

This file collects the elementary API of `Scheme.ord` specialised to the places of a curve:
it vanishes on nonzero constants and on the negatives of units, and it is multiplicative.
-/
import Submission.Work.CurveBasics.Order

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

instance instNonemptyOpensTop (C : Curve k) : Nonempty (⊤ : C.left.Opens) :=
  ⟨⟨genericPoint C.left, trivial⟩⟩

/-- The order of vanishing of `1`. -/
theorem ordAt_one (C : Curve k) (Q : C.Place) : C.ordAt (1 : C.functionField) Q = 0 := by
  have h : (1 : C.functionField) = C.germToFunctionField ⊤ (1 : Γ(C.left, ⊤)) := by
    rw [map_one]
  rw [h, ordAt]
  exact Scheme.ord_of_isUnit isUnit_one (show Q.point ∈ (⊤ : C.left.Opens) from trivial)

/-- The order of vanishing at a place is multiplicative. -/
theorem ordAt_mul (C : Curve k) {f g : C.functionField} (hf : f ≠ 0) (hg : g ≠ 0)
    (Q : C.Place) : C.ordAt (f * g) Q = C.ordAt f Q + C.ordAt g Q :=
  Scheme.ord_mul hf hg

/-- The order of vanishing of the image of a nonzero constant is zero. -/
theorem ordAt_algebraMap (C : Curve k) {c : k} (hc : c ≠ 0) (Q : C.Place) :
    C.ordAt (algebraMap k C.functionField c) Q = 0 := by
  have hunit : IsUnit (C.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) := by
    set a := C.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) with ha
    have hprod : a * C.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c⁻¹) = 1 := by
      rw [ha, ← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one]
    exact ⟨Units.mkOfMulEqOne a _ hprod, rfl⟩
  have h : algebraMap k C.functionField c =
      C.germToFunctionField ⊤
        (C.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) := rfl
  rw [h, ordAt]
  exact Scheme.ord_of_isUnit hunit (show Q.point ∈ (⊤ : C.left.Opens) from trivial)

/-- `ord` at a place is invariant under negation. -/
theorem ordAt_neg (C : Curve k) (f : C.functionField) (Q : C.Place) :
    C.ordAt (-f) Q = C.ordAt f Q := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have h : (-f : C.functionField) = (-1 : C.functionField) * f := by ring
  rw [h, C.ordAt_mul (by simp) hf]
  have hneg : C.ordAt (-1 : C.functionField) Q = 0 := by
    have h1 : (-1 : C.functionField) = C.germToFunctionField ⊤ (-1 : Γ(C.left, ⊤)) := by
      rw [map_neg, map_one]
    rw [h1, ordAt]
    exact Scheme.ord_of_isUnit (isUnit_one.neg)
      (show Q.point ∈ (⊤ : C.left.Opens) from trivial)
  rw [hneg, zero_add]

/-- The order of vanishing of the inverse. -/
theorem ordAt_inv (C : Curve k) {f : C.functionField} (hf : f ≠ 0) (Q : C.Place) :
    C.ordAt f⁻¹ Q = -C.ordAt f Q := by
  have h := C.ordAt_mul hf (inv_ne_zero hf) Q
  rw [mul_inv_cancel₀ hf, C.ordAt_one Q] at h
  linarith

end

end Curve

end Work.CurveBasics
