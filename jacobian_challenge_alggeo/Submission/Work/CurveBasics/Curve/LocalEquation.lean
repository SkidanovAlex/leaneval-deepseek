/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A rational function is locally given by a pair of regular functions

Let `C` be a curve over `k` and `h ∈ K(C)^*`.  For every point `z` of `C` there is an affine open
`W ∋ z` and a pair `(a, b) ≠ (0,0)` of rational functions regular on `W` with `a·h = b`.  In
other words, the rational function `h` defines a rational map `C ⇢ ℙ¹` (sending `z` to
`[a(z) : b(z)]`) which is *defined at every point* of `C`.

This is the coordinate form of the statement that a rational map from a smooth proper curve to a
proper target extends to a morphism: here the local defining pairs `(a, b)` (taken from the
"numerator/denominator" description of `h`) glue, since `a·h = b` pins the point `[a : b]` of
`ℙ¹` down to `[1 : h]` (or `[0 : 1]` at a pole of `h`, which is the point at infinity).

## Main result

* `Work.CurveBasics.Curve.exists_local_equation_pair`
-/
import Submission.Work.CurveBasics.BaseChange.exists_affine_nbhd
import Submission.Work.CurveBasics.Order.div_algebraMap_eq_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.CurveBasics

namespace Curve

variable {k : Type u} [Field k]

/-- Every nonzero rational function of a curve is, in a neighbourhood of any point, the ratio of
two functions regular there: there are an affine open `W ∋ z` and `(a, b) ≠ (0,0)`, regular on
`W`, with `a * h = b`. -/
theorem exists_local_equation_pair {C : Curve k} {h : C.functionField} (hh : h ≠ 0)
    (z : C.left) :
    ∃ W : C.left.Opens, AlgebraicGeometry.IsAffineOpen W ∧ z ∈ W ∧
      ∃ a b : C.functionField, (a, b) ≠ (0, 0) ∧ C.RegularOn W a ∧ C.RegularOn W b ∧
        a * h = b := by
  obtain ⟨W, hWaff, hzW, hW⟩ := BaseChange.exists_affine_nbhd h hh z
  have hone : C.RegularOn W (1 : C.functionField) := fun Q _ => by
    have h1 : (1 : C.functionField) = algebraMap k C.functionField 1 := by simp
    rw [h1, Work.CurveBasics.Order.ordAt_algebraMap_eq_zero]
  rcases hW with hreg | hinv
  · exact ⟨W, hWaff, hzW, 1, h, by simp, hone, hreg, one_mul h⟩
  · exact ⟨W, hWaff, hzW, h⁻¹, 1, by simp, hinv, hone, inv_mul_cancel₀ hh⟩

end Curve

end Work.CurveBasics
