/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The divisor of an `F`-point of a curve (area SpecLin)

An `F`-point `p` of a curve `C` over `K` (a morphism `Spec F ⟶ C` over `Spec K`) induces a
*closed* point `ptPlace p` of the base-changed curve `C_F` (proved in
`Submission/Work/SpecLin/Points/ptToPoint_isClosed.lean`) and hence a divisor `ptDiv p = [p]` on
`C_F`.  This is the "point divisor" appearing in the interface `Work.SpecLin.SymGeom` (area `SY`)
and in the statement of specialisation of linear equivalence.

A divisor of the form `ptDiv p` is effective and nonzero, so `F`-points of `C` correspond to
*degree-one* effective divisors of `C_F` (over the interface `SymGeom` this dictionary is
`SymGeom.ptDiv`, available for every field extension of `K`).
-/
import Submission.Work.SpecLin.Points.Setup
import Submission.Work.SpecLin.Points.ptToPoint_isClosed

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.SpecLin

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {F : Type u} [Field F]
  [Algebra K F]

/-- The place of `C_F` attached to an `F`-point of `C`. -/
noncomputable def ptPlace (p : CurveFPt C F) : (C.baseChange F).Place :=
  ⟨ptToPoint p, Work.SpecLin.Points.ptToPoint_isClosed p⟩

/-- The divisor `[p]` of an `F`-point of `C`, as a divisor on `C_F`. -/
noncomputable def ptDiv (p : CurveFPt C F) : Dv C F :=
  Work.CurveBasics.Curve.Div.place (ptPlace p)

theorem ptDiv_apply (p : CurveFPt C F) (Q : (C.baseChange F).Place) :
    ptDiv p Q = if ptPlace p = Q then 1 else 0 := by
  rw [ptDiv, Work.CurveBasics.Curve.Div.place, Finsupp.single_apply]

theorem ptDiv_isEffective (p : CurveFPt C F) : (ptDiv p).IsEffective := by
  intro Q
  rw [ptDiv_apply]
  by_cases h : ptPlace p = Q <;> simp [h]

theorem ptDiv_ne_zero (p : CurveFPt C F) : ptDiv p ≠ 0 := by
  intro h
  have h1 := ptDiv_apply p (ptPlace p)
  rw [h] at h1
  norm_num at h1

/-- `ptDiv` is the same as the divisor of the place, so two `F`-points with the same point
divisor have the same place. -/
theorem ptPlace_eq_of_ptDiv_eq {p q : CurveFPt C F} (h : ptDiv p = ptDiv q) :
    ptPlace p = ptPlace q := by
  by_contra hne
  have h1 : (ptDiv q) (ptPlace p) = 1 := by
    have hh := ptDiv_apply p (ptPlace p)
    rw [h] at hh
    simpa using hh
  have h2 : (ptDiv q) (ptPlace p) = 0 := by
    have hh := ptDiv_apply q (ptPlace p)
    rw [if_neg (show ¬ (ptPlace q = ptPlace p) from fun h' => hne h'.symm)] at hh
    exact hh
  rw [h2] at h1
  exact one_ne_zero h1.symm

end Work.SpecLin
