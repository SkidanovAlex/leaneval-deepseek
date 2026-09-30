/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area BNChart (Submission/Work/NOTES_LEAD_jacobian_closure.md §2.B5)

# Area BNChart, B5 — RESID data for a concrete curve

`Work.Domain.Resid.ResidData (symGeom) g` bundles the inputs of the residue map of area `DM`:
addition of symmetric powers with its `divOf`-compatibility, RR7 with the degree preserved, the
geometry of `Sym^n C`, invariance of `ℓ` under base change, and specialisation of linear
equivalence along a valuation ring.

This file inhabits it for the *concrete* family `symGeom := SymQuot.symGeomFamily C` of area `SY`
and the genus of a `RochData` of area `BNChart`.  The only work is case analysis on the `match`
in `symGeomFamily`: `SymQuot.symGeomFamily C n` is *definitionally* `Sym C n` in every case, but
the `match` is stuck on a variable `n`, so `addMap` has to be assembled from the four cases
`m = 0, n = 0`, `m = 0, n = l+1`, `m = k+1, n = 0`, `m = k+1, n = l+1`.  The non-zero cases are
area `SY`'s `SymQuot.addMap` with `OfDiv.addMap_divOf`, and the two zero cases are
`OfDiv.addMap_divOf_zero_left` and `OfDiv.addMap_divOf_zero_right`; the target `(m+n)` is again a
successor in every case, so the `match` reduces there by `whnf`.

The same case analysis provides the geometry of `Sym^n C`.
-/
import Submission.Work.BNChart.Basic
import Submission.Work.SymQuot.SymGeomInst
import Submission.Work.SymQuot.OfDiv.addMap_divOf
import Submission.Work.SymQuot.OfDiv.addMap_divOf_zero_left
import Submission.Work.SymQuot.OfDiv.addMap_divOf_zero_right
import Submission.Work.SymQuot.OfDiv.constMap_divOf
import Submission.Work.SymQuot.Sym.curveIso_divOf
import Submission.Work.SymQuot.Sym.symGeom_zero
import Submission.Work.SymQuot.Sym.isProper_sym
import Submission.Work.SymQuot.Sym.locallyOfFiniteType_sym
import Submission.Work.SpecLin.specLin
import Submission.Work.Domain.Resid.Setup
import Submission.Work.Charts.RochData_exists_effective_deg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

namespace Work.BNChart

open Work.CurveBasics Work.GCBasics Work.Charts

noncomputable section

variable {K : Type u} [Field K]

/-- **Addition of symmetric powers, for the concrete family `symGeomFamily`.**  Defined by the
four cases of the `match` in `SymQuot.symGeomFamily`; in each case the target is again a
successor, so the definitional shape of `symGeomFamily` is preserved. -/
noncomputable def addMapFam (C : Curve K) [SymQuot.CurveAffineCover C] (m n : ℕ) :
    (SymQuot.symGeomFamily C m).S ⊗ (SymQuot.symGeomFamily C n).S
      ⟶ (SymQuot.symGeomFamily C (m + n)).S := by
  cases m with
  | zero =>
    cases n with
    | zero => exact SymQuot.addMap C 0 0
    | succ l => exact SymQuot.addMap C 0 (l + 1)
  | succ k =>
    cases n with
    | zero => exact SymQuot.addMap C (k + 1) 0
    | succ l => exact SymQuot.addMap C (k + 1) (l + 1)

variable (C : Curve K) [SymQuot.CurveAffineCover C]

/-- **`divOf` of a sum of points is the sum of the divisors**, for the concrete family: this is
`SymQuot.OfDiv.addMap_divOf` in the four non-degenerate cases and
`addMap_divOf_zero_left`/`addMap_divOf_zero_right` in the degenerate ones. -/
theorem addMapFam_divOf (m n : ℕ) {X : Sch K}
    (u : X ⟶ (SymQuot.symGeomFamily C m).S) (v : X ⟶ (SymQuot.symGeomFamily C n).S)
    {F : Type u} [Field F] [Algebra K F] (p : FPt X F) :
    (SymQuot.symGeomFamily C (m + n)).divOf
        ((p ≫ CartesianMonoidalCategory.liftEquiv (u, v)) ≫ addMapFam C m n)
      = (SymQuot.symGeomFamily C m).divOf (p ≫ u)
        + (SymQuot.symGeomFamily C n).divOf (p ≫ v) := by
  rcases m with _ | k <;> rcases n with _ | l
  · -- `m = 0`, `n = 0`
    show (0 : Dv C F) = 0 + 0
    simp
  · -- `m = 0`, `n = l + 1`
    rw [show addMapFam C 0 (l + 1) = SymQuot.addMap C 0 (l + 1) from rfl]
    exact SymQuot.OfDiv.addMap_divOf_zero_left (C := C) (n := l + 1) u v p
  · -- `m = k + 1`, `n = 0`
    rw [show addMapFam C (k + 1) 0 = SymQuot.addMap C (k + 1) 0 from rfl]
    exact SymQuot.OfDiv.addMap_divOf_zero_right (C := C) (m := k + 1) u v p
  · -- `m = k + 1`, `n = l + 1`
    rw [show addMapFam C (k + 1) (l + 1) = SymQuot.addMap C (k + 1) (l + 1) from rfl]
    exact SymQuot.OfDiv.addMap_divOf (C := C) (m := k + 1) (n := l + 1) u v p

/-- **B5: the RESID data of a concrete curve.**

All the inputs of the residue map of area `DM` for `symGeom := SymQuot.symGeomFamily C` and the
genus `R.g`: `addMapFam` with `addMapFam_divOf`, RR7 with the degree preserved
(`Charts.RochData_exists_effective_deg`), properness and local finiteness of type of `Sym^n C`
(area `SY`, by the same case analysis), invariance of `ℓ` under base change (`ell_bc`, from area
`CB`'s `l_divMap`) and specialisation of linear equivalence (`Work.SpecLin.specLin`). -/
noncomputable def residData (R : RochData C) :
    Domain.Resid.ResidData (K := K) (SymQuot.symGeomFamily C) R.g where
  addMap := addMapFam C
  addMap_divOf := addMapFam_divOf C
  rr7 := fun {F} _ _ D h => Charts.RochData_exists_effective_deg R D h
  isProper := fun n => by
    rcases n with _ | k
    · exact SymQuot.Sym.isProper_sym C 0
    · exact SymQuot.Sym.isProper_sym C (k + 1)
  locallyOfFiniteType := fun n => by
    rcases n with _ | k
    · exact SymQuot.Sym.locallyOfFiniteType_sym C 0
    · exact SymQuot.Sym.locallyOfFiniteType_sym C (k + 1)
  ell_bc := fun _ D => ell_bc _ D
  specLin := fun G R' _ _ _ _ a b h => SpecLin.specLin G R' a b h

/-! ### The remaining `SY`-side data for the concrete family -/

/-- The identification `C ≅ Sym¹ C` of area `SY`, for the concrete family `symGeomFamily`
(`n = 1` is already a successor, so no case analysis is needed here). -/
noncomputable def curveIsoFam (C : Curve K) [SymQuot.CurveAffineCover C] :
    C.toOver ⟶ (SymQuot.symGeomFamily C 1).S :=
  SymQuot.Sym.curveIso C

/-- `divOf` of the point `x ≫ curveIsoFam C` is the point divisor `[x]`. -/
theorem curveIsoFam_divOf (C : Curve K) [SymQuot.CurveAffineCover C] {F : Type u} [Field F]
    [Algebra K F] (x : SpecLin.CurveFPt C F) :
    (SymQuot.symGeomFamily C 1).divOf (x ≫ curveIsoFam C) = SpecLin.ptDiv x :=
  SymQuot.Sym.curveIso_divOf x

/-- **The constant map at an effective divisor of degree `n`**, for the concrete family: the
`n = 0` case is the constant map to the point of `Sym⁰ C`, the others are area `SY`'s
`Sym.constMap`. -/
noncomputable def constMapFam (C : Curve K) [SymQuot.CurveAffineCover C] (n : ℕ) (E : Dv C K)
    (hE : E.IsEffective) (hd : Ddeg C K E = n) (X : Sch K) :
    X ⟶ (SymQuot.symGeomFamily C n).S := by
  cases n with
  | zero => exact SymQuot.Sym.symZeroPt C X
  | succ k => exact SymQuot.Sym.constMap C (k + 1) E hE hd X

/-- `divOf` of a constant map is the base change of the divisor. -/
theorem constMapFam_divOf (C : Curve K) [SymQuot.CurveAffineCover C] (n : ℕ) (E : Dv C K)
    (hE : E.IsEffective) (hd : Ddeg C K E = n) (X : Sch K)
    {F : Type u} [Field F] [Algebra K F] (p : FPt X F) :
    (SymQuot.symGeomFamily C n).divOf (p ≫ constMapFam C n E hE hd X)
      = SpecLin.DivBase.bc (IsScalarTower.toAlgHom K K F) E := by
  cases n with
  | zero =>
    have hE0 : E = 0 :=
      (Work.CurveBasics.Divisor.deg_eq_zero_iff (C := C.baseChange K) hE).mp hd
    subst E
    rw [SpecLin.DivBase.bc_zero]
    exact SymQuot.symGeomZero_divOf C _
  | succ k =>
    rw [show constMapFam C (k + 1) E hE hd X = SymQuot.Sym.constMap C (k + 1) E hE hd X
      from rfl]
    exact SymQuot.OfDiv.constMap_divOf E hE hd X p

end

end Work.BNChart
