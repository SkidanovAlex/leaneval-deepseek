/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area BNChart (Submission/Work/NOTES_LEAD_jacobian_closure.md §2.B1)

# Area BNChart, B1 — `RochData` for a concrete curve, in successor shape

This file builds the Riemann–Roch input `Work.Charts.RochData C` for a concrete curve
`C : CurveBasics.Curve K`, with the `DivBase` instance being area `SY`'s concrete
`Work.SymQuot.instDivBase` (the ramification-weighted base change of divisors) and the
symmetric powers given by `Work.SymQuot.symGeomFamily`.

The canonical divisor of the data is
`W := (Curve.bcSquare C K).divMap (canonical C) : Dv C K`, i.e. the pullback of a canonical
divisor of `C` along the (identity) base change `C_K ⟶ C`.  Its defining property is that its
pullback along `C_F ⟶ C_K` is again canonical (`RiemannRoch.Curve.isCanonical_divMap`), which
turns the Riemann–Roch equation on `C_F` (`RiemannRoch.Curve.riemannRoch`) into the field `rr`
of `RochData`, because `iOf C W D` is *by definition* the dimension of `L (pullK C W - D)`.

Two forms of the data are provided:

* `rochData C`, with `g := genus C`;
* `rochDataPos C h` (for `h : genus C ≠ 0`), with `g := (genus C - 1) + 1` — the **successor
  shape** which makes `SymQuot.symGeomFamily C R.g` reduce definitionally to
  `instSymGeomOfNeZero`, as required by areas `DM`/`CH`/`GC`.  The two data have the same `W`,
  and `rochDataPos_g` identifies the two genera.
-/
import Submission.Work.Charts.Basic
import Submission.Work.SymQuot.DivBaseInst
import Submission.Work.RiemannRoch.ExportCB
import Submission.Work.RiemannRoch.Canonical.ExistsCanonical
import Submission.Work.RiemannRoch.Canonical.Properties
import Submission.Work.RiemannRoch.RRLib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
open scoped Work.GCBasics

namespace Work.BNChart

open Work.CurveBasics Work.GCBasics Work.Charts

noncomputable section

variable {K : Type u} [Field K]

/-! ### The canonical divisor of the data -/

/-- **The canonical divisor of area `BNChart`**: a canonical divisor of `C`, pulled back along
the base change `C_K ⟶ C` (which is an isomorphism, but not definitionally the identity).
This is an element of `Dv C K = (C.baseChange K).Div`, i.e. a divisor on `C` over the base
field, as `Charts.RochData.W` demands. -/
def rochW (C : Curve K) : Dv C K :=
  (Curve.bcSquare C K).divMap (RiemannRoch.Curve.canonical C)

/-! ### `pullK` of the canonical divisor -/

/-- The tower square of `K → K → F`, in the form in which the concrete `DivBase.bc` unfolds. -/
theorem pullK_rochW (C : Curve K) (F : Type u) [Field F] [Algebra K F] :
    pullK C (rochW C)
      = (SymQuot.DivOf.bcSquareTower (C := C) K F).divMap (rochW C) := by
  show SpecLin.DivBase.bc (IsScalarTower.toAlgHom K K F) (rochW C) = _
  letI : Algebra K F := (IsScalarTower.toAlgHom K K F).toRingHom.toAlgebra
  haveI : IsScalarTower K K F :=
    SymQuot.isScalarTower_of_algHom (IsScalarTower.toAlgHom K K F)
  rfl

/-- **`pullK` of the canonical divisor is the base change of a canonical divisor**: the tower
square `K → K → F` composed with the base-change square `C_K ⟶ C` is the base-change square
`C_F ⟶ C` (the two have the same projection, `towerHom ≫ baseChangeFst C K = baseChangeFst C F`),
and ``divMap`` is compatible with composition of squares. -/
theorem pullK_rochW_bcSquare (C : Curve K) (F : Type u) [Field F] [Algebra K F] :
    pullK C (rochW C) = (Curve.bcSquare C F).divMap (RiemannRoch.Curve.canonical C) := by
  rw [pullK_rochW C F, rochW]
  have hsq : (Curve.bcSquare C K).comp (SymQuot.DivOf.bcSquareTower (C := C) K F)
      = Curve.bcSquare C F :=
    SymQuot.bcSquare_eq_of_pi (by
      show SymQuot.DivOf.BCSquareBaseChange.towerHom (C := C) (F := K) (F' := F)
          ≫ Curve.baseChangeFst C K = Curve.baseChangeFst C F
      exact SymQuot.DivOf.BCSquareBaseChange.towerHom_fst (C := C) (F := K) (F' := F))
  have h := congrArg (fun (g : C.Div →+ (C.baseChange F).Div) =>
      g (RiemannRoch.Curve.canonical C))
    (Curve.BCSquare.divMap_comp (Curve.bcSquare C K)
      (SymQuot.DivOf.bcSquareTower (C := C) K F))
  simp only [AddMonoidHom.comp_apply] at h
  rw [← h, hsq]

/-- **`pullK` of the canonical divisor is canonical on `C_F`.** -/
theorem isCanonical_pullK_rochW (C : Curve K) (F : Type u) [Field F] [Algebra K F] :
    RiemannRoch.Curve.IsCanonical (C.baseChange F) (pullK C (rochW C)) := by
  rw [pullK_rochW_bcSquare C F]
  exact RiemannRoch.Curve.isCanonical_divMap (Curve.bcSquare C F)
    (RiemannRoch.Curve.isCanonical_canonical C)

/-- **`iOf` is the index of speciality of `C_F`.**  Since `pullK C (rochW C)` is canonical on
`C_F`, `iOf C (rochW C) D = ℓ(pullK C (rochW C) - D)` is `i (C_F) D` for every divisor `D` of
`C_F`. -/
theorem iOf_rochW_eq_i (C : Curve K) (F : Type u) [Field F] [Algebra K F] (D : Dv C F) :
    iOf C (rochW C) D = RiemannRoch.Curve.i (C.baseChange F) D :=
  ((isCanonical_pullK_rochW C F) D).symm

/-! ### `RochData` -/

/-- **B1, first form: the Riemann–Roch data of `C`, with `g := genus C`.**

The genus is `RiemannRoch.Curve.genus C`, the canonical divisor is `rochW C`, the
Riemann–Roch equation is `RiemannRoch.Curve.riemannRoch` on `C_F` (with `iOf = i` by
`iOf_rochW_eq_i` and `genus (C_F) = genus C` by `RiemannRoch.Curve.genus_eq`), and RR7 is
`RiemannRoch.Curve.riemann_inequality`. -/
def rochData (C : Curve K) : Charts.RochData C where
  g := RiemannRoch.Curve.genus C
  W := rochW C
  rr := by
    intro F _ _ D
    rw [iOf_rochW_eq_i C F D]
    have h2 := RiemannRoch.Curve.riemannRoch (C.baseChange F) D
    have h3 : RiemannRoch.Curve.genus (C.baseChange F) = RiemannRoch.Curve.genus C :=
      RiemannRoch.Curve.genus_eq (Curve.bcSquare C F)
    have h4 : (C.baseChange F).l D = ell C D := rfl
    have h5 : (C.baseChange F).deg D = Ddeg C F D := rfl
    rw [h3, h4, h5] at h2
    linarith
  ell_pos_of_genus_le_deg := by
    intro F _ _ D hD
    have h3 : RiemannRoch.Curve.genus (C.baseChange F) = RiemannRoch.Curve.genus C :=
      RiemannRoch.Curve.genus_eq (Curve.bcSquare C F)
    have h2 := RiemannRoch.Curve.riemann_inequality (C.baseChange F) D
    have h5 : (C.baseChange F).deg D = Ddeg C F D := rfl
    rw [h5, h3] at h2
    have h1 : (1 : ℤ) ≤ ((C.baseChange F).l D : ℤ) := by linarith
    have h6 : (C.baseChange F).l D = ell C D := rfl
    rw [h6] at h1
    exact_mod_cast h1

@[simp]
theorem rochData_g (C : Curve K) : (rochData C).g = RiemannRoch.Curve.genus C := rfl

@[simp]
theorem rochData_W (C : Curve K) : (rochData C).W = rochW C := rfl

/-! ### Changing the genus, keeping the divisor -/

/-- **The same Riemann–Roch data with a different (equal) genus.**  If `g' = R.g` then `R`
with its `g`-field replaced by `g'` is again Riemann–Roch data: the equation and RR7 only
involve the genus through the cast `(g : ℤ)`. -/
def _root_.Work.Charts.RochData.ofG {C : Curve K} [SpecLin.DivBase C] (R : Charts.RochData C)
    (g' : ℕ) (h : g' = R.g) : Charts.RochData C where
  g := g'
  W := R.W
  rr := by
    intro F _ _ D
    rw [h]
    exact R.rr D
  ell_pos_of_genus_le_deg := by
    intro F _ _ D hD
    rw [h] at hD
    exact R.ell_pos_of_genus_le_deg D hD

@[simp]
theorem _root_.Work.Charts.RochData.ofG_g {C : Curve K} [SpecLin.DivBase C]
    (R : Charts.RochData C) (g' : ℕ) (h : g' = R.g) : (R.ofG g' h).g = g' := rfl

@[simp]
theorem _root_.Work.Charts.RochData.ofG_W {C : Curve K} [SpecLin.DivBase C]
    (R : Charts.RochData C) (g' : ℕ) (h : g' = R.g) : (R.ofG g' h).W = R.W := rfl

/-! ### The successor shape -/

/-- **B1, second form: the Riemann–Roch data in successor shape.**

If the genus of `C` is nonzero, then `(genus C - 1) + 1 = genus C`, so `RochData.ofG` turns
`rochData C` into Riemann–Roch data whose genus is *syntactically* a successor.  This is what
makes `SymQuot.symGeomFamily C R.g` reduce (by `whnf`) to `instSymGeomOfNeZero`, the instance
that areas `DM`, `CH` and `GC` use. -/
def rochDataPos (C : Curve K) (h : RiemannRoch.Curve.genus C ≠ 0) : Charts.RochData C :=
  (rochData C).ofG ((RiemannRoch.Curve.genus C - 1) + 1)
    (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero h))

/-- **The genus of the successor-shaped data is the genus of `C`.** -/
theorem rochDataPos_g (C : Curve K) (h : RiemannRoch.Curve.genus C ≠ 0) :
    (rochDataPos C h).g = RiemannRoch.Curve.genus C :=
  Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero h)

@[simp]
theorem rochDataPos_W (C : Curve K) (h : RiemannRoch.Curve.genus C ≠ 0) :
    (rochDataPos C h).W = rochW C := rfl

/-- The genus of the successor-shaped data is nonzero (indeed it *is* `genus C`), so that
`NeZero` fires for `symGeomFamily`, `instSymGeomOfNeZero` and every consumer of the
successor shape. -/
instance instNeZeroRochDataPos (C : Curve K) (h : RiemannRoch.Curve.genus C ≠ 0) :
    NeZero (rochDataPos C h).g :=
  ⟨by rw [rochDataPos_g C h]; exact h⟩

/-! ### The concrete `ell_bc` of area `CB` -/

/-- **`ℓ` is invariant under the concrete base change of divisors.**  This is
`Work.CurveBasics.Curve.BCSquare.l_divMap` for the tower square of a field extension, read
through `Work.SymQuot.instDivBase`. -/
theorem ell_bc {C : Curve K} {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') (D : Dv C F) :
    ell C (SpecLin.DivBase.bc (C := C) e D) = ell C D := by
  letI : Algebra F F' := e.toRingHom.toAlgebra
  haveI : IsScalarTower K F F' := SymQuot.isScalarTower_of_algHom e
  show (C.baseChange F').l ((SymQuot.DivOf.bcSquareTower (C := C) F F').divMap D) = ell C D
  rw [Curve.BCSquare.l_divMap]
  rfl

end

end Work.BNChart
