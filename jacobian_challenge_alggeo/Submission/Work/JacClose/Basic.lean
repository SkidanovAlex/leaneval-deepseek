/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area JacClose (Submission/Work/NOTES_LEAD_jacobian_closure.md §2.C1)
-/
import Submission.Work.Charts.GalCharts_toCharts
import Submission.Work.BcDiv.All
import Submission.Work.SymQuot.SymGeomInst

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area JacClose — shared vocabulary

This file collects the definitions of area `JacClose` that are used by more than one of its
files.  It contains the C1 naming data of `Work.BcDiv.symBC`.

## C1: the naming data of the base-change comparison of symmetric powers

`Work.Charts.SymBC` — the bundle that compares the symmetric powers of `C` and of `C_L` — is
built by area `BcDiv`'s `Work.BcDiv.symBC` from five pieces of *naming data* on `C_L`: a place
`Q'`, an affine open `U'`, and a basis `h'` of the Riemann–Roch space `L(R'.W)`, together with
the two facts that the basis lies in `L(R'.W)` and spans it.  Nothing on disk produces them;
`Work.JacClose.SymBCNaming` is that data, and `Work.JacClose.nonempty_symBCNaming` (in
`Submission/Work/JacClose/Naming.lean`) proves it exists.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

namespace Work.JacClose

open Work.CurveBasics
open Work.GCBasics

noncomputable section

variable {K : Type u} [Field K] {C : Curve K} [Work.SpecLin.DivBase C]

/-- **C1: the naming data of `Work.BcDiv.symBC`.**  For a `RochData` `R'` on the base change
`C_L`, the five pieces of data from which `Work.BcDiv.symBC` assembles the comparison
`Work.Charts.SymBC R L R'` of symmetric powers: a place `Q'` of `C_L`, an affine open `U'` of
`C_L`, and a basis `h' : Fin R'.g → K(C_L)` of the Riemann–Roch space of the canonical divisor
`R'.W` (with the two facts that its elements lie in that space and that they span it).

It is `exists_namingData` of the lead's §2.C1. -/
structure SymBCNaming (C : Curve K) {L : Type u} [Field L] [Algebra K L]
    (R' : Work.Charts.RochData (C.baseChange L)) where
  /-- a place of `C_L` -/
  Q' : (C.baseChange L).Place
  /-- an affine open of `C_L` -/
  U' : (C.baseChange L).left.Opens
  /-- it is affine -/
  hU' : IsAffineOpen U'
  /-- a basis of the Riemann–Roch space of the canonical divisor -/
  h' : Fin R'.g → ((C.baseChange L).baseChange L).functionField
  /-- the basis elements lie in the Riemann–Roch space -/
  h_mem' : ∀ j, (0 : ((C.baseChange L).baseChange L).Div)
    ≤ ((C.baseChange L).baseChange L).div (h' j) + R'.W
  /-- the basis elements span the Riemann–Roch space -/
  h_span' : ((C.baseChange L).baseChange L).L R'.W = Submodule.span L (Set.range h')

/-! ## The tensor product of two symmetric powers -/

/-- The tensor product `Sym^m C ⊗ Sym^n C` of two symmetric powers, as a `K`-scheme.  Written
with an explicit name because it occurs in the statement of the two normality fields
(`Work.JacClose.normal_sym_tensor`) that area `GC` needs once its RESID interface is
corrected. -/
abbrev SymTensor {K : Type u} [Field K] (C : Curve K) (m n : ℕ) : Work.SpecLin.Sch K :=
  Work.SymQuot.Sym C m ⊗ Work.SymQuot.Sym C n

end

end Work.JacClose
