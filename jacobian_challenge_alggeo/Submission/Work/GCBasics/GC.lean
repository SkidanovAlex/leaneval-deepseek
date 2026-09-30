/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Work.GC`: the shared conventions under the names used in the lead's notes

`NOTES_LEAD_jacobian_GC.md` §2 writes the shared conventions of area GB in the namespace
`Work.GC` (`Work.GC.Sch`, `Work.GC.specOf`, `Work.GC.RPt`, `Work.GC.FPt`, `Work.GC.Dv`,
`Work.GC.ell`, `Work.GC.LinEquiv`, `Work.GC.Pic0`, ...).  Area GB is implemented in the
namespace `Work.GCBasics`; this file re-exports every name under the `Work.GC` name, as an
`abbrev`, so that the two are definitionally equal and the notes' statements elaborate
verbatim.

Use `open scoped Work.GC` (or `open scoped Work.GCBasics`) for the scoped bridge
`overClass` making every object of `Sch K` a scheme over `Spec K`.

Namespaced lemmas (`RPt.map`, `RPt.LandsIn`, `RPt.factor_of_closed_landsIn`,
`FPt.factor_of_landsIn`, `FPt.tensorEquiv`, `LinEquiv.refl`, `LinEquiv.symm`, ...,
`Pic0.mk`, `Pic.mk`) are reached through dot notation: for `p : Work.GC.FPt X F` the
expression `p.LandsIn U` resolves to `Work.GCBasics.RPt.LandsIn p U`, because `Work.GC.FPt`
is an `abbrev` for `Work.GCBasics.FPt`.
-/
import Submission.Work.GCBasics.Basic
import Submission.Work.GCBasics.Points
import Submission.Work.GCBasics.DivApi
import Submission.Work.GCBasics.DivBaseChange

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.GC

noncomputable section

variable {K : Type u} [Field K]

/-- The category of `K`-schemes, i.e. `Work.GCBasics.Sch K`. -/
abbrev Sch (K : Type u) [Field K] : Type (u + 1) := Work.GCBasics.Sch K

/-- `Spec R` as a `K`-scheme, i.e. `Work.GCBasics.specOf K R`. -/
abbrev specOf (K : Type u) [Field K] (R : Type u) [CommRing R] [Algebra K R] : Sch K :=
  Work.GCBasics.specOf K R

/-- `R`-valued points of a `K`-scheme, i.e. `Work.GCBasics.RPt`. -/
abbrev RPt (X : Sch K) (R : Type u) [CommRing R] [Algebra K R] : Type u :=
  Work.GCBasics.RPt X R

/-- `F`-valued points of a `K`-scheme, i.e. `Work.GCBasics.FPt`. -/
abbrev FPt (X : Sch K) (F : Type u) [Field F] [Algebra K F] : Type u :=
  Work.GCBasics.FPt X F

/-- Divisors of `C` over `F`, i.e. `Work.GCBasics.Dv`. -/
abbrev Dv (C : Work.CurveBasics.Curve K) (F : Type u) [Field F] [Algebra K F] : Type u :=
  Work.GCBasics.Dv C F

/-- The degree of a divisor over `F`, i.e. `Work.GCBasics.Ddeg`. -/
abbrev Ddeg (C : Work.CurveBasics.Curve K) (F : Type u) [Field F] [Algebra K F] :
    Dv C F →+ ℤ :=
  Work.GCBasics.Ddeg C F

/-- `ℓ(D) = dim_F L(D)`, i.e. `Work.GCBasics.ell`. -/
abbrev ell (C : Work.CurveBasics.Curve K) {F : Type u} [Field F] [Algebra K F]
    (D : Dv C F) : ℕ :=
  Work.GCBasics.ell C D

/-- Linear equivalence of divisors, i.e. `Work.GCBasics.LinEquiv`. -/
abbrev LinEquiv (C : Work.CurveBasics.Curve K) {F : Type u} [Field F] [Algebra K F]
    (D D' : Dv C F) : Prop :=
  Work.GCBasics.LinEquiv C D D'

/-- The subgroup of principal divisors, i.e. `Work.GCBasics.prin`. -/
abbrev prin (C : Work.CurveBasics.Curve K) (F : Type u) [Field F] [Algebra K F] :
    AddSubgroup (Dv C F) :=
  Work.GCBasics.prin C F

/-- The divisor class group, i.e. `Work.GCBasics.Pic`. -/
abbrev Pic (C : Work.CurveBasics.Curve K) (F : Type u) [Field F] [Algebra K F] : Type u :=
  Work.GCBasics.Pic C F

/-- The group of divisor classes of degree zero, i.e. `Work.GCBasics.Pic0`. -/
abbrev Pic0 (C : Work.CurveBasics.Curve K) (F : Type u) [Field F] [Algebra K F] : Type u :=
  Work.GCBasics.Pic0 C F

/-- The residue field of a point, i.e. `Work.GCBasics.resField`. -/
abbrev resField (X : Sch K) (x : X.left) : Type u := Work.GCBasics.resField X x

/-- The canonical `κ(x)`-point of `X`, i.e. `Work.GCBasics.resPt`. -/
abbrev resPt (X : Sch K) (x : X.left) : FPt X (resField X x) := Work.GCBasics.resPt X x

/-- The generic point of `Spec R` over `Frac R`, i.e. `Work.GCBasics.genPt`. -/
abbrev genPt (R : Type u) [CommRing R] [IsDomain R] [Algebra K R] :
    FPt (specOf K R) (FractionRing R) :=
  Work.GCBasics.genPt R

/-- The closed point of `Spec R` over `R ⧸ m`, i.e. `Work.GCBasics.closedPt`. -/
abbrev closedPt (R : Type u) [CommRing R] [IsLocalRing R] [Algebra K R] :
    FPt (specOf K R) (IsLocalRing.ResidueField R) :=
  Work.GCBasics.closedPt R

/-- The generic point of an integral `K`-scheme, as a point over its function field, i.e.
`Work.GCBasics.genericFPt`. -/
abbrev genericFPt (X : Sch K) [IsIntegral X.left] : FPt X X.left.functionField :=
  Work.GCBasics.genericFPt X

/-- A valuation subring dominating the local ring at a point, i.e.
`Work.GCBasics.Dominates`. -/
abbrev Dominates {X : Scheme.{u}} [IsIntegral X] (A : ValuationSubring X.functionField)
    (x : X) : Prop :=
  Work.GCBasics.Dominates A x

/-- The scoped bridge making every object of `Sch K` a scheme over `Spec K`; this is the
`Work.GC.overClass` of the shared conventions. -/
scoped instance overClass (X : Sch K) : X.left.Over (Spec (CommRingCat.of K)) := ⟨X.hom⟩

end

end Work.GC
