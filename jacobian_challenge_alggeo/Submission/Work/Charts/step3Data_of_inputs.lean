/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area CH — route B: assembling the inputs `Step3Data` from the named inputs

`Work.Charts.Step3Data R` bundles everything route B needs.  This file shows that it is
*inhabited* from the named inputs that areas `SY`, `RR`, `CB7`, `NM` and `CH` deliver:

* the family of symmetric powers `symGeom : ∀ n, SymGeom C n` (area `SY`);
* the RESID data `ResidData symGeom R.g` (area `DM`);
* `SymProps C g` and `SymProps C (g+g)` (area `SY`): integrality, geometric irreducibility,
  local finiteness of type and quasi-compactness of `Sym^g` and `Sym^{g+g}`;
* area `NM`'s normality of the local rings of `Sym^{g+g} C`;
* the base point `P0 : 𝟙_ (Sch K) ⟶ C.toOver` (areas `GC`/`DS`) together with the Brill–Noether
  chart `BNData C R`.

The constant map `a` is `constMap symGeom g P0` and `ha` is `divOf_constMap`; the base divisor
`P0Div` is `ptDiv` of the base point read as a `K`-point of `C` (`P0DivOf P0`), of degree one
by `ptDiv_deg`.

So **COV′ (route B) consumes exactly the named inputs above**, and nothing else.
-/
import Submission.Work.Charts.Step3Defs
import Submission.Work.Charts.divOf_constMap
import Submission.Work.SpecLin.Points.ptDiv_deg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

namespace Work.Charts

open Work.CurveBasics
open Work.GCBasics

noncomputable section

variable {K : Type u} [Field K]

/-- **The base divisor `[P₀]` has degree one.** -/
theorem Ddeg_P0DivOf {C : Curve K} [Work.SpecLin.DivBase C]
    (P0 : unitSch K ⟶ C.toOver) : Ddeg C K (P0DivOf P0) = 1 :=
  Work.SpecLin.Points.ptDiv_deg (toCurveFPt P0)

/-- **The inputs of route B, built from the named inputs** of areas `SY`, `DM`, `NM` and `CH`
(see the module docstring).  It is a `def` (and not only a `Nonempty`) so that its first
component is *definitionally* the given family `symGeom`, which downstream statements
(`exists_galCharts_of_inputs`) rely on. -/
noncomputable def step3DataOf {C : Curve K} [Work.SpecLin.DivBase C] (R : RochData C)
    (symGeom : ∀ n, Work.SpecLin.SymGeom C n)
    (D : Work.Domain.Resid.ResidData (K := K) symGeom R.g)
    (hprops_g : SymPropsAt symGeom R.g) (hprops_gg : SymPropsAt symGeom (R.g + R.g))
    (hstalk : ∀ x : ((symGeom (R.g + R.g)).S).left,
      IsIntegrallyClosed (((symGeom (R.g + R.g)).S).left.presheaf.stalk x))
    (P0 : unitSch K ⟶ C.toOver) (d : BNDataAt R symGeom) : Step3Data (K := K) R where
  symGeom := symGeom
  resid := D
  geo :=
    { integral_g := hprops_g.isIntegral
      integral_gg := hprops_gg.isIntegral
      separated_g := (Work.SpecLin.SymGeom.isProper (C := C) (n := R.g)).toIsSeparated
      geomIrr_g := hprops_g.geometricallyIrreducible
      geomIrr_gg := hprops_gg.geometricallyIrreducible
      quasiCompact_g := hprops_g.quasiCompact
      locallyOfFiniteType_g := hprops_g.locallyOfFiniteType
      hstalk := hstalk }
  a := constMap symGeom R.g P0 ((symGeom (R.g + R.g)).S)
  P0Div := P0DivOf P0
  hP0 := Ddeg_P0DivOf P0
  ha := fun {F} _ _ p => divOf_constMap symGeom R.g P0 p
  d := d

/-- **Route B's inputs are inhabited** by the named inputs of areas `SY`, `DM`, `NM` and `CH`
(see the module docstring). -/
theorem nonempty_step3Data {C : Curve K} [Work.SpecLin.DivBase C] (R : RochData C)
    (symGeom : ∀ n, Work.SpecLin.SymGeom C n)
    (D : Work.Domain.Resid.ResidData (K := K) symGeom R.g)
    (hprops_g : SymPropsAt symGeom R.g) (hprops_gg : SymPropsAt symGeom (R.g + R.g))
    (hstalk : ∀ x : ((symGeom (R.g + R.g)).S).left,
      IsIntegrallyClosed (((symGeom (R.g + R.g)).S).left.presheaf.stalk x))
    (P0 : unitSch K ⟶ C.toOver) (d : BNDataAt R symGeom) :
    Nonempty (Step3Data (K := K) R) :=
  ⟨step3DataOf R symGeom D hprops_g hprops_gg hstalk P0 d⟩

end

end Work.Charts
