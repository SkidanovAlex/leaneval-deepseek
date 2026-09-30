/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area CH — route B: COV′ (`ExistsGalCharts`) over the base field

This is the **main theorem of route B** (`Submission/Work/NOTES_LEAD_jacobian_charts3.md` §4):
from the inputs `Step3Data R` (the symmetric powers, RESID, the geometry of `Sym^g` and
`Sym^{g+g}`, area `NM`'s normality, the constant map at `g·P₀` and the Brill–Noether chart) and
the base point `P0`, there is a finite Galois extension `k'` of `K` with finitely many centres
`E₀ : ι₀ → Sym^g C(k')` whose full `Gal(k'/k')`-orbits cover every degree-zero class of `C`
over every `K`-algebra receiving `k'` — i.e. `GalCharts C R P0`, the covering COV′ consumed by
area `DS`.

It is `galCharts_of_orbit_cover` applied to `exists_orbit_cover` (the finite-subcover
assembly of `Ω_E`), and `exists_galCharts_of_inputs` specialises the inputs to the *named*
inputs of areas `SY`, `DM`, `NM` and `CH` via `nonempty_step3Data`.
-/
import Submission.Work.Charts.Step3Defs
import Submission.Work.Charts.Step3Cover
import Submission.Work.Charts.exists_orbit_cover
import Submission.Work.Charts.step3Data_of_inputs
import Submission.Work.Charts.galCharts_of_orbit_cover
import Submission.Work.Charts.nonempty_BNData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

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

variable {K : Type u} [Field K] {C : Curve K} [Work.SpecLin.DivBase C]

/-- **COV′** (route B of the lead's design): from the inputs `Step3Data` and the base point
`P0`, the Galois-equivariant covering `GalCharts C R P0` of `Pic⁰` by translates of the
Brill–Noether chart exists over a finite Galois extension `k'` of `K`. -/
theorem exists_galCharts (R : RochData C) (I : Step3Data R) (P0 : unitSch K ⟶ C.toOver) :
    Nonempty (@GalCharts K _ C _ R (I.symGeom R.g) P0) := by
  letI := I.symGeom R.g
  obtain ⟨k', hfin, hgal, ι₀, hft, E₀, hcover⟩ := exists_orbit_cover R I
  haveI := hfin
  haveI := hgal
  exact galCharts_of_orbit_cover R ↥k' I.d E₀ hcover

/-- **COV′ from the named inputs.**  For a curve `C/K` with

* a family of symmetric powers `symGeom` (area `SY`),
* the RESID data `D` for the genus `g` (area `DM`),
* `SymProps` for `g` and `g+g` (area `SY`),
* area `NM`'s normality of the local rings of `Sym^{g+g} C`,
* the base point `P0`,
* the Brill–Noether chart `d` (area `CH`),

the Galois-equivariant covering `GalCharts C R P0` exists. -/
theorem exists_galCharts_of_inputs (R : RochData C) (symGeom : ∀ n, Work.SpecLin.SymGeom C n)
    (D : Work.Domain.Resid.ResidData (K := K) symGeom R.g)
    (hprops_g : SymPropsAt symGeom R.g) (hprops_gg : SymPropsAt symGeom (R.g + R.g))
    (hstalk : ∀ x : ((symGeom (R.g + R.g)).S).left,
      IsIntegrallyClosed (((symGeom (R.g + R.g)).S).left.presheaf.stalk x))
    (P0 : unitSch K ⟶ C.toOver) (d : BNDataAt R symGeom) :
    Nonempty (@GalCharts K _ C _ R (symGeom R.g) P0) :=
  exists_galCharts R (step3DataOf R symGeom D hprops_g hprops_gg hstalk P0 d) P0

/-- **COV′ with the chart built from its defining data.**  Same as `exists_galCharts_of_inputs`,
but the Brill–Noether chart is no longer an input: it is *constructed* by
`nonempty_BNData_of_basis` from the place `Q`, the affine open `U` carrying the sections
`s : Fin g → Γ(C,U)`, the basis data of `L(W)`, the determinant criterion `hcrit` and the
existence `hnonspec` of a non-special degree-`g` divisor supported in `U` (RR6). -/
theorem exists_galCharts_of_basis {C : Curve K} [Work.SpecLin.DivBase C] (R : RochData C)
    (symGeom : ∀ n, Work.SpecLin.SymGeom C n)
    (D : Work.Domain.Resid.ResidData (K := K) symGeom R.g)
    (hprops_g : SymPropsAt symGeom R.g) (hprops_gg : SymPropsAt symGeom (R.g + R.g))
    (hstalk : ∀ x : ((symGeom (R.g + R.g)).S).left,
      IsIntegrallyClosed (((symGeom (R.g + R.g)).S).left.presheaf.stalk x))
    (P0 : unitSch K ⟶ C.toOver) (U : C.left.Opens) (hU : IsAffineOpen U) (Q : C.Place)
    (h : Fin R.g → (C.baseChange K).functionField)
    (h_mem : ∀ j, 0 ≤ (C.baseChange K).div (h j) + R.W)
    (h_span : (C.baseChange K).L R.W = Submodule.span K (Set.range h))
    (s : Fin R.g → (C.left.presheaf.obj (Opposite.op U)))
    (hcrit : ∀ {F : Type u} [Field F] [Algebra K F]
      (p : FPt (Cprod C R.g) F) (hp : RPt.LandsIn p (cgOpen C U R.g)),
      (Matrix.det (Matrix.of (fun j m => evalSection (coord p m).left
        (coord_landsIn hp m) (s j)))) ≠ 0 ↔
        iOf C R.W (Work.SpecLin.SymGeom.divOf (ptComp p (quotMap C R.g))) = 0)
    (hnonspec : ∃ (F : Type u) (_ : Field F) (_ : Algebra K F)
      (p : FPt (Cprod C R.g) F) (hp : RPt.LandsIn p (cgOpen C U R.g)),
      iOf C R.W (Work.SpecLin.SymGeom.divOf (ptComp p (quotMap C R.g))) = 0) :
    Nonempty (@GalCharts K _ C _ R (symGeom R.g) P0) := by
  letI := symGeom R.g
  exact exists_galCharts R
    (step3DataOf R symGeom D hprops_g hprops_gg hstalk P0
      (Classical.choice
        (nonempty_BNData_of_basis R U hU Q h h_mem h_span s hcrit hnonspec D.ell_bc)))
    P0

end

end Work.Charts
