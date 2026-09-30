/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area JacFinal (the final assembly: `Work.DescentGeom.Input` from the areas)
-/
import Submission.Work.DescentGeom.All
import Submission.Work.Universal.Main
import Submission.Work.SymQuot.DivBaseInst

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area `JacFinal` — the final assembly

This area is the last step of the drive: it produces, for every `k`-point `P0` of a curve `C/k`,
a chart datum

`Work.DescentGeom.Input C.toOver P0`

— a finite Galois extension `k'/k`, a group chunk `G'` over `k'` with its semilinear Galois
action, and the Abel–Jacobi map with its universal property over `k'` — from which area
`DescentGeom` (`Work.DescentGeom.jacPkgExists_of_inputs`) manufactures the Jacobian package
`Work.Packaging.JacPkg C P0`, i.e. the challenge's `jacPkgExists`.

## What is assumed, and what is built here

`Work.DescentGeom.Input` has exactly one field which is not an output of one of the areas of
the drive: the semilinear **Galois action** `galAct` on the group chunk `G'` and its
compatibility with `μ`, `η`, `ι` and `AJ'`.  Everything else is assembled here from the
outputs of the other areas:

* `G'` and its group structure, properness, geometric integrality and the Abel–Jacobi maps are
  the outputs of area `GC` (the fields of `Work.Universal.Input`, i.e. the "glued group
  chunk" as it is being produced in `Submission/Work/GroupChunk`);
* the symmetric powers and their geometry are the outputs of area `SY`
  (`Work.GroupChunk.Input.symGeom`, the fields of `Work.SpecLin.SymGeom`), the Riemann–Roch
  input is area `RR` (`Work.Charts.RochData`), the Brill–Noether chart is area `CH`
  (`Work.Charts.ChartDatum`), the residue-map engine is area `DM`
  (`Work.Domain.Resid.ResidData`), and the key lemma is area `KL` (the fields `kl`/`kl_add` of
  `Work.Universal.Input`);
* smoothness and connectedness of `G'` are *derived* here from the outputs above
  (`smooth_of_grpObj` and `GeometricallyIrreducible.irreducibleSpace_of_subsingleton`);
* the `Γ`-stable affine cover is a *theorem*: it is proved in `Submission/Work/JacFinal/
  Orbit.lean` (`Work.JacFinal.Inputs.cover_of_chart_orbit`) from the two chart-level items of
  the lead's §1.4 — `IsAffineOpen V` and "the `Γ`-orbit of every point of `G'` lies in the
  range of *one* chart" — via the finite-intersection construction of §1.4(g)
  (`Work.JacFinal.Inputs.cover_of_affine_orbit`);
* `AJ'_pt` is *derived* here from the `GC` output `AJ₀_pt` and the uniqueness of the
  morphism out of the terminal object;
* the universal property `univ'` over `k'` and the generation property `epi'` are *derived*
  here from the corresponding outputs of area `UP` (`Work.Universal.univ`, `Work.Universal.epi`).

## The convention on `G'`

Everything over `k'` is written in the vocabulary of area `DescentGeom`: `Sch k' = Over (Spec k')`,
`bc k' X` for the base change of a `k`-scheme `X`, `galActK k' X σ` for the semilinear Galois
action on `bc k' X`, and `specGal σ` for `Spec σ` read over `Spec k`.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical MonObj MonoidalCategory CategoryTheory
open CartesianMonoidalCategory Functor

universe u

namespace Work.JacFinal

noncomputable section

/-- The category of `k`-schemes (area `GCBasics`' notation, for use inside this area). -/
abbrev Sch (k : Type u) [Field k] : Type (u + 1) := Over (Spec (.of k))

variable {k : Type u} [Field k]

/-- **The base point of `C_{k'}` induced by `P0`**: the inverse of the terminal comparison,
applied to the base change of `P0`.  This is the form in which the base point of the group chunk
over `k'` is used (so that `AJ₀_pt` of area `GC` has the shape of `Work.Universal.Input`). -/
abbrev bcPt (C : CurveBasics.Curve k) (P0 : 𝟙_ (Sch k) ⟶ C.toOver) (k' : Type u) [Field k']
    [Algebra k k'] : 𝟙_ (Sch k') ⟶ (C.baseChange k').toOver :=
  (CartesianMonoidalCategory.preservesTerminalIso (Work.DescentGeom.bcFun k k')).inv ≫
    (Work.DescentGeom.bcFun k k').map P0

/-- **The hypotheses of the final assembly, in the exact current Lean form of the areas of the
drive.**

* `chart : Work.GroupChunk.Input (C_{k'}) (bcPt C P0 k')` — the chart datum over `k'` (areas
  `SY`, `RR`, `CH`, `DM`, bundled by area `GC` as its input interface);
* `exports : Work.Universal.Input (C_{k'}) (bcPt C P0 k')` — the outputs of area `GC` (the
  glued group chunk `G'`: its group law, the universal property of the gluing, the
  Abel–Jacobi maps and their defining properties, properness, geometric integrality) together
  with area `SY`'s quotient property of `Cⁿ ⟶ Symⁿ C` (`SymQuotData`) and area `KL`'s key
  lemma (`kl`, `kl_add`).

The semilinear Galois action on `G'` — the only field of `Work.DescentGeom.Input` which is not
the output of another area — is **constructed** from these two hypotheses in
`Work.JacFinal.GalAct` (`Work.JacFinal.Inputs.toChunk`).
-/
structure Inputs (C : CurveBasics.Curve k) (P0 : 𝟙_ (Sch k) ⟶ C.toOver) where
  /-- the finite Galois extension over which the group chunk is defined -/
  k' : Type u
  [field' : Field k']
  [algebra' : Algebra k k']
  [galois' : IsGalois k k']
  [finiteDimensional' : FiniteDimensional k k']
  /-- **(SY, RR, CH, DM)** the chart datum over `k'` -/
  chart : GroupChunk.Input (C.baseChange k') (bcPt C P0 k')
  /-- **(GC, SY, KL)** the outputs of the areas `GC`, `SY` (quotient property) and `KL` -/
  exports : Universal.Input (C.baseChange k') (bcPt C P0 k')

namespace Inputs

variable {C : CurveBasics.Curve k} {P0 : 𝟙_ (Sch k) ⟶ C.toOver}

instance instField (d : Inputs C P0) : Field d.k' := d.field'
instance instAlgebra (d : Inputs C P0) : Algebra k d.k' := d.algebra'
instance instIsGalois (d : Inputs C P0) : IsGalois k d.k' := d.galois'
instance instFiniteDimensional (d : Inputs C P0) : FiniteDimensional k d.k' := d.finiteDimensional'
instance instChart (d : Inputs C P0) :
    GroupChunk.Input (C.baseChange d.k') (bcPt C P0 d.k') := d.chart
instance instExports (d : Inputs C P0) :
    Universal.Input (C.baseChange d.k') (bcPt C P0 d.k') := d.exports

end Inputs

end

end Work.JacFinal
