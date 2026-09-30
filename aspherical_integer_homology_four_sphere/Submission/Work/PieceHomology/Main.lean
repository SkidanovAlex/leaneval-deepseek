/-
# `PieceHomology/`: the challenge theorem from the three homology computations and the bridge

This is the headline of the area: from

* `CuspModels` (or `DeltaCuspModels`) — the three homology computations of the geometry, per cusp
  (`H_k(∂[-1,1]² × T²_v)`, `H_k(M̄)`, `H_k(T²_v)`), and
* `Bridge` — the chain-level bridge data (the subdivision maps and the witnesses of
  `rtdata/data/mv_certificate.json`),

we build the declared structures `Work.HomologyIso.CuspData`, `Work.HomologyIso.CuspInputs`,
`Work.HomologyIso.Inputs`, then `Work.Final.FinalInputs`, and finally the challenge theorem
`∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere`.

The only remaining inputs are `Work.HomologyIso.Remaining` (the assembled space `M̂`, the
smoothness of its Levi-Civita connection and the curvature bound) — everything else is supplied
here.

## Names

* `Work.PieceHomology.cuspData`, `Work.PieceHomology.cuspInputs`, `Work.PieceHomology.inputs`;
* `Work.PieceHomology.deltaCuspInputs`, `Work.PieceHomology.deltaPieceInputs` — the same from
  `Δ`-complex models;
* `Work.PieceHomology.finalInputsOfCusps`, `Work.PieceHomology.finalInputs`;
* `Work.PieceHomology.aspherical_integer_homology_four_sphere`.
-/
import Submission.Work.PieceHomology.Bridge

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open LeanEval.Topology
open scoped Topology

namespace Work.PieceHomology

noncomputable section

variable [rt : Work.Space.RTData]

/-! ## §1  The declared inputs of `Work.HomologyIso` -/

/-- **The declared fields of `Work.HomologyIso.CuspData` from the per-cusp models.** -/
def cuspData (D : CuspModels (rt := rt)) : Work.HomologyIso.CuspData (rt := rt) :=
  D.toCuspData

/-- **The per-cusp inputs of the area** (`Work.HomologyIso.CuspInputs`): the per-cusp models and
the bridge. -/
def cuspInputs (D : CuspModels (rt := rt)) (B : Bridge (rt := rt) D.toCuspData.toPieceData) :
    Work.HomologyIso.CuspInputs (rt := rt) :=
  Bridge.toCuspInputs D.toCuspData B

/-- **The per-cusp inputs from `Δ`-complex models.** -/
def deltaCuspInputs (D : DeltaCuspModels (rt := rt))
    (B : Bridge (rt := rt) D.toCuspData.toPieceData) :
    Work.HomologyIso.CuspInputs (rt := rt) :=
  Bridge.toCuspInputs D.toCuspData B

/-- **The declared fields of `Work.HomologyIso.Inputs`** (the unrefined form): the models of the
three pieces and the bridge. -/
def inputs (D : PieceModels (rt := rt)) (B : Bridge (rt := rt) D.toPieceData) :
    Work.HomologyIso.Inputs (rt := rt) :=
  Bridge.toInputs D.toPieceData B

/-- **The inputs from `Δ`-complex models.** -/
def deltaPieceInputs (D : DeltaPieceModels (rt := rt))
    (B : Bridge (rt := rt) D.toPieceData) : Work.HomologyIso.Inputs (rt := rt) :=
  Bridge.toInputs D.toPieceData B

/-! ## §2  The final assembly -/

/-- **`Work.Final.FinalInputs` from the remaining inputs and the per-cusp data**: this is
`Work.HomologyIso.finalInputs_of_cusps` applied to the `CuspInputs` built here. -/
def finalInputsOfCusps (R : Work.HomologyIso.Remaining (rt := rt)) (D : CuspModels (rt := rt))
    (B : Bridge (rt := rt) D.toCuspData.toPieceData) : Work.Final.FinalInputs :=
  Work.HomologyIso.finalInputs_of_cusps R (cuspInputs D B)

/-- The same, from the unrefined (per-piece) models. -/
def finalInputs (R : Work.HomologyIso.Remaining (rt := rt)) (D : PieceModels (rt := rt))
    (B : Bridge (rt := rt) D.toPieceData) : Work.Final.FinalInputs :=
  Work.HomologyIso.finalInputs R (inputs D B)

/-- The `L` field of the assembled instance is the Mayer–Vietoris sequence of the area
`Work.HomologyIso` (definitional). -/
theorem finalInputsOfCusps_L (R : Work.HomologyIso.Remaining (rt := rt)) (D : CuspModels (rt := rt))
    (B : Bridge (rt := rt) D.toCuspData.toPieceData) :
    (finalInputsOfCusps R D B).L = Work.HomologyIso.mhatLES (rt := rt) := rfl

/-! ## §3  The challenge theorem -/

/-- **The challenge theorem, from the remaining inputs and the data of this area.** -/
theorem aspherical_integer_homology_four_sphere
    (R : Work.HomologyIso.Remaining (rt := rt)) (D : CuspModels (rt := rt))
    (B : Bridge (rt := rt) D.toCuspData.toPieceData) :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere :=
  Work.HomologyIso.aspherical_integer_homology_four_sphere_of_cusps R (cuspInputs D B)

/-- The same, from `Δ`-complex models. -/
theorem aspherical_integer_homology_four_sphere_of_delta
    (R : Work.HomologyIso.Remaining (rt := rt)) (D : DeltaCuspModels (rt := rt))
    (B : Bridge (rt := rt) D.toCuspData.toPieceData) :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere :=
  Work.HomologyIso.aspherical_integer_homology_four_sphere_of_cusps R (deltaCuspInputs D B)

end

end Work.PieceHomology
