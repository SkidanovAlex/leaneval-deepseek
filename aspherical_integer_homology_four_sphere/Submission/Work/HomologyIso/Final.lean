/-
# `HomologyIso/`: the complete `Work.Final.FinalInputs` from this area's data

`Work.Final.FinalInputs` has eight fields.  Three of them are the subject of this area
(`eM`, `eN`, `hsq` for `L = mhatLES`), two more are constructed inside `Work.Final` *without* any
input (`L` itself, and `hX`), and the three remaining ones are the assembled space
(`Work.Space.RTData`), the smoothness of its Levi-Civita connection, and the curvature bound.

This file records that, with the sequence `mhatLES` of this area in place of the field `L`, the
structuring of `FinalInputs` reduces to those three:

```lean
structure Work.HomologyIso.Remaining (rt : Work.Space.RTData) where
  [cov_smooth : CovariantDerivative.ContMDiffCovariantDerivative (Work.Final.mhatCov (rt := rt)) ∞]
  curvLe : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe (Work.Final.mhatCov (rt := rt)) K

def Work.HomologyIso.finalInputs (R : Remaining rt) (I : Inputs rt) : Work.Final.FinalInputs
```

so that the whole challenge becomes

```lean
instance : Work.Final.FinalInputs :=
  Work.HomologyIso.finalInputs R I          -- R : Remaining rt, I : Inputs rt
theorem aspherical_integer_homology_four_sphere : … :=
  Work.Final.aspherical_integer_homology_four_sphere
```

(The `L`, `eM`, `eN`, `hsq`, `hX` fields are *definitionally* the ones of this area: see
`Submission/Work/HomologyIso/Check.lean`.)
-/
import Submission.Work.HomologyIso.Main
import Submission.Work.HomologyIso.CuspData

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open LeanEval.Topology
open CategoryTheory CategoryTheory.Limits
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace Work.HomologyIso

noncomputable section

variable [rt : Work.Space.RTData]

/-- **The `(k,2)`-slot of `mhatLES` is the singular homology of `M̂`**, built without any
`FinalInputs` instance (`Work.Final.FinalInputs.mhatLES_hX` is the same statement with the
instance). -/
def mhatLES_hX (k : ℕ) :
    (mhatLES (rt := rt)).H ((k : ℤ), 2) ≅ intHomology k (TopCat.of rt.Mhat) :=
  Work.Final.mhatMVLES_hX (rt := rt) (mhatMVExactDegreeZero (rt := rt)) k

/-- **The inputs of the final assembly other than the five fields built in this area and in
`Work.Final`**: the assembled space `M̂` (a `Work.Space.RTData` — the `rt` parameter of this
structure), the smoothness of its Levi-Civita connection, and the parametric curvature bound
`∀ K > 0, RauchK.CurvLe lcConn K`. -/
structure Remaining (rt : Work.Space.RTData) where
  /-- **LEVICIVITA.**  The connection of `M̂` is smooth — `Work.LeviCivita.lcConn_contMDiff`. -/
  [cov_smooth : CovariantDerivative.ContMDiffCovariantDerivative
    (Work.Final.mhatCov (rt := rt)) ∞]
  /-- **CURVATURE.**  The curvature bound, in the parametric form consumed by Cartan–Hadamard —
  `Work.Final.FinalInputs.curvLe_field` (from the chart models of `Work.Space.RTData`) or
  `Work.Final.ofSecNonpos`. -/
  curvLe : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe (Work.Final.mhatCov (rt := rt)) K

/-- **The complete list of remaining inputs of the challenge**, once the three fields of this area
are supplied: `L`, `eM`, `eN`, `hsq`, `hX` are all constructed here (respectively in
`Work.Final` and in this area). -/
def finalInputs (R : Remaining (rt := rt)) (I : Inputs (rt := rt)) : Work.Final.FinalInputs where
  rt := rt
  cov_smooth := R.cov_smooth
  curvLe := R.curvLe
  L := mhatLES (rt := rt)
  eM := (fields I).eM
  eN := (fields I).eN
  hsq := (fields I).hsq
  hX := mhatLES_hX (rt := rt)

/-- **The complete `Work.Final.FinalInputs` from the per-cusp inputs** — the form in which the
`rtdata` data is organised (one computation per cusp). -/
def finalInputs_of_cusps (R : Remaining (rt := rt)) (I : CuspInputs (rt := rt)) :
    Work.Final.FinalInputs :=
  finalInputs R I.toInputs

/-- **The challenge theorem, from the remaining inputs and the per-cusp data.** -/
theorem aspherical_integer_homology_four_sphere_of_cusps
    (R : Remaining (rt := rt)) (I : CuspInputs (rt := rt)) :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere :=
  Work.Final.aspherical_integer_homology_four_sphere (D := finalInputs_of_cusps R I)

/-- The `L` field of `finalInputs` is the sequence of this area (definitional). -/
theorem finalInputs_mhatLES (R : Remaining (rt := rt)) (I : Inputs (rt := rt)) :
    (finalInputs R I).L = mhatLES (rt := rt) := rfl

/-- The `eM` field of `finalInputs` is the one built in this area (definitional). -/
theorem finalInputs_eM (R : Remaining (rt := rt)) (I : Inputs (rt := rt)) (k : ℤ) :
    (finalInputs R I).eM k = eM I.toPieceData k := rfl

/-- The `eN` field of `finalInputs` is the one built in this area (definitional). -/
theorem finalInputs_eN (R : Remaining (rt := rt)) (I : Inputs (rt := rt)) (k : ℤ) :
    (finalInputs R I).eN k = eN I.toPieceData k := rfl

/-- The `hsq` field of `finalInputs` is the one proved in this area (definitional). -/
theorem finalInputs_hsq (R : Remaining (rt := rt)) (I : Inputs (rt := rt)) (k : ℤ) :
    (finalInputs R I).hsq k = hsq I k := rfl

/-- **The challenge theorem, from the remaining inputs and this area's data.**  This is the form
in which `Submission.lean` can be closed once `Work.HomologyIso.Inputs` is supplied: the only
inputs left are the assembled space `M̂`, the smoothness of `lcConn` and the curvature bound. -/
theorem aspherical_integer_homology_four_sphere_of_remaining
    (R : Remaining (rt := rt)) (I : Inputs (rt := rt)) :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere :=
  Work.Final.aspherical_integer_homology_four_sphere (D := finalInputs R I)

end

end Work.HomologyIso
