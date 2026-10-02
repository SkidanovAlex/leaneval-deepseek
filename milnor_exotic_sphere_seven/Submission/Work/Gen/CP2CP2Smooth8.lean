import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Gen.Cp2Cp2Smooth
import Submission.Work.Gen.Cp2Cp2AtlasExplicit
import Submission.Work.Projective.Model
import Submission.Work.Projective.t2Space_CP

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# AREA GEN — `ℂP² × ℂP²` as a `Work.Drive.Smooth8`

The drive's second generator is `G₂ = ℂP² × ℂP²`.  This module installs

* the `ChartedSpace (EuclideanSpace ℝ (Fin 8))` structure on `ℂP² × ℂP²` (from
  `Work.Gen.Cp2Cp2Smooth`, which re-charts the product of the two Euclidean atlases over `ℝ⁸`
  along `Work.Model.prod_transfer`),
* the matching `IsManifold (𝓡 8) ∞` structure,
* and turns them, together with `CompactSpace`/`T2Space`/`ConnectedSpace` for the product and a
  **generating fundamental class** supplied by the caller, into a `Work.Drive.Smooth8`.

The fundamental class itself is proved to exist separately
(`Work.Gen.Cp2Cp2FundamentalClass`); keeping it as an argument means this module is independent of
that computation, and it is what the final assembly of `Work.Gen.generators8` consumes.
-/

open scoped Manifold ContDiff

namespace Work.Gen

open Work.Projective

noncomputable section

/-- The `ChartedSpace (EuclideanSpace ℝ (Fin 8))` structure on `ℂP² × ℂP²`: the pushforward of
the product atlas along the linear isometry `ℝ⁴ × ℝ⁴ ≅ ℝ⁸`.

**This is a *definition*, not a `Classical.choose`.**  Its previous definition was
`Classical.choose Cp2Cp2Smooth`, an *opaque* witness of the `∃`-statement
`Work.Model.prod_transfer`; since `Classical.choice` has no computation rule, the charts (and hence
the tangent bundle, and hence `Work.Thom.p1Tangent'`/`p2Tangent'`) of `ℂP² × ℂP²` were then
uncomputable, which blocks `Work.Gen.cp2cp2_model`.  `Work.Gen.cp2cp2ChartedSpaceExplicit` is the
*explicit* structure (the same atlas, exhibited rather than chosen), and is definitionally the one
the `IsManifold` proof below refers to. -/
noncomputable def cp2cp2ChartedSpaceEuclid :
    ChartedSpace (EuclideanSpace ℝ (Fin 8)) (CP 2 × CP 2) :=
  cp2cp2ChartedSpaceExplicit

attribute [instance] cp2cp2ChartedSpaceEuclid

/-- The `C^∞` structure on `ℂP² × ℂP²`, over the model `EuclideanSpace ℝ (Fin 8)`: the explicit
`C^∞` structure of `Work.Gen.cp2cp2ChartedSpaceExplicit`. -/
theorem cp2cp2IsManifoldEuclid : IsManifold (𝓡 8) ∞ (CP 2 × CP 2) :=
  cp2cp2IsManifoldExplicit

attribute [instance] cp2cp2IsManifoldEuclid

/-- **`ℂP² × ℂP²` as a closed connected oriented `C^∞` `8`-manifold**, from a chosen generating
fundamental class.  All the manifold structure comes from
`Work.Gen.Cp2Cp2Smooth` / `Work.Projective`; only the fundamental class is an argument. -/
noncomputable def cp2cp2Smooth8Of
    (c : (Work.Cohomology.chainC ℤ
      (TopCat.toSSet.obj (TopCat.of (CP 2 × CP 2)))).homology 8)
    (hc : Submodule.span ℤ {c} = ⊤) : Work.Drive.Smooth8 :=
  letI : CompactSpace (CP 2) := compactSpace_CP 2
  letI : T2Space (CP 2) := t2Space_CP 2
  letI : ConnectedSpace (CP 2) := connectedSpace_CP 2
  {
  pt := CP 2 × CP 2
  chartedSpace := cp2cp2ChartedSpaceEuclid
  isManifold := cp2cp2IsManifoldEuclid
  compactSpace := inferInstance
  t2Space := inferInstance
  connectedSpace := inferInstance
  c := c
  c_generates := hc }

theorem cp2cp2Smooth8Of_pt
    (c : (Work.Cohomology.chainC ℤ
      (TopCat.toSSet.obj (TopCat.of (CP 2 × CP 2)))).homology 8)
    (hc : Submodule.span ℤ {c} = ⊤) :
    (cp2cp2Smooth8Of c hc).pt = (CP 2 × CP 2) := rfl

end

end Work.Gen
