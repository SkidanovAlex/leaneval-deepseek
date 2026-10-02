import Mathlib
import Submission.Work.Gen.CP2CP2Smooth8
import Submission.Work.Gen.Cp2Cp2Smooth
import Submission.Work.TangentClasses.tangentBundle_prod_coordChange
import Submission.Work.Thom.complexification
import Submission.Work.Whitney.Basic

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
# AREA GEN — the product tangent bundle of `ℂP² × ℂP²`

`Work.Gen.cp2cp2_model` must identify the *defined* classes `Work.Thom.p1Tangent'`,
`Work.Thom.p2Tangent'` of `ℂP² × ℂP²` with the Künneth model's `p₁ = 3(a² + b²)`,
`p₂ = 9a²b²`.  The characteristic-class side of that goes through the standard splitting

  `T(ℂP² × ℂP²) ≅ π₁^*(TℂP²) ⊕ π₂^*(TℂP²)`,

whose transition-function form is `Work.TangentClasses.tangentBundle_prod_coordChange` (the
transition functions of `T(M × N)` are the block-diagonal combinations of those of `TM`, `TN`).
That lemma is stated for the *product* charted-space structure; the deliverable uses the
re-charted structure of `Work.Gen.Cp2Cp2ChartedSpaceExplicit` (`Work.Gen.Cp2Cp2AtlasExplicit`,
the atlas pushed forward along the linear isometry `ℝ⁴ × ℝ⁴ ≅ ℝ⁸`).  The two structures differ
by the *constant* gauge `Φ`, which is exactly the comparison that has to be made.

This file states the **GEN-owned** target as a `Prop`.
-/

open scoped Manifold ContDiff Topology

namespace Work.Gen

noncomputable section

open Work.Projective

attribute [local instance] cp2cp2ChartedSpaceEuclid
attribute [local instance] cp2cp2IsManifoldEuclid
attribute [local instance] cp2ChartedSpace
attribute [local instance] cp2IsManifold

/-- The `C^1` (in fact `C^∞`) structure on `ℂP² × ℂP²`, in the form `tangentBundle` consumes. -/
instance cp2cp2IsManifoldOne : IsManifold (𝓡 8) 1 (CP 2 × CP 2) :=
  IsManifold.of_le (n := ∞) (by simp)

/-- The `C^1` (in fact `C^∞`) structure on `ℂP²`, in the form `tangentBundle` consumes. -/
instance cp2IsManifoldOne : IsManifold (𝓡 4) 1 (CP 2) :=
  IsManifold.of_le (n := ∞) (by simp)

/-- The complexified tangent bundle of `ℂP² × ℂP²` over the **explicit** `ℝ⁸`-atlas of
`Work.Gen.cp2cp2ChartedSpaceEuclid` (= `Work.Gen.cp2cp2ChartedSpaceExplicit`). -/
noncomputable abbrev cp2cp2TangentC :
    VectorBundleCore ℂ (CP 2 × CP 2) (EuclideanSpace ℂ (Fin 8))
      (atlas (EuclideanSpace ℝ (Fin 8)) (CP 2 × CP 2)) :=
  Work.Thom.complexificationCore
    (Work.TangentClasses.tangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 2 × CP 2))

/-- The complexified tangent bundle of `ℂP²` (over its Euclidean charts), pulled back along a
continuous map `f : ℂP² × ℂP² → ℂP²`. -/
noncomputable abbrev factorTangentC (f : ContinuousMap (CP 2 × CP 2) (CP 2)) :
    VectorBundleCore ℂ (CP 2 × CP 2) (EuclideanSpace ℂ (Fin 4))
      (atlas (EuclideanSpace ℝ (Fin 4)) (CP 2)) :=
  Work.Thom.complexificationCore
    (Work.Thom.bundleComap
      (Work.TangentClasses.tangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) (CP 2)) f)

/-- **The product splitting of the complexified tangent bundle of `ℂP² × ℂP²`**, in the exact
presentation used by the deliverable: the complexified tangent bundle of `ℂP² × ℂP²` over the
explicit `ℝ⁸`-atlas is isomorphic to the direct sum of the pullbacks of the complexified tangent
bundles of the two factors.

Consumption (with the Whitney sum formula and the classical Chern classes of `TℂP²`):
`p₁(T(ℂP²×ℂP²)) = 3(a² + b²)` and `p₂(T(ℂP²×ℂP²)) = 9a²b²`, i.e. the `h1`, `h2` inputs of
`Work.Gen.cp2cp2_model`. -/
def Cp2Cp2TangentSplits : Prop :=
  Nonempty (Work.Thom.BundleIso cp2cp2TangentC
    (Work.Whitney.whitneySum
      (factorTangentC ContinuousMap.fst)
      (factorTangentC ContinuousMap.snd)))

end

end Work.Gen
