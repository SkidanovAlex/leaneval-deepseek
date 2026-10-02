import Mathlib
import Submission.Work.Gen.Cp2Cp2TangentSplits
import Submission.Work.Gen.CP4Smooth8
import Submission.Work.Gen.EulerChernCP4
import Submission.Work.Thom.Cohomology

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
# AREA GEN — the *defined* tangent classes of `ℂP² × ℂP²`

This is the last GEN-owned residue of `Work.Gen.cp2cp2_model`: the identification of the **defined**
classes `Work.Thom.p1Tangent'`, `Work.Thom.p2Tangent'` of `ℂP² × ℂP²` with the classical
expressions

  `p₁(T(ℂP²×ℂP²)) = 3·(π₁^*u² + π₂^*u²)`,   `p₂(T(ℂP²×ℂP²)) = 9·(π₁^*u² ⌣ π₂^*u²)`,

where `u² = Work.Gen.uSq 2 = c₁(O(1))²` is the hyperplane-square of `ℂP²`.  These are exactly the
Künneth model's `p₁ = 3(a² + b²)`, `p₂ = 9·a²b²` written without naming the model's classes
(`a = π₁^*h`, `b = π₂^*h`).

The proof consumes

* the product splitting `Work.Gen.Cp2Cp2TangentSplits` (delegated), transported through
  `Work.Thom.chernClass_BundleIso` to the complexified tangent bundles,
* the Whitney sum formula in degrees `2` and `4` (`Work.Gen.WhitneyFormula`; this is the `D1`-
  dependent input of the area, see `README.md` SESSION 7),
* the classical Chern classes of `TℂP²` (`c₂(ℂ⊗TℝℂP²) = -3u²`, `c₄(ℂ⊗TℝℂP²) = 0`), from the
  Euler sequence of `ℂP²` (`Submission/Work/Gen/eulerSequence_iso_two.lean`),
* naturality of the Chern classes under pullback (`Work.Thom.chernClass_comap`).
-/

open scoped Manifold ContDiff Topology

namespace Work.Gen

noncomputable section

open Work.Projective

attribute [local instance] cp2cp2ChartedSpaceEuclid
attribute [local instance] cp2cp2IsManifoldEuclid
attribute [local instance] cp2ChartedSpace
attribute [local instance] cp2IsManifold

/-- The first projection `ℂP² × ℂP² → ℂP²`. -/
abbrev projFirst : ContinuousMap (CP 2 × CP 2) (CP 2) := ContinuousMap.fst

/-- The second projection `ℂP² × ℂP² → ℂP²`. -/
abbrev projSecond : ContinuousMap (CP 2 × CP 2) (CP 2) := ContinuousMap.snd

/-- **The defined tangent classes of `ℂP² × ℂP²` are the classical ones**: the `p₁`, `p₂` of
`Work.Thom.p1Tangent'`/`p2Tangent'` (the classes of `T ⊗_ℝ ℂ` over the explicit `ℝ⁸`-atlas of
`Work.Gen.cp2cp2ChartedSpaceEuclid`) are `3·(π₁^*u² + π₂^*u²)` and `9·(π₁^*u² ⌣ π₂^*u²)`.

This is the `h1`, `h2` half of `Work.Gen.cp2cp2_model` (the Künneth model's `p₁`, `p₂` are these
expressions with `πᵢ^*u² = a², b²`). -/
def Cp2Cp2TangentClasses : Prop :=
  letI : CompactSpace (CP 2) := compactSpace_CP 2
  letI : CompactSpace (CP 2 × CP 2) := inferInstance
  Work.Thom.p1Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 2 × CP 2)
      = (3 : ℤ) • ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2)
          + (Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))
    ∧ Work.Thom.p2Tangent' 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 2 × CP 2)
      = (9 : ℤ) • Work.Cohomology.cupH'
          ℤ (TopCat.toSSet.obj (TopCat.of (CP 2 × CP 2))) 4 4
          ((Work.Thom.CohMap projFirst ℤ 4).hom (uSq 2))
          ((Work.Thom.CohMap projSecond ℤ 4).hom (uSq 2))

end

end Work.Gen
