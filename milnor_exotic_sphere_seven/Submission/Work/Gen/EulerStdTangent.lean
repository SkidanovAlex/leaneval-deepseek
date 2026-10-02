import Mathlib
import Submission.Work.Gen.Euler
import Submission.Work.Gen.EulerSplit

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

/-!
# The tangent bundle of `ℂP⁴` over the standard Euclidean chart cover

`Work.Gen.stdTangentC 4` is the complexification of `Work.Gen.stdTangentReal`, the tangent bundle of
`ℂP⁴` reindexed along the standard `Fin 5` chart cover (`euclidChart 4 i`).  This module names
`stdTangentReal` and records the `rfl`-identifications of `stdTangentC 4` with its complexification.
-/

open scoped Manifold ContDiff

namespace Work.Gen

open Work.Projective Work.TangentClasses

noncomputable section

/-- The (real) tangent bundle of `ℂP⁴` over the standard Euclidean chart cover. -/
def stdTangentReal : RealBundle (CP 4) (EuclideanSpace ℝ (Fin 8)) (Fin 5) :=
  (tangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 4)).reindex (stdChart 4) (stdChart_covers 4)

theorem stdTangentC_eq :
    stdTangentC 4 = Work.Thom.complexificationCore (stdTangentReal) := rfl

theorem stdTangentReal_baseSet (p : Fin 5) : stdTangentReal.baseSet p = chartSet p := by
  show (Work.TangentClasses.tangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 4)).baseSet
    (stdChart 4 p) = chartSet p
  rw [Work.TangentClasses.tangentBundle_baseSet, stdChart_source]

theorem stdTangentC_baseSet (p : Fin 5) : (stdTangentC 4).baseSet p = chartSet p := by
  rw [stdTangentC_eq]
  exact stdTangentReal_baseSet p

theorem stdTangentReal_coordChange (p q : Fin 5) (b : CP 4) :
    stdTangentReal.coordChange p q b
      = (tangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 8)) (CP 4)).coordChange
          (stdChart 4 p) (stdChart 4 q) b := rfl

end

end Work.Gen
