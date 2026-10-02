import Mathlib
import Submission.Work.Gen.Cp2Cp2TangentSplits
import Submission.Work.Gen.Cp2Cp2AtlasExplicit
import Submission.Work.Gen.CP2CP2Smooth8

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
# The pushed-forward `ℝ⁸`-atlas of `ℂP² × ℂP²`: vocabulary for the product splitting

The tangent bundle of `ℂP² × ℂP²` in the presentation of `Work.Gen.cp2cp2TangentC` is
`Work.TangentClasses.tangentBundle 𝓘(ℝ,ℝ⁸)` over the atlas of `Work.Gen.cp2cp2ChartedSpaceEuclid`,
which is the **pushforward** of the product atlas of `ℂP² × ℂP²` along the linear isometry
`Φ = Work.Gen.prodLinEquiv 4 4 : ℝ⁴ × ℝ⁴ ≅ ℝ⁸`.

This module fixes the vocabulary relating the two presentations:

* `Work.Gen.PhiH` — `Φ` as a partial homeomorphism;
* `Work.Gen.pushChart`, `Work.Gen.pushAtlas` — the pushforward of a chart resp. of an atlas
  element;
* `Work.Gen.pushIdx` — the pushforward of a **pair** of charts of `ℂP²` (the index of the
  direct-sum presentation);
* `Work.Gen.achart_pushAtlas_chartAt` — the chart of the `ℝ⁸`-structure at a point `b` is the
  pushforward of the product chart at `b`.
-/

open scoped Manifold ContDiff Topology

namespace Work.Gen

open Work.Projective

noncomputable section

/-- The Euclidean model of `ℂP²`. -/
abbrev H4 : Type := EuclideanSpace ℝ (Fin 4)

/-- The Euclidean model of `ℂP² × ℂP²`. -/
abbrev H8 : Type := EuclideanSpace ℝ (Fin 8)

/-- `ℂP² × ℂP²`. -/
abbrev P2 : Type := CP 2 × CP 2

/-- The linear isometry `ℝ⁴ × ℝ⁴ ≅ ℝ⁸` of `Work.Gen.prodLinEquiv 4 4`, as a partial
homeomorphism. -/
def PhiH : OpenPartialHomeomorph (ModelProd H4 H4) H8 :=
  (prodLinEquiv 4 4).toHomeomorph.toOpenPartialHomeomorph

/-- The pushforward of a chart of `ℂP² × ℂP²` along `Φ`. -/
def pushChart (A : OpenPartialHomeomorph P2 (ModelProd H4 H4)) : OpenPartialHomeomorph P2 H8 :=
  A.trans PhiH

/-- The element of the pushed-forward `ℝ⁸`-atlas of the pushforward of a chart. -/
def pushAtlas (A : OpenPartialHomeomorph P2 (ModelProd H4 H4))
    (hA : A ∈ atlas (ModelProd H4 H4) P2) : atlas H8 P2 :=
  ⟨pushChart A, ⟨A, hA, rfl⟩⟩

/-- The `ℝ⁸`-atlas index of a **pair** of charts of `ℂP²`: the pushforward of their product. -/
def pushIdx (t : atlas H4 (CP 2) × atlas H4 (CP 2)) : atlas H8 P2 :=
  pushAtlas (t.1.1.prod t.2.1) (Set.mem_image2_of_mem t.1.2 t.2.2)

/-- The chart of the `ℝ⁸`-structure at a point `b` is the pushforward of the product chart at
`b`. -/
theorem achart_pushAtlas_chartAt (b : P2) :
    pushAtlas (chartAt (ModelProd H4 H4) b) (chart_mem_atlas (ModelProd H4 H4) b)
      = achart H8 b :=
  rfl

end

end Work.Gen
