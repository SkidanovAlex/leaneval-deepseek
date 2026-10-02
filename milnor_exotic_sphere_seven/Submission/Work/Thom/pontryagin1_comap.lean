import Mathlib
import Submission.Work.Thom.manifoldP1
import Submission.Work.Thom.chernClass_comap
import Submission.Work.Thom.complexPullback

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom

/-- **Naturality of the first Pontryagin class.**  For a real vector bundle `Z` over a finite cover
and a continuous map `f`, the first Pontryagin class of the pullback is the pullback of the first
Pontryagin class:
`p₁(f^*Z) = f^*(p₁ Z)`.

Since `p₁ = - c₂(− ⊗_ℝ ℂ)`, this is immediate from the naturality of the Chern classes
(`chernClass_comap`) together with the fact that the complexification commutes with the pullback
(`complexificationCore_bundleComap`), the pullback being additive. -/
theorem pontryagin1_comap {k : ℕ} {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {ι : Type} [Fintype ι] (Z : Work.TangentClasses.RealBundle B (EuclideanSpace ℝ (Fin k)) ι)
    (f : C(B', B)) :
    Work.Thom.pontryagin1 (Work.Thom.bundleComap Z f)
      = (Work.Thom.CohMap f ℤ 4).hom (Work.Thom.pontryagin1 Z) := by
  rw [pontryagin1_def, pontryagin1_def]
  rw [complexificationCore_bundleComap]
  rw [chernClass_comap]
  rw [map_neg]

end Work.Thom
