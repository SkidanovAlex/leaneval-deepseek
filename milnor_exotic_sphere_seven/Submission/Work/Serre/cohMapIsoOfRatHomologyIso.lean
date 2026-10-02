import Mathlib
import Submission.Work.Serre.Defs
import Submission.Work.Thom.Cohomology
import Submission.Work.Cohomology.DualComplexMap
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.Cohomology.hmv_naturality
import Submission.Work.Serre.cohRatAlg
import Submission.Work.Serre.isIso_chainScMap_of_isIso_homologyMap
import Submission.Work.Serre.isIso_homologyMap_dual_of_isIso_dualScMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A rational homology isomorphism is a rational cohomology isomorphism (in one degree)

For a continuous map `f : C(X,Y)` and a degree `k`, if the induced map
`H_k(X;ℚ) → H_k(Y;ℚ)` is an isomorphism, then so is the induced map
`H^k(Y;ℚ) → H^k(X;ℚ)`.

Over a field the universal coefficient theorem identifies `H^k` with the dual of `H_k`, so this is
the statement that the dual of an isomorphism of vector spaces is an isomorphism — the content being
the *naturality* of the universal coefficient isomorphism, which is what the auxiliary module
`Submission.Work.Serre.cohRatAlg` provides.
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

theorem cohMapIsoOfRatHomologyIso {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (k : ℕ) (h : CategoryTheory.IsIso (Work.Serre.ratHomologyMap f k)) :
    CategoryTheory.IsIso (Work.Thom.CohMap f ℚ k) := by
  have hA := Work.Serre.isIso_chainScMap_of_isIso_homologyMap
    (C := Work.Cohomology.singularChains ℚ (TopCat.of X))
    (D := Work.Cohomology.singularChains ℚ (TopCat.of Y))
    (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) k h
  haveI : CategoryTheory.IsIso (Work.Serre.fdZMap
      (Work.Cohomology.singularChains ℚ (TopCat.of X))
      (Work.Cohomology.singularChains ℚ (TopCat.of Y))
      (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) k) := hA
  have hG := Work.Serre.isIso_dualHMap_of_isIso_fdZMap
    (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) k inferInstance
  exact Work.Serre.isIso_homologyMap_dual_of_isIso_dualScMap
    (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) k hG

end Work.Serre
