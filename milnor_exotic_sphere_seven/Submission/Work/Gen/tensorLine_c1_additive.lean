import Mathlib
import Submission.Work.Gen.LineTensor
import Submission.Work.Gen.PathCompDefs
import Submission.Work.Gen.Coh_eq_zero_of_pathComponents
import Submission.Work.Thom.chernClass
import Submission.Work.Thom.chernClass_comap
import Submission.Work.Thom.CohMap_oneH
import Submission.Work.Gen.chernClass_one_whitneySum_eq_tensorLine
import Submission.Work.LineBundles.Basic
import Submission.Work.LineBundles.Divis
import Submission.Work.LineBundles.Connected
import Submission.Work.Whitney.Cup
import Submission.Work.Cohomology.exists_smul_oneH
import Submission.Work.Cohomology.CupRing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology Simplicial
open scoped Simplicial

namespace Work.Gen

/-- **Each path component is path connected.**  Two points with the same `π₀`-class of the singular
simplicial set are joined by a path: the `π₀`-classes are the fibres of
`TopCat.zerothHomotopyEquiv : ZerothHomotopy X ≃ (toSSet.obj X).π₀`, and `ZerothHomotopy` is the
quotient of the `Joined` relation. -/
theorem pathConnectedSpace_pathComp (X : Type) [TopologicalSpace X]
    (c : SSet.π₀ (TopCat.toSSet.obj (TopCat.of X))) :
    PathConnectedSpace (pathComp X c) := by
  -- a point of `X` whose `π₀`-class is `c`
  obtain ⟨z₀, hz₀⟩ := ZerothHomotopy.mk_surjective (X := X)
    ((TopCat.zerothHomotopyEquiv (X := TopCat.of X)).symm c)
  have hz₀' : TopCat.zerothHomotopyEquiv (X := TopCat.of X) (ZerothHomotopy.mk z₀) = c := by
    rw [hz₀, Equiv.apply_symm_apply]
  have hiff : ∀ x : X, (SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := TopCat.of X)).symm x) = c)
      ↔ ZerothHomotopy.mk x = ZerothHomotopy.mk z₀ := by
    intro x
    have h1 : SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := TopCat.of X)).symm x)
        = TopCat.zerothHomotopyEquiv (X := TopCat.of X) (ZerothHomotopy.mk x) :=
      (TopCat.zerothHomotopyEquiv_mk (X := TopCat.of X) x).symm
    rw [h1, ← hz₀']
    exact (TopCat.zerothHomotopyEquiv (X := TopCat.of X)).apply_eq_iff_eq
  -- the component of `c` is the path component of `z₀`
  have hpred : (fun x : X => SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := TopCat.of X)).symm x) = c)
      = pathComponent z₀ := by
    rw [← ZerothHomotopy.preimage_singleton_eq_pathComponent (X := X) z₀]
    exact funext (fun x => propext (hiff x))
  have hIs : IsPathConnected (fun x : X => SSet.π₀.mk ((TopCat.toSSetObj₀Equiv (X := TopCat.of X)).symm x) = c) := by
    rw [hpred]
    exact isPathConnected_pathComponent
  exact isPathConnected_iff_pathConnectedSpace.mp hIs


/-- **Additivity of `c₁` on the tensor product of line bundles over a path connected base.**  This
is `Work.LineBundles.tensorLine_c1_additive_connected`. -/
theorem tensorLine_c1_additive_of_pathConnected {B : Type} [TopologicalSpace B]
    [PathConnectedSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (M : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂) :
    Work.Thom.chernClass 1 1 (Work.Gen.tensorLine L M)
      = Work.Thom.chernClass 1 1 L + Work.Thom.chernClass 1 1 M :=
  Work.LineBundles.tensorLine_c1_additive_connected Work.LineBundles.divisibility L M

end Work.Gen

namespace Work.Gen

open CategoryTheory AlgebraicTopology Simplicial
open scoped Simplicial

/-- The first Chern class of `L`, as an abbreviation. -/
local notation "c₁" => Work.Thom.chernClass 1 1

/-- **The tensor product of line bundles is additive in `c₁`, over an arbitrary topological base.**
The identity is checked after pulling back along the inclusion of each path component, where it is
the path connected case `Work.Gen.tensorLine_c1_additive_of_pathConnected`; the pullbacks jointly
detect zero by `Work.Gen.Coh_eq_zero_of_pathComponents`. -/
theorem tensorLine_c1_additive {B : Type} [TopologicalSpace B] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (L : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₁)
    (M : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι₂) :
    Work.Thom.chernClass 1 1 (Work.Gen.tensorLine L M)
      = Work.Thom.chernClass 1 1 L + Work.Thom.chernClass 1 1 M := by
  apply sub_eq_zero.mp
  refine Work.Gen.Coh_eq_zero_of_pathComponents _ (fun c => ?_)
  haveI : PathConnectedSpace (Work.Gen.pathComp B c) := Work.Gen.pathConnectedSpace_pathComp B c
  have hcomp := tensorLine_c1_additive_of_pathConnected
    (Work.Thom.bundleComap L (Work.Gen.pathCompIncl B c))
    (Work.Thom.bundleComap M (Work.Gen.pathCompIncl B c))
  rw [map_sub, map_add,
    ← Work.Thom.chernClass_comap (m := 1) (j := 1) L (Work.Gen.pathCompIncl B c),
    ← Work.Thom.chernClass_comap (m := 1) (j := 1) M (Work.Gen.pathCompIncl B c),
    ← Work.Thom.chernClass_comap (m := 1) (j := 1)
      (Work.Gen.tensorLine L M) (Work.Gen.pathCompIncl B c),
    Work.Gen.tensorLine_bundleComap]
  rw [sub_eq_zero]
  exact hcomp

end Work.Gen
